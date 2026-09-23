import AutomaticContinuity.SchwarzDerivativeBounds
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Topology.Homeomorph.Defs

set_option autoImplicit false

/-!
# Finite compositions with a uniform quadratic Euler error

The hypotheses concern the individual factors and vector fields on a fixed
tube. Intermediate points stay in that tube by an explicit displacement
bound. The composition estimate is proved from these hypotheses; it is not
an assumed flow or ODE theorem.
-/

noncomputable section

namespace AutomaticContinuity.FiniteFlowComposition

open Set
open scoped BigOperators

universe u v
variable {𝕜 : Type u} [NormedField 𝕜]
variable {E : Type v}

/-- Apply factors in increasing index order. -/
def applyFactors (f : ℕ → E → E) : ℕ → E → E
  | 0, x => x
  | n + 1, x => f n (applyFactors f n x)

@[simp] theorem applyFactors_zero (f : ℕ → E → E) (x : E) :
    applyFactors f 0 x = x := rfl

@[simp] theorem applyFactors_succ (f : ℕ → E → E) (n : ℕ) (x : E) :
    applyFactors f (n + 1) x = f n (applyFactors f n x) := rfl

variable [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- A factor remainder and a field bound imply a linear displacement bound. -/
theorem factor_displacement_le {f V : E → E} {τ : 𝕜} {A B : ℝ}
    (hA : 0 ≤ A) (hτ : ‖τ‖ ≤ 1) {x : E}
    (hV : ‖V x‖ ≤ B) (hf : ‖f x - x - τ • V x‖ ≤ A * ‖τ‖ ^ 2) :
    ‖f x - x‖ ≤ ‖τ‖ * (B + A) := by
  have ht : ‖τ‖ ^ 2 ≤ ‖τ‖ := by nlinarith [norm_nonneg τ]
  calc
    ‖f x - x‖ = ‖(f x - x - τ • V x) + τ • V x‖ := by rw [sub_add_cancel]
    _ ≤ ‖f x - x - τ • V x‖ + ‖τ • V x‖ := norm_add_le _ _
    _ ≤ A * ‖τ‖ ^ 2 + ‖τ‖ * B := by rw [norm_smul]; gcongr
    _ ≤ ‖τ‖ * (B + A) := by nlinarith

/-- Every prefix remains in the specified tube. The final bound uses only
the number of factors, their field bounds, and their individual remainders. -/
theorem displacement_le
    (f V : ℕ → E → E) (N : ℕ) {S T : Set E} {τ : 𝕜} {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (_hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hf : ∀ i < N, ∀ y ∈ T,
      ‖f i y - y - τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) :
    ∀ n ≤ N, ‖applyFactors f n x - x‖ ≤ (n : ℝ) * ‖τ‖ * (B + A) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    have hprev := ih (Nat.le_of_lt hnN)
    have hyn : applyFactors f n x ∈ T := by
      apply htube x hx
      calc
        _ ≤ (n : ℝ) * ‖τ‖ * (B + A) := hprev
        _ ≤ (N : ℝ) * ‖τ‖ * (B + A) := by gcongr
        _ ≤ δ := hsize
    have hstep := factor_displacement_le hA hτ (hV n hnN _ hyn) (hf n hnN _ hyn)
    calc
      ‖applyFactors f (n + 1) x - x‖ =
          ‖(f n (applyFactors f n x) - applyFactors f n x) +
            (applyFactors f n x - x)‖ := by simp only [applyFactors_succ]; congr 1; abel
      _ ≤ ‖f n (applyFactors f n x) - applyFactors f n x‖ +
          ‖applyFactors f n x - x‖ := norm_add_le _ _
      _ ≤ ‖τ‖ * (B + A) + (n : ℝ) * ‖τ‖ * (B + A) := add_le_add hstep hprev
      _ = ((n + 1 : ℕ) : ℝ) * ‖τ‖ * (B + A) := by push_cast; ring

theorem applyFactors_mem
    (f V : ℕ → E → E) (N : ℕ) {S T : Set E} {τ : 𝕜} {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hf : ∀ i < N, ∀ y ∈ T,
      ‖f i y - y - τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) {n : ℕ} (hn : n ≤ N) :
    applyFactors f n x ∈ T := by
  apply htube x hx
  have hd := displacement_le f V N hA hB hδ hτ hsize htube hV hf hx n hn
  calc
    _ ≤ (n : ℝ) * ‖τ‖ * (B + A) := hd
    _ ≤ (N : ℝ) * ‖τ‖ * (B + A) := by gcongr
    _ ≤ δ := hsize

/-- Finite flow splitting has an explicit quadratic remainder. No property
of a complete flow is assumed beyond the displayed estimates for each factor. -/
theorem euler_error_le
    (f V : ℕ → E → E) (N : ℕ) {S T : Set E} {τ : 𝕜} {A B L δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hLip : ∀ i < N, ∀ y ∈ T, ∀ z ∈ T, ‖V i y - V i z‖ ≤ L * ‖y - z‖)
    (hf : ∀ i < N, ∀ y ∈ T,
      ‖f i y - y - τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) :
    ∀ n ≤ N,
      ‖applyFactors f n x - x - τ • ∑ i ∈ Finset.range n, V i x‖ ≤
        ((n : ℝ) * A + (n : ℝ) ^ 2 * L * (B + A)) * ‖τ‖ ^ 2 := by
  have hxT : x ∈ T := htube x hx x (by simpa using hδ)
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnN : n < N := by omega
    have hnle := Nat.le_of_lt hnN
    have hyn := applyFactors_mem f V N hA hB hδ hτ hsize htube hV hf hx hnle
    have hdisp := displacement_le f V N hA hB hδ hτ hsize htube hV hf hx n hnle
    have hprev := ih hnle
    have herr := hf n hnN _ hyn
    have hlip := hLip n hnN _ hyn x hxT
    have hdiff : ‖τ • (V n (applyFactors f n x) - V n x)‖ ≤
        (n : ℝ) * L * (B + A) * ‖τ‖ ^ 2 := by
      rw [norm_smul]
      calc
        ‖τ‖ * ‖V n (applyFactors f n x) - V n x‖ ≤
            ‖τ‖ * (L * ((n : ℝ) * ‖τ‖ * (B + A))) :=
          mul_le_mul_of_nonneg_left (hlip.trans (mul_le_mul_of_nonneg_left hdisp hL))
            (norm_nonneg τ)
        _ = (n : ℝ) * L * (B + A) * ‖τ‖ ^ 2 := by ring
    have heq : applyFactors f (n + 1) x - x - τ • ∑ i ∈ Finset.range (n + 1), V i x =
        (f n (applyFactors f n x) - applyFactors f n x - τ • V n (applyFactors f n x)) +
        (applyFactors f n x - x - τ • ∑ i ∈ Finset.range n, V i x) +
        τ • (V n (applyFactors f n x) - V n x) := by
      rw [applyFactors_succ, Finset.sum_range_succ, smul_add, smul_sub]
      abel
    rw [heq]
    calc
      _ ≤ ‖f n (applyFactors f n x) - applyFactors f n x - τ • V n (applyFactors f n x)‖ +
          ‖applyFactors f n x - x - τ • ∑ i ∈ Finset.range n, V i x‖ +
          ‖τ • (V n (applyFactors f n x) - V n x)‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ A * ‖τ‖ ^ 2 + ((n : ℝ) * A + (n : ℝ) ^ 2 * L * (B + A)) * ‖τ‖ ^ 2 +
          (n : ℝ) * L * (B + A) * ‖τ‖ ^ 2 := by gcongr
      _ ≤ (((n + 1 : ℕ) : ℝ) * A + ((n + 1 : ℕ) : ℝ) ^ 2 * L * (B + A)) * ‖τ‖ ^ 2 := by
        push_cast
        have hp : 0 ≤ ((n : ℝ) + 1) * L * (B + A) * ‖τ‖ ^ 2 := by positivity
        nlinarith

end AutomaticContinuity.FiniteFlowComposition

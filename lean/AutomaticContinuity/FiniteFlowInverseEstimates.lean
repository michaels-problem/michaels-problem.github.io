import AutomaticContinuity.FiniteFlowHolomorphy

set_option autoImplicit false

/-!
# Quantitative bounds for the actual inverse finite product

Reverse-order inverse factors give the inverse of the original product.
Every inverse prefix remains in the same tube, and the actual inverse has
the negative sum of generators as its first-order term, with an explicit
quadratic error.
-/

noncomputable section

namespace AutomaticContinuity.FiniteFlowComposition

open Set FiniteFlowHolomorphy
open scoped BigOperators

universe u v
variable {𝕜 : Type u} [NormedField 𝕜]
variable {E : Type v} [NormedAddCommGroup E]

/-- Every inverse prefix cancels the matching suffix of the full product. -/
theorem reverse_prefix_eq (e : ℕ → E ≃ₜ E) (N : ℕ) (x : E) :
    ∀ n ≤ N,
      applyFactors (fun i => (e (N - 1 - i)).symm) n x =
        compose e (N - n) ((compose e N).symm x) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hn
    have hnle : n ≤ N := by omega
    have hidx : N - 1 - n = N - (n + 1) := by omega
    have hpred : N - n = N - (n + 1) + 1 := by omega
    rw [applyFactors_succ, ih hnle, hidx, hpred, compose_succ_apply,
      Homeomorph.symm_apply_apply]

theorem reverseFactors_eq_compose_symm (e : ℕ → E ≃ₜ E) (N : ℕ) (x : E) :
    applyFactors (fun i => (e (N - 1 - i)).symm) N x = (compose e N).symm x := by
  simpa using reverse_prefix_eq e N x N le_rfl

variable [NormedSpace 𝕜 E]

theorem inverse_prefix_mem
    (e : ℕ → E ≃ₜ E) (V : ℕ → E → E) (N : ℕ)
    {S T : Set E} {τ : 𝕜} {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hei : ∀ i < N, ∀ y ∈ T,
      ‖(e i).symm y - y + τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) {n : ℕ} (hn : n ≤ N) :
    applyFactors (fun i => (e (N - 1 - i)).symm) n x ∈ T := by
  apply applyFactors_mem (fun i => (e (N - 1 - i)).symm)
    (fun i y => -V (N - 1 - i) y) N hA hB hδ hτ hsize htube _ _ hx hn
  · intro i hi y hy
    simpa only [norm_neg] using hV (N - 1 - i) (by omega) y hy
  · intro i hi y hy
    simpa only [smul_neg, sub_neg_eq_add] using hei (N - 1 - i) (by omega) y hy

theorem inverse_displacement_le
    (e : ℕ → E ≃ₜ E) (V : ℕ → E → E) (N : ℕ)
    {S T : Set E} {τ : 𝕜} {A B δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hei : ∀ i < N, ∀ y ∈ T,
      ‖(e i).symm y - y + τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) :
    ‖(compose e N).symm x - x‖ ≤ (N : ℝ) * ‖τ‖ * (B + A) := by
  rw [← reverseFactors_eq_compose_symm e N x]
  apply displacement_le (fun i => (e (N - 1 - i)).symm)
    (fun i y => -V (N - 1 - i) y) N hA hB hδ hτ hsize htube _ _ hx N le_rfl
  · intro i hi y hy
    simpa only [norm_neg] using hV (N - 1 - i) (by omega) y hy
  · intro i hi y hy
    simpa only [smul_neg, sub_neg_eq_add] using hei (N - 1 - i) (by omega) y hy

/-- The inverse in this estimate is the actual inverse homeomorphism of the
finite product, with every intermediate point justified by the tube bounds. -/
theorem inverse_euler_error_le
    (e : ℕ → E ≃ₜ E) (V : ℕ → E → E) (N : ℕ)
    {S T : Set E} {τ : 𝕜} {A B L δ : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hL : 0 ≤ L) (hδ : 0 ≤ δ) (hτ : ‖τ‖ ≤ 1)
    (hsize : (N : ℝ) * ‖τ‖ * (B + A) ≤ δ)
    (htube : ∀ x ∈ S, ∀ y, ‖y - x‖ ≤ δ → y ∈ T)
    (hV : ∀ i < N, ∀ y ∈ T, ‖V i y‖ ≤ B)
    (hLip : ∀ i < N, ∀ y ∈ T, ∀ z ∈ T, ‖V i y - V i z‖ ≤ L * ‖y - z‖)
    (hei : ∀ i < N, ∀ y ∈ T,
      ‖(e i).symm y - y + τ • V i y‖ ≤ A * ‖τ‖ ^ 2)
    {x : E} (hx : x ∈ S) :
    ‖(compose e N).symm x - x + τ • ∑ i ∈ Finset.range N, V i x‖ ≤
      ((N : ℝ) * A + (N : ℝ) ^ 2 * L * (B + A)) * ‖τ‖ ^ 2 := by
  have hVr : ∀ i < N, ∀ y ∈ T, ‖-V (N - 1 - i) y‖ ≤ B := by
    intro i hi y hy
    simpa only [norm_neg] using hV (N - 1 - i) (by omega) y hy
  have hLr : ∀ i < N, ∀ y ∈ T, ∀ z ∈ T,
      ‖-V (N - 1 - i) y - -V (N - 1 - i) z‖ ≤ L * ‖y - z‖ := by
    intro i hi y hy z hz
    simpa only [neg_sub_neg, norm_sub_rev] using hLip (N - 1 - i) (by omega) y hy z hz
  have her : ∀ i < N, ∀ y ∈ T,
      ‖(e (N - 1 - i)).symm y - y - τ • (-V (N - 1 - i) y)‖ ≤ A * ‖τ‖ ^ 2 := by
    intro i hi y hy
    simpa only [smul_neg, sub_neg_eq_add] using hei (N - 1 - i) (by omega) y hy
  have hh := euler_error_le (fun i => (e (N - 1 - i)).symm)
    (fun i y => -V (N - 1 - i) y) N hA hB hL hδ hτ hsize htube hVr hLr her hx N le_rfl
  rw [reverseFactors_eq_compose_symm, Finset.sum_neg_distrib,
    Finset.sum_range_reflect (fun i => V i x) N,
    smul_neg, sub_neg_eq_add] at hh
  exact hh

end AutomaticContinuity.FiniteFlowComposition

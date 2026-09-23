import AutomaticContinuity.ParameterFibreComposition
import AutomaticContinuity.EuclideanBallGeometry
import Mathlib.Algebra.BigOperators.Intervals

set_option autoImplicit false

/-!
# Actual inverse tails stay inside protected balls

The points are `F_i(F_n⁻¹ y)` for the actual cumulative fibre automorphisms.
Backward induction controls every intermediate point before applying the next
inverse displacement estimate. No invariance or convergence is assumed.
-/

noncomputable section

namespace AutomaticContinuity.NonautonomousInverseTails

open Set Filter ParameterFibreComposition
open scoped BigOperators Topology

abbrev Pair := ℂ × ℂ

variable {P : Type*}

/-- Cancellation identifies the next backward point with the actual inverse
of the next factor. -/
theorem inverse_tail_step (e : ℕ → P → Pair ≃ₜ Pair) (p : P) (i n : ℕ) (y : Pair) :
    product e i p ((product e n p).symm y) =
      (e i p).symm (product e (i + 1) p ((product e n p).symm y)) := by
  change _ = (e i p).symm (e i p (product e i p ((product e n p).symm y)))
  rw [Homeomorph.symm_apply_apply]

theorem sum_tail_le (ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i) {j k n : ℕ} (hjk : j ≤ k) :
    ∑ i ∈ Finset.Ico k n, ε i ≤ ∑ i ∈ Finset.Ico j n, ε i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro i hi
    exact Finset.mem_Ico.mpr ⟨hjk.trans (Finset.mem_Ico.mp hi).1, (Finset.mem_Ico.mp hi).2⟩
  · intro i _ _
    exact hε i

/-- Every intermediate point of an actual reversed inverse tail lies in the
same protected ball, with its precise finite error tail. -/
theorem inverse_tail_prefix_bound (e : ℕ → P → Pair ≃ₜ Pair) (p : P)
    (a ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i) (j n : ℕ) (_hjn : j ≤ n)
    (y : Pair) {R S : ℝ} (hy : euclideanPairNorm y ≤ R)
    (hsum : R + ∑ i ∈ Finset.Ico j n, ε i ≤ S)
    (hprotected : ∀ i, j ≤ i → i < n → S ≤ a i)
    (hstep : ∀ i, j ≤ i → i < n → ∀ w, euclideanPairNorm w ≤ a i →
      euclideanPairNorm ((e i p).symm w - w) ≤ ε i) :
    ∀ k, j ≤ k → k ≤ n →
      euclideanPairNorm (product e k p ((product e n p).symm y)) ≤
          R + ∑ i ∈ Finset.Ico k n, ε i ∧
        R + ∑ i ∈ Finset.Ico k n, ε i ≤ S := by
  have hS (k : ℕ) (hjk : j ≤ k) : R + ∑ i ∈ Finset.Ico k n, ε i ≤ S :=
    (add_le_add (le_refl R) (sum_tail_le ε hε (n := n) hjk)).trans hsum
  intro k hjk hkn
  refine ⟨?_, hS k hjk⟩
  refine Nat.decreasingInduction'
    (P := fun i => euclideanPairNorm (product e i p ((product e n p).symm y)) ≤
      R + ∑ t ∈ Finset.Ico i n, ε t) (m := k) (n := n) ?_ hkn ?_
  · intro i hin hki hi
    have hji : j ≤ i := hjk.trans hki
    have hcurrent : euclideanPairNorm (product e (i + 1) p ((product e n p).symm y)) ≤ a i :=
      (hi.trans (hS (i + 1) (by omega))).trans (hprotected i hji hin)
    have he := hstep i hji hin (product e (i + 1) p ((product e n p).symm y)) hcurrent
    have htri := euclideanPairNorm_add_le
      ((e i p).symm (product e (i + 1) p ((product e n p).symm y)) -
        product e (i + 1) p ((product e n p).symm y))
      (product e (i + 1) p ((product e n p).symm y))
    rw [sub_add_cancel] at htri
    rw [inverse_tail_step e p i n y, Finset.sum_eq_sum_Ico_succ_bot hin ε]
    exact htri.trans (by linarith)
  · simpa using hy

/-- The requested tail bound for `F_j ∘ F_n⁻¹`, including the terminal case
`j=n`, where the tail is empty. -/
theorem inverse_tail_bound (e : ℕ → P → Pair ≃ₜ Pair) (p : P)
    (a ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i) (j n : ℕ) (hjn : j ≤ n)
    (y : Pair) {R S : ℝ} (hy : euclideanPairNorm y ≤ R)
    (hsum : R + ∑ i ∈ Finset.Ico j n, ε i ≤ S)
    (hprotected : ∀ i, j ≤ i → i < n → S ≤ a i)
    (hstep : ∀ i, j ≤ i → i < n → ∀ w, euclideanPairNorm w ≤ a i →
      euclideanPairNorm ((e i p).symm w - w) ≤ ε i) :
    euclideanPairNorm (product e j p ((product e n p).symm y)) ≤
        R + ∑ i ∈ Finset.Ico j n, ε i ∧
      R + ∑ i ∈ Finset.Ico j n, ε i ≤ S :=
  inverse_tail_prefix_bound e p a ε hε j n hjn y hy hsum hprotected hstep j le_rfl hjn

/-- Uniform finite-tail bounds give exactly the eventual closed bound needed
to place a convergent inverse sequence inside an entry domain. -/
theorem eventually_inverse_tail_le (e : ℕ → P → Pair ≃ₜ Pair) (p : P)
    (a ε : ℕ → ℝ) (hε : ∀ i, 0 ≤ ε i) (j : ℕ)
    (y : Pair) {R S : ℝ} (hy : euclideanPairNorm y ≤ R)
    (hsum : ∀ n, j ≤ n → R + ∑ i ∈ Finset.Ico j n, ε i ≤ S)
    (hprotected : ∀ i, j ≤ i → S ≤ a i)
    (hstep : ∀ i, j ≤ i → ∀ w, euclideanPairNorm w ≤ a i →
      euclideanPairNorm ((e i p).symm w - w) ≤ ε i) :
    ∀ᶠ n in atTop, euclideanPairNorm (product e j p ((product e n p).symm y)) ≤ S := by
  filter_upwards [eventually_ge_atTop j] with n hn
  have hb := inverse_tail_bound e p a ε hε j n hn y hy (hsum n hn)
    (fun i hi _ => hprotected i hi) (fun i hi _ => hstep i hi)
  exact hb.1.trans hb.2

/-- The adaptive half-budget condition supplies a finite tail estimate by
telescoping; no infinite-series theorem is needed. -/
theorem sum_quarter_budget_le (b : ℕ → ℝ) (hpos : ∀ i, 0 ≤ b i)
    (hhalf : ∀ i, b (i + 1) ≤ b i / 2) (j n : ℕ) (hjn : j ≤ n) :
    ∑ i ∈ Finset.Ico j n, b i / 4 ≤ b j / 2 := by
  have htel : ∑ i ∈ Finset.Ico j n, b i / 4 ≤ (b j - b n) / 2 := by
    induction n, hjn using Nat.le_induction with
    | base => simp
    | succ k hk ih =>
      rw [Finset.sum_Ico_succ_top hk]
      linarith [hhalf k]
  exact htel.trans (by linarith [hpos n])

/-- Geometrically controlled inverse steps directly yield the eventual bound
used by the entry-domain limit argument. -/
theorem eventually_inverse_tail_le_of_geometric_budget
    (e : ℕ → P → Pair ≃ₜ Pair) (p : P) (a b : ℕ → ℝ)
    (hpos : ∀ i, 0 ≤ b i) (hhalf : ∀ i, b (i + 1) ≤ b i / 2) (j : ℕ)
    (y : Pair) {R S : ℝ} (hy : euclideanPairNorm y ≤ R)
    (hbudget : R + b j / 2 ≤ S) (hprotected : ∀ i, j ≤ i → S ≤ a i)
    (hstep : ∀ i, j ≤ i → ∀ w, euclideanPairNorm w ≤ a i →
      euclideanPairNorm ((e i p).symm w - w) ≤ b i / 4) :
    ∀ᶠ n in atTop, euclideanPairNorm (product e j p ((product e n p).symm y)) ≤ S := by
  apply eventually_inverse_tail_le e p a (fun i => b i / 4)
    (fun i => div_nonneg (hpos i) (by norm_num)) j y hy
    (fun n hn => (add_le_add (le_refl R) (sum_quarter_budget_le b hpos hhalf j n hn)).trans hbudget)
    hprotected hstep

end AutomaticContinuity.NonautonomousInverseTails

import AutomaticContinuity.Flags
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FieldSimp

/-!
# The numerical finite-dimensional coefficient estimate

This proves the geometric-series calculation in Section 3.3, equation
`coefficient-convergence`, once the pointwise Cauchy estimates on Taylor
coefficients are available. The analytic Cauchy estimate itself, the construction
of Taylor coefficients, and their embedding in the countably-variable coefficient
algebra are not supplied or assumed globally here. All coefficient inequalities
are explicit hypotheses of the corresponding conditional estimates.
-/

namespace AutomaticContinuity

open scoped BigOperators

/-- A multiindex in precisely `n` variables. -/
abbrev FiniteMultiIndex (n : ℕ) := Fin n → ℕ

/-- Total degree of a multiindex in finitely many variables. -/
def finiteTotalDegree {n : ℕ} (α : FiniteMultiIndex n) : ℕ := ∑ j, α j

set_option backward.isDefEq.respectTransparency false in
/-- The product geometric series giving the factor `2ⁿ` in the Cauchy estimate. -/
theorem hasSum_half_pow_finiteTotalDegree (n : ℕ) :
    HasSum (fun α : FiniteMultiIndex n => (1 / 2 : ℝ) ^ finiteTotalDegree α) (2 ^ n) := by
  classical
  induction n with
  | zero =>
      simp [finiteTotalDegree]
  | succ n ih =>
      have hgeom : HasSum (fun j : ℕ => (1 / 2 : ℝ) ^ j) 2 := hasSum_geometric_two
      have hmul : Summable (fun p : ℕ × FiniteMultiIndex n =>
          (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ finiteTotalDegree p.2) :=
        Summable.mul_of_nonneg
          (f := fun j : ℕ => (1 / 2 : ℝ) ^ j)
          (g := fun α : FiniteMultiIndex n => (1 / 2 : ℝ) ^ finiteTotalDegree α)
          hgeom.summable ih.summable
          (fun j => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) j)
          (fun α => pow_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (finiteTotalDegree α))
      have hprod : HasSum (fun p : ℕ × FiniteMultiIndex n =>
          (1 / 2 : ℝ) ^ p.1 * (1 / 2 : ℝ) ^ finiteTotalDegree p.2) (2 * 2 ^ n) :=
        HasSum.mul
          (f := fun j : ℕ => (1 / 2 : ℝ) ^ j)
          (g := fun α : FiniteMultiIndex n => (1 / 2 : ℝ) ^ finiteTotalDegree α)
          hgeom ih hmul
      apply (Fin.consEquiv (fun _ : Fin (n + 1) => ℕ)).hasSum_iff.mp
      simpa [Function.comp_def, Fin.consEquiv, finiteTotalDegree,
        Fin.sum_univ_succ, pow_add, pow_succ'] using hprod

theorem summable_half_pow_finiteTotalDegree (n : ℕ) :
    Summable (fun α : FiniteMultiIndex n => (1 / 2 : ℝ) ^ finiteTotalDegree α) :=
  (hasSum_half_pow_finiteTotalDegree n).summable

theorem tsum_half_pow_finiteTotalDegree (n : ℕ) :
    (∑' α : FiniteMultiIndex n, (1 / 2 : ℝ) ^ finiteTotalDegree α) = 2 ^ n :=
  (hasSum_half_pow_finiteTotalDegree n).tsum_eq

/-- A coefficient summand at real radius `r`, prior to embedding in the
countably-variable coefficient algebra. -/
noncomputable def finiteWeightedTerm {n : ℕ} (r : ℝ) (c : FiniteMultiIndex n → ℂ)
    (α : FiniteMultiIndex n) : ℝ := ‖c α‖ * r ^ finiteTotalDegree α

theorem finiteWeightedTerm_nonneg {n : ℕ} {r : ℝ} (hr : 0 ≤ r)
    (c : FiniteMultiIndex n → ℂ) (α : FiniteMultiIndex n) :
    0 ≤ finiteWeightedTerm r c α :=
  mul_nonneg (norm_nonneg _) (pow_nonneg hr _)

theorem finiteWeightedTerm_mono {n : ℕ} {r s : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s)
    (c : FiniteMultiIndex n → ℂ) (α : FiniteMultiIndex n) :
    finiteWeightedTerm r c α ≤ finiteWeightedTerm s c α := by
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr hrs _) (norm_nonneg _)

theorem finiteWeightedTerm_le_half_pow {n : ℕ} {r M : ℝ} (hr : 0 < r)
    {c : FiniteMultiIndex n → ℂ}
    (hCauchy : ∀ α, ‖c α‖ ≤ M / (2 * r) ^ finiteTotalDegree α)
    (α : FiniteMultiIndex n) :
    finiteWeightedTerm r c α ≤ M * (1 / 2 : ℝ) ^ finiteTotalDegree α := by
  calc
    finiteWeightedTerm r c α ≤
        (M / (2 * r) ^ finiteTotalDegree α) * r ^ finiteTotalDegree α :=
      mul_le_mul_of_nonneg_right (hCauchy α) (pow_nonneg hr.le _)
    _ = M * (r / (2 * r)) ^ finiteTotalDegree α := by rw [div_pow]; ring
    _ = M * (1 / 2 : ℝ) ^ finiteTotalDegree α := by
      have heq : r / (2 * r) = (1 / 2 : ℝ) := by field_simp
      rw [heq]

/-- The numerical conclusion of the finite-dimensional Cauchy argument.
Analytic estimates on the coefficients are the explicit `hCauchy` hypothesis. -/
theorem finiteCauchy_bound {n : ℕ} {r M : ℝ} (hr : 0 < r)
    {c : FiniteMultiIndex n → ℂ}
    (hCauchy : ∀ α, ‖c α‖ ≤ M / (2 * r) ^ finiteTotalDegree α) :
    Summable (finiteWeightedTerm r c) ∧
      (∑' α, finiteWeightedTerm r c α) ≤ M * 2 ^ n := by
  have hmajorant := (hasSum_half_pow_finiteTotalDegree n).mul_left M
  have hs : Summable (finiteWeightedTerm r c) :=
    Summable.of_nonneg_of_le (finiteWeightedTerm_nonneg hr.le c)
      (finiteWeightedTerm_le_half_pow hr hCauchy) hmajorant.summable
  refine ⟨hs, ?_⟩
  calc
    (∑' α, finiteWeightedTerm r c α) ≤
        ∑' α, M * (1 / 2 : ℝ) ^ finiteTotalDegree α :=
      hs.tsum_le_tsum (finiteWeightedTerm_le_half_pow hr hCauchy) hmajorant.summable
    _ = M * 2 ^ n := hmajorant.tsum_eq

/-- The exact `2^(-2N)` numerical bound from `coefficient-convergence`.
No existence of Taylor coefficients with the stated estimate is asserted. -/
theorem finiteStageCauchy_bound {n : ℕ} (hn : 0 < n)
    {c : FiniteMultiIndex n → ℂ}
    (hCauchy : ∀ α, ‖c α‖ ≤ ((2 : ℝ) ^ (3 * n))⁻¹ /
      (2 * (n : ℝ)) ^ finiteTotalDegree α) :
    Summable (finiteWeightedTerm (n : ℝ) c) ∧
      (∑' α, finiteWeightedTerm (n : ℝ) c α) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by
  obtain ⟨hs, hbound⟩ := finiteCauchy_bound (by exact_mod_cast hn) hCauchy
  refine ⟨hs, hbound.trans_eq ?_⟩
  rw [show 3 * n = 2 * n + n by omega, pow_add]
  field_simp

/-- The same stage estimate holds at every smaller nonnegative radius, as used
for each fixed coefficient seminorm in Section 3.3. -/
theorem finiteStageCauchy_bound_at_radius {n : ℕ} (hn : 0 < n)
    {r : ℝ} (hr : 0 ≤ r) (hrn : r ≤ n)
    {c : FiniteMultiIndex n → ℂ}
    (hCauchy : ∀ α, ‖c α‖ ≤ ((2 : ℝ) ^ (3 * n))⁻¹ /
      (2 * (n : ℝ)) ^ finiteTotalDegree α) :
    Summable (finiteWeightedTerm r c) ∧
      (∑' α, finiteWeightedTerm r c α) ≤ ((2 : ℝ) ^ (2 * n))⁻¹ := by
  obtain ⟨hs, hbound⟩ := finiteStageCauchy_bound hn hCauchy
  have hsr : Summable (finiteWeightedTerm r c) :=
    Summable.of_nonneg_of_le (finiteWeightedTerm_nonneg hr c)
      (finiteWeightedTerm_mono hr hrn c) hs
  exact ⟨hsr, (hsr.tsum_le_tsum (finiteWeightedTerm_mono hr hrn c) hs).trans hbound⟩

theorem stageCoefficientError_eq_quarter_pow (n : ℕ) :
    ((2 : ℝ) ^ (2 * n))⁻¹ = (1 / 4 : ℝ) ^ n := by
  rw [pow_mul, ← inv_pow]
  norm_num

/-- Summability of the numerical coefficient error bounds. -/
theorem hasSum_stageCoefficientErrors :
    HasSum (fun n : ℕ => ((2 : ℝ) ^ (2 * n))⁻¹) (4 / 3) := by
  simp_rw [stageCoefficientError_eq_quarter_pow]
  convert! hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num) using 1
  norm_num

theorem summable_stageCoefficientErrors :
    Summable (fun n : ℕ => ((2 : ℝ) ^ (2 * n))⁻¹) :=
  hasSum_stageCoefficientErrors.summable

/-- The total numerical bound for the differences starting at stage `N = 2`. -/
theorem hasSum_stageCoefficientErrors_from_two :
    HasSum (fun n : ℕ => ((2 : ℝ) ^ (2 * (n + 2)))⁻¹) (1 / 12) := by
  have hsum := hasSum_stageCoefficientErrors.mul_left (1 / 16 : ℝ)
  convert! hsum using 1
  · funext n
    rw [stageCoefficientError_eq_quarter_pow, stageCoefficientError_eq_quarter_pow, pow_add]
    norm_num
    ring
  · norm_num

end AutomaticContinuity

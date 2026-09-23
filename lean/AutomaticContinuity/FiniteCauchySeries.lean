import AutomaticContinuity.FiniteCauchyIntegral

/-!
# Convergence of finite Cauchy coefficient series

The geometric domination below is proved for actual iterated contour
coefficients. The subsequent analytic expansion uses one-variable Cauchy
expansion and justified interchange of summation and integration.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set
open scoped BigOperators Real

/-- The ordinary monomial in a finite tuple of complex variables. -/
def monomial {n : ℕ} (z : FinitePoint n) (α : FiniteMultiIndex n) : ℂ :=
  ∏ j, z j ^ α j

@[simp] theorem monomial_zero (z : FinitePoint 0) (α : FiniteMultiIndex 0) :
    monomial z α = 1 := by simp [monomial]

@[simp] theorem monomial_cons {n : ℕ} (z : FinitePoint (n + 1)) (m : ℕ)
    (α : FiniteMultiIndex n) :
    monomial z (Fin.cons m α) = z 0 ^ m * monomial (Fin.tail z) α := by
  simp only [monomial, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]

theorem norm_monomial_le {n : ℕ} {r : ℝ} (_hr : 0 ≤ r) (z : FinitePoint n)
    (hz : z ∈ polydisc n r) (α : FiniteMultiIndex n) :
    ‖monomial z α‖ ≤ r ^ finiteTotalDegree α := by
  calc
    ‖monomial z α‖ = ∏ j, ‖z j‖ ^ α j := by simp [monomial, norm_prod, norm_pow]
    _ ≤ ∏ j : Fin n, r ^ α j := by
      apply Finset.prod_le_prod₀ (fun j _ => pow_nonneg (norm_nonneg _) _)
      intro j _
      exact pow_le_pow_left₀ (norm_nonneg _) (hz j) _
    _ = r ^ finiteTotalDegree α := by
      rw [Finset.prod_pow_eq_pow_sum]
      rfl

/-- On the half-polydisc, all monomial terms have the common geometric majorant. -/
theorem norm_coefficient_mul_monomial_le {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (h : FinitePoint n → ℂ)
    (hbound : ∀ w ∈ polydisc n (2 * r), ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) (α : FiniteMultiIndex n) :
    ‖coefficient (fun _ => 2 * r) h α * monomial z α‖ ≤
      M * (1 / 2 : ℝ) ^ finiteTotalDegree α := by
  calc
    ‖coefficient (fun _ => 2 * r) h α * monomial z α‖ ≤
        ‖coefficient (fun _ => 2 * r) h α‖ * r ^ finiteTotalDegree α := by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_monomial_le hr.le z hz α) (norm_nonneg _)
    _ ≤ M * (1 / 2 : ℝ) ^ finiteTotalDegree α :=
      finiteWeightedTerm_le_half_pow hr
        (fun β => norm_coefficient_le_common (by positivity) h hbound β) α

/-- Absolute summability of the actual finite contour coefficient expansion. -/
theorem summable_coefficient_mul_monomial {n : ℕ} {r M : ℝ} (hr : 0 < r)
    (h : FinitePoint n → ℂ)
    (hbound : ∀ w ∈ polydisc n (2 * r), ‖h w‖ ≤ M)
    (z : FinitePoint n) (hz : z ∈ polydisc n r) :
    Summable (fun α => coefficient (fun _ => 2 * r) h α * monomial z α) := by
  exact ((summable_half_pow_finiteTotalDegree n).mul_left M).of_norm_bounded
    (norm_coefficient_mul_monomial_le hr h hbound z hz)

end AutomaticContinuity.FiniteCauchy

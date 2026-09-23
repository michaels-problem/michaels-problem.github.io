import AutomaticContinuity.PolynomialConvexity

set_option autoImplicit false

/-!
# Polynomial convexity of translated coordinate polydiscs

The standard norm on a finite coordinate space is the maximum norm, so its
closed balls are exactly translated coordinate polydiscs. A shifted coordinate
polynomial separates any exterior point.
-/

namespace AutomaticContinuity

open Metric

theorem isPolynomiallyConvex_closedBall {σ : Type*} [Fintype σ]
    (c : σ → ℂ) {R : ℝ} (hR : 0 ≤ R) :
    IsPolynomiallyConvexOf (fun z : σ → ℂ => z) (closedBall c R) := by
  classical
  apply (isPolynomiallyConvexOf_iff_separation _ _).mpr
  intro z hz
  rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR] at hz
  change ¬ ∀ j : σ, ‖z j - c j‖ ≤ R at hz
  obtain ⟨j, hj⟩ := not_forall.mp hz
  refine ⟨MvPolynomial.X j - MvPolynomial.C (c j), R, ?_, ?_⟩
  · intro w hw
    rw [mem_closedBall, dist_eq_norm, pi_norm_le_iff_of_nonneg hR] at hw
    change ∀ i : σ, ‖w i - c i‖ ≤ R at hw
    simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] using hw j
  · simpa only [map_sub, MvPolynomial.eval_X, MvPolynomial.eval_C] using lt_of_not_ge hj

end AutomaticContinuity

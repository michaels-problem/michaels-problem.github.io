import AutomaticContinuity.DirectionalCompleteFlows

set_option autoImplicit false

/-!
# Quantitative estimates for directional complete flows

The quadratic remainders use the Euclidean norm explicitly. The accompanying
product-norm bounds are consequences, for use in normed-space composition
estimates. No regularity of a coefficient is required for a pointwise bound.
-/

noncomputable section

namespace AutomaticContinuity.DirectionalCompleteFlows

open EuclideanPairRotations

theorem euclideanPairNorm_direction (s : ℂ) :
    euclideanPairNorm (direction s) = Real.sqrt (‖s‖ ^ 2 + 1) := by
  simp [euclideanPairNorm, direction]

theorem shearFlow_remainder (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    shearFlow s m c t w - w - t • shearField s m c w = 0 := by
  simp [shearFlow, shearField, mul_smul]

theorem overshearFlow_remainder (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    overshearFlow s m c t w - w - t • overshearField s m c w =
      ((Complex.exp (t * (c * linearForm s w ^ m)) - 1 -
        t * (c * linearForm s w ^ m)) * w.2) • direction s := by
  ext <;> simp [overshearFlow, overshearField, direction, smul_eq_mul] <;> ring

theorem euclidean_overshearFlow_remainder_eq (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    euclideanPairNorm (overshearFlow s m c t w - w - t • overshearField s m c w) =
      ‖Complex.exp (t * (c * linearForm s w ^ m)) - 1 -
        t * (c * linearForm s w ^ m)‖ * ‖w.2‖ * euclideanPairNorm (direction s) := by
  rw [overshearFlow_remainder, euclideanPairNorm_complex_smul, norm_mul]

/-- The directional remainder is exactly the scalar overshear remainder
multiplied by the Euclidean length of its direction. -/
theorem euclidean_overshearFlow_remainder_eq_standard
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) :
    euclideanPairNorm (overshearFlow s m c t w - w - t • overshearField s m c w) =
      euclideanPairNorm (OvershearEulerBounds.remainder
        (fun _ : Unit × ℂ => c * linearForm s w ^ m) t ((), 0, w.2)) *
      euclideanPairNorm (direction s) := by
  rw [euclidean_overshearFlow_remainder_eq, OvershearEulerBounds.norm_remainder_eq]

theorem euclidean_overshearFlow_remainder_le
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair)
    (hsmall : ‖t‖ * ‖c * linearForm s w ^ m‖ ≤ 1) :
    euclideanPairNorm (overshearFlow s m c t w - w - t • overshearField s m c w) ≤
      (‖t‖ * ‖c * linearForm s w ^ m‖) ^ 2 * ‖w.2‖ *
        euclideanPairNorm (direction s) := by
  rw [euclidean_overshearFlow_remainder_eq_standard]
  exact mul_le_mul_of_nonneg_right
    (OvershearEulerBounds.norm_remainder_le
      (fun _ : Unit × ℂ => c * linearForm s w ^ m) t ((), 0, w.2) hsmall)
    (euclideanPairNorm_nonneg _)

theorem euclidean_overshearFlow_remainder_le_uniform
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) {M B : ℝ}
    (hc : ‖c * linearForm s w ^ m‖ ≤ M) (hy : ‖w.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    euclideanPairNorm (overshearFlow s m c t w - w - t • overshearField s m c w) ≤
      ‖t‖ ^ 2 * M ^ 2 * B * euclideanPairNorm (direction s) := by
  rw [euclidean_overshearFlow_remainder_eq_standard]
  exact mul_le_mul_of_nonneg_right
    (OvershearEulerBounds.norm_remainder_le_uniform
      (fun _ : Unit × ℂ => c * linearForm s w ^ m) t ((), 0, w.2) hc hy hsmall)
    (euclideanPairNorm_nonneg _)

theorem euclidean_overshearFlow_inverse_remainder_le_uniform
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) {M B : ℝ}
    (hc : ‖c * linearForm s w ^ m‖ ≤ M) (hy : ‖w.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    euclideanPairNorm (overshearFlow s m c (-t) w - w + t • overshearField s m c w) ≤
      ‖t‖ ^ 2 * M ^ 2 * B * euclideanPairNorm (direction s) := by
  simpa only [norm_neg, neg_smul, sub_neg_eq_add] using
    euclidean_overshearFlow_remainder_le_uniform s m c (-t) w hc hy
      (by simpa only [norm_neg] using hsmall)

/-- Default product-norm version of the same Euclidean estimate. -/
theorem norm_overshearFlow_remainder_le_uniform
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) {M B : ℝ}
    (hc : ‖c * linearForm s w ^ m‖ ≤ M) (hy : ‖w.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    ‖overshearFlow s m c t w - w - t • overshearField s m c w‖ ≤
      ‖t‖ ^ 2 * M ^ 2 * B * euclideanPairNorm (direction s) :=
  (norm_le_euclideanPairNorm _).trans
    (euclidean_overshearFlow_remainder_le_uniform s m c t w hc hy hsmall)

theorem norm_overshearFlow_inverse_remainder_le_uniform
    (s : ℂ) (m : ℕ) (c t : ℂ) (w : Pair) {M B : ℝ}
    (hc : ‖c * linearForm s w ^ m‖ ≤ M) (hy : ‖w.2‖ ≤ B)
    (hsmall : ‖t‖ * M ≤ 1) :
    ‖overshearFlow s m c (-t) w - w + t • overshearField s m c w‖ ≤
      ‖t‖ ^ 2 * M ^ 2 * B * euclideanPairNorm (direction s) :=
  (norm_le_euclideanPairNorm _).trans
    (euclidean_overshearFlow_inverse_remainder_le_uniform s m c t w hc hy hsmall)

end AutomaticContinuity.DirectionalCompleteFlows

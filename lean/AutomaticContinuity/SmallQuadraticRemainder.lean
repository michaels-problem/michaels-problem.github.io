import AutomaticContinuity.HolomorphicQuadraticRemainder

set_option autoImplicit false

/-! # Quadratic remainder balls with an arbitrary positive smallness tolerance -/

namespace AutomaticContinuity.HolomorphicQuadraticRemainder

open Metric

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_quadratic_remainder_le (T : E → F) (A : E →L[ℂ] F)
    (hT : Differentiable ℂ T) (hT0 : T 0 = 0) (hTd : HasFDerivAt T A 0)
    {η : ℝ} (hη : 0 < η) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ C * r ≤ η ∧
      ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2 := by
  obtain ⟨R, C, hR, hC, _, hrem⟩ := exists_small_quadratic_remainder T A hT hT0 hTd
  have hCp : 0 < C + 1 := by linarith
  let r := min R (η / (C + 1))
  refine ⟨r, C, lt_min hR (div_pos hη hCp), hC, ?_, ?_⟩
  · have hr : r ≤ η / (C + 1) := min_le_right _ _
    calc
      C * r ≤ C * (η / (C + 1)) := mul_le_mul_of_nonneg_left hr hC
      _ ≤ η := by
        rw [← mul_div_assoc, div_le_iff₀ hCp]
        nlinarith
  · intro x hx
    exact hrem x ((closedBall_subset_closedBall (min_le_left _ _)) hx)

end AutomaticContinuity.HolomorphicQuadraticRemainder

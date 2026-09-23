import AutomaticContinuity.LocalLinearization
import Mathlib.Analysis.Complex.Schwarz

set_option autoImplicit false

/-!
# A quadratic remainder from the higher-order Schwarz estimate

Complex differentiability near zero and the prescribed first derivative imply
an actual quadratic norm estimate on a sufficiently small ball. This discharges
the quantitative input in the normalized rescaled-iterate construction without
assuming a Taylor expansion in several variables.
-/

noncomputable section

namespace AutomaticContinuity.HolomorphicQuadraticRemainder

open Filter Metric Set
open scoped Topology

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem exists_small_quadratic_remainder (T : E → F) (A : E →L[ℂ] F)
    (hT : Differentiable ℂ T) (hT0 : T 0 = 0) (hTd : HasFDerivAt T A 0) :
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧ C * r ≤ 1 / 12 ∧
      ∀ x ∈ closedBall (0 : E) r, ‖T x - A x‖ ≤ C * ‖x‖ ^ 2 := by
  let f : E → F := fun x => T x - A x
  have hf : Differentiable ℂ f := hT.sub A.differentiable
  have hf0 : f 0 = 0 := by simp [f, hT0]
  have hfd : HasFDerivAt f (0 : E →L[ℂ] F) 0 := by
    convert hTd.sub A.hasFDerivAt using 1
    · funext x
      rfl
    · exact (sub_self A).symm
  have hsmall : {x : E | ‖f x‖ < 1} ∈ 𝓝 0 := by
    have hcont : ContinuousAt (fun x : E => ‖f x‖) 0 := hf.continuous.continuousAt.norm
    exact hcont.preimage_mem_nhds (Iio_mem_nhds (by simp [hf0]))
  obtain ⟨R, hR, hbound⟩ := Metric.mem_nhds_iff.mp hsmall
  have hmap : MapsTo f (ball (0 : E) R) (closedBall (f 0) 1) := by
    intro x hx
    rw [mem_closedBall, hf0, dist_zero_right]
    exact (hbound hx).le
  have hlo : (fun x => f x - f 0) =o[𝓝 (0 : E)] (fun x => ‖x - 0‖ ^ (1 : ℕ)) := by
    simpa only [zero_apply, sub_zero, pow_one] using hfd.isLittleO.norm_right
  let r : ℝ := min (R / 2) (R ^ 2 / 12)
  have hr : 0 < r := lt_min (half_pos hR) (by positivity)
  have hrR : r < R := (min_le_left _ _).trans_lt (half_lt_self hR)
  have hRne : R ≠ 0 := hR.ne'
  refine ⟨r, (R ^ 2)⁻¹, hr, by positivity, ?_, ?_⟩
  · have hh : r ≤ R ^ 2 / 12 := min_le_right _ _
    calc
      (R ^ 2)⁻¹ * r ≤ (R ^ 2)⁻¹ * (R ^ 2 / 12) := by gcongr
      _ = 1 / 12 := by field_simp
  · intro x hx
    have hxR : x ∈ ball (0 : E) R := (closedBall_subset_ball hrR) hx
    have h := Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO
      hf.differentiableOn hmap hlo hxR
    simp only [hf0, dist_zero_right, one_mul, Nat.reduceAdd] at h
    change ‖f x‖ ≤ _
    calc
      ‖f x‖ ≤ (‖x‖ / R) ^ 2 := h
      _ = (R ^ 2)⁻¹ * ‖x‖ ^ 2 := by ring

end AutomaticContinuity.HolomorphicQuadraticRemainder

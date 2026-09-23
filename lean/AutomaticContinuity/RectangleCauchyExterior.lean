import AutomaticContinuity.RectangleCauchyReproduction

set_option autoImplicit false

/-! # Vanishing of the rectangular Cauchy transform at exterior poles -/

noncomputable section
namespace AutomaticContinuity.RectangleCauchy
open Complex Set
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem rectangleIntegral_inv_smul_eq_zero (f : ℂ → E) {l r b t : ℝ} {z : ℂ}
    (hlr : l ≤ r) (hbt : b ≤ t) (hz : z ∉ closedRectangle l r b t)
    (hc : ContinuousOn f (closedRectangle l r b t))
    (hd : DifferentiableOn ℂ f (openRectangle l r b t)) :
    rectangleIntegral l r b t (fun w => (w - z)⁻¹ • f w) = 0 := by
  have hne (w : ℂ) (hw : w ∈ closedRectangle l r b t) : w - z ≠ 0 :=
    sub_ne_zero.mpr (ne_of_mem_of_not_mem hw hz)
  apply rectangleIntegral_eq_zero_off_countable _ hlr hbt ∅ countable_empty
  · exact ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul hc
  · intro w hw
    exact (((differentiableAt_id.sub_const z).inv
      (hne w (openRectangle_subset_closedRectangle l r b t hw.1))).smul
      (hd.differentiableAt ((isOpen_openRectangle l r b t).mem_nhds hw.1)))

end AutomaticContinuity.RectangleCauchy

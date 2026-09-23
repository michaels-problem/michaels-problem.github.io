import AutomaticContinuity.RectangleCauchyKernel
import AutomaticContinuity.RectangleCauchyAlgebra

set_option autoImplicit false

/-! # Vector-valued rectangular Cauchy reproduction

The removable divided difference is continuous on the closed rectangle and
holomorphic away from its centre.  Off-countable rectangular Goursat then
reduces reproduction to the explicitly evaluated scalar Cauchy kernel.
-/

noncomputable section
namespace AutomaticContinuity.RectangleCauchy
open Complex Set MeasureTheory Filter Function
open scoped Interval

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem rectangleIntegral_inv_smul (f : ℂ → E) {l r b t : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle l r b t)
    (hc : ContinuousOn f (closedRectangle l r b t))
    (hd : DifferentiableOn ℂ f (openRectangle l r b t)) :
    rectangleIntegral l r b t (fun w => (w - z)⁻¹ • f w) =
      (2 * Real.pi * I : ℂ) • f z := by
  have hlr : l ≤ r := (hz.1.1.trans hz.1.2).le
  have hbt : b ≤ t := (hz.2.1.trans hz.2.2).le
  have hnhds : closedRectangle l r b t ∈ nhds z :=
    mem_of_superset ((isOpen_openRectangle l r b t).mem_nhds hz)
      (openRectangle_subset_closedRectangle l r b t)
  let F : ℂ → E := dslope f z
  have hcF : ContinuousOn F (closedRectangle l r b t) :=
    (continuousOn_dslope hnhds).2
      ⟨hc, hd.differentiableAt ((isOpen_openRectangle l r b t).mem_nhds hz)⟩
  have hdF : ∀ w ∈ openRectangle l r b t \ {z}, DifferentiableAt ℂ F w := by
    intro w hw
    exact (differentiableAt_dslope_of_ne (by simpa only [mem_singleton_iff] using hw.2)).2
      (hd.differentiableAt ((isOpen_openRectangle l r b t).mem_nhds hw.1))
  have HI := rectangleIntegral_eq_zero_off_countable F hlr hbt {z}
    (countable_singleton z) hcF hdF
  have hFeq : EqOn F (fun w => (w - z)⁻¹ • f w - (w - z)⁻¹ • f z)
      (rectangleBoundary l r b t) := by
    intro w hw
    calc
      F w = (w - z)⁻¹ • (f w - f z) := update_of_ne (boundary_ne_interior hw hz) ..
      _ = _ := smul_sub _ _ _
  have hkernel : ContinuousOn (fun w : ℂ => (w - z)⁻¹)
      (rectangleBoundary l r b t) :=
    (continuousOn_id.sub continuousOn_const).inv₀
      (fun w hw => sub_ne_zero.mpr (boundary_ne_interior hw hz))
  have hi₁ : BoundaryIntegrable l r b t (fun w => (w - z)⁻¹ • f w) :=
    boundaryIntegrable_of_continuousOn hlr hbt
      (hkernel.smul (hc.mono (rectangleBoundary_subset_closedRectangle l r b t)))
  have hi₂ : BoundaryIntegrable l r b t (fun w => (w - z)⁻¹ • f z) :=
    boundaryIntegrable_of_continuousOn hlr hbt
      (hkernel.smul (continuousOn_const : ContinuousOn (fun _ : ℂ => f z) _))
  have hh := rectangleIntegral_congr hlr hbt hFeq
  rw [rectangleIntegral_sub hi₁ hi₂, rectangleIntegral_smul_const,
    rectangleIntegral_kernel hz, HI] at hh
  exact sub_eq_zero.mp hh.symm

theorem normalized_rectangleIntegral_inv_smul (f : ℂ → E) {l r b t : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle l r b t)
    (hc : ContinuousOn f (closedRectangle l r b t))
    (hd : DifferentiableOn ℂ f (openRectangle l r b t)) :
    (2 * Real.pi * I : ℂ)⁻¹ •
      rectangleIntegral l r b t (fun w => (w - z)⁻¹ • f w) = f z := by
  rw [rectangleIntegral_inv_smul f hz hc hd, inv_smul_smul₀]
  simp [Real.pi_ne_zero, I_ne_zero]

end AutomaticContinuity.RectangleCauchy

import AutomaticContinuity.RectangleCauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

set_option autoImplicit false

/-! # The rectangular Cauchy kernel has integral `2πi`

Principal logarithms give primitives on the bottom, right, and top sides.
On the left side the primitive is the logarithm of the negative argument.
The two explicitly checked branch jumps give the positive winding constant.
-/

noncomputable section

namespace AutomaticContinuity.RectangleCauchy

open Complex Set MeasureTheory
open scoped Interval

theorem horizontal_kernel_eq_log {l r y : ℝ} (z : ℂ)
    (hslit : ∀ x ∈ Set.uIcc l r, (x : ℂ) + (y : ℂ) * I - z ∈ slitPlane) :
    horizontalIntegral l r y (fun w => (w - z)⁻¹) =
      log ((r : ℂ) + (y : ℂ) * I - z) - log ((l : ℂ) + (y : ℂ) * I - z) := by
  have hi : ContinuousOn (fun x : ℝ => ((x : ℂ) + (y : ℂ) * I - z)⁻¹)
      (Set.uIcc l r) :=
    (by fun_prop : Continuous (fun x : ℝ => (x : ℂ) + (y : ℂ) * I - z)).continuousOn.inv₀
      (fun x hx => slitPlane_ne_zero (hslit x hx))
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi.intervalIntegrable
  intro x hx
  simpa only [id_eq, one_div] using!
    ((((hasDerivAt_id (x : ℂ)).add_const ((y : ℂ) * I)).sub_const z).clog (hslit x hx)).comp_ofReal

theorem vertical_kernel_eq_log {b t x : ℝ} (z : ℂ)
    (hslit : ∀ y ∈ Set.uIcc b t, (x : ℂ) + (y : ℂ) * I - z ∈ slitPlane) :
    verticalIntegral b t x (fun w => (w - z)⁻¹) =
      log ((x : ℂ) + (t : ℂ) * I - z) - log ((x : ℂ) + (b : ℂ) * I - z) := by
  have hi : ContinuousOn (fun y : ℝ => I * ((x : ℂ) + (y : ℂ) * I - z)⁻¹)
      (Set.uIcc b t) :=
    continuousOn_const.mul
      ((by fun_prop : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I - z)).continuousOn.inv₀
        (fun y hy => slitPlane_ne_zero (hslit y hy)))
  rw [verticalIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi.intervalIntegrable
  intro y hy
  simpa only [id_eq, one_mul, div_eq_mul_inv] using!
    ((((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const z |>.clog
      (hslit y hy)).comp_ofReal

theorem vertical_kernel_eq_log_neg {b t x : ℝ} (z : ℂ)
    (hslit : ∀ y ∈ Set.uIcc b t, -((x : ℂ) + (y : ℂ) * I - z) ∈ slitPlane) :
    verticalIntegral b t x (fun w => (w - z)⁻¹) =
      log (-((x : ℂ) + (t : ℂ) * I - z)) -
        log (-((x : ℂ) + (b : ℂ) * I - z)) := by
  have hne : ∀ y ∈ Set.uIcc b t, (x : ℂ) + (y : ℂ) * I - z ≠ 0 := by
    intro y hy hh
    apply slitPlane_ne_zero (hslit y hy)
    rw [hh, neg_zero]
  have hi : ContinuousOn (fun y : ℝ => I * ((x : ℂ) + (y : ℂ) * I - z)⁻¹)
      (Set.uIcc b t) :=
    continuousOn_const.mul
      ((by fun_prop : Continuous (fun y : ℝ => (x : ℂ) + (y : ℂ) * I - z)).continuousOn.inv₀ hne)
  rw [verticalIntegral, smul_eq_mul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi.intervalIntegrable
  intro y hy
  simpa only [id_eq, Pi.neg_apply, one_mul, neg_div_neg_eq, div_eq_mul_inv, inv_neg, neg_mul_neg] using!
    (((((hasDerivAt_id (y : ℂ)).mul_const I).const_add (x : ℂ)).sub_const z).neg.clog
      (hslit y hy)).comp_ofReal

theorem log_sub_log_neg_of_im_pos {z : ℂ} (hz : 0 < z.im) :
    log z - log (-z) = (Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_sub_pi_of_im_pos hz]
  push_cast
  ring

theorem log_sub_log_neg_of_im_neg {z : ℂ} (hz : z.im < 0) :
    log z - log (-z) = -(Real.pi : ℂ) * I := by
  rw [Complex.log, Complex.log, norm_neg, arg_neg_eq_arg_add_pi_of_im_neg hz]
  push_cast
  ring

/-- The positively oriented rectangle winds once around each strictly
interior point. All four contour edges avoid the kernel singularity. -/
theorem rectangleIntegral_kernel {l r b t : ℝ} {z : ℂ}
    (hz : z ∈ openRectangle l r b t) :
    rectangleIntegral l r b t (fun w => (w - z)⁻¹) = (2 * Real.pi * I : ℂ) := by
  have hzre : l < z.re ∧ z.re < r := hz.1
  have hzim : b < z.im ∧ z.im < t := hz.2
  have hb : ∀ x ∈ Set.uIcc l r, (x : ℂ) + (b : ℂ) * I - z ∈ slitPlane := by
    intro x _
    apply mem_slitPlane_iff.mpr
    right
    simp only [sub_im, add_im, ofReal_im, mul_im, I_im, ofReal_re, mul_one,
      I_re, mul_zero, add_zero, zero_add]
    linarith
  have ht : ∀ x ∈ Set.uIcc l r, (x : ℂ) + (t : ℂ) * I - z ∈ slitPlane := by
    intro x _
    apply mem_slitPlane_iff.mpr
    right
    simp only [sub_im, add_im, ofReal_im, mul_im, I_im, ofReal_re, mul_one,
      I_re, mul_zero, add_zero, zero_add]
    linarith
  have hr : ∀ y ∈ Set.uIcc b t, (r : ℂ) + (y : ℂ) * I - z ∈ slitPlane := by
    intro y _
    apply mem_slitPlane_iff.mpr
    left
    simp only [sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  have hl : ∀ y ∈ Set.uIcc b t, -((l : ℂ) + (y : ℂ) * I - z) ∈ slitPlane := by
    intro y _
    apply mem_slitPlane_iff.mpr
    left
    simp only [neg_re, sub_re, add_re, ofReal_re, mul_re, I_re, ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero]
    linarith
  rw [rectangleIntegral, horizontal_kernel_eq_log z hb, horizontal_kernel_eq_log z ht,
    vertical_kernel_eq_log z hr, vertical_kernel_eq_log_neg z hl]
  have htop : 0 < ((l : ℂ) + (t : ℂ) * I - z).im := by simp; linarith
  have hbottom : ((l : ℂ) + (b : ℂ) * I - z).im < 0 := by simp; linarith
  have hT := log_sub_log_neg_of_im_pos htop
  have hB := log_sub_log_neg_of_im_neg hbottom
  calc
    _ = (log ((l : ℂ) + (t : ℂ) * I - z) - log (-((l : ℂ) + (t : ℂ) * I - z))) -
        (log ((l : ℂ) + (b : ℂ) * I - z) - log (-((l : ℂ) + (b : ℂ) * I - z))) := by ring
    _ = (2 * Real.pi * I : ℂ) := by rw [hT, hB]; ring

end AutomaticContinuity.RectangleCauchy

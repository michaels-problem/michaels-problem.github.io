import AutomaticContinuity.FiniteCauchyIntegral

/-!
# Expansion of the Cauchy transform of a circle-integrable scalar function

This layer uses no holomorphicity hypothesis. Its coefficient integrals agree
exactly with those in the finite-dimensional construction, and its series sums
to the normalized Cauchy transform inside the contour.
-/

noncomputable section

namespace AutomaticContinuity.OneVariableCauchy

open Complex Metric
open scoped Real

/-- Evaluation of Mathlib's Cauchy power series agrees exactly with the scalar
coefficient-integral convention used in the finite-dimensional construction. -/
theorem cauchyPowerSeries_apply_eq (h : ℂ → ℂ) (R : ℝ) (m : ℕ) (z : ℂ) :
    cauchyPowerSeries h 0 R m (fun _ => z) = FiniteCauchy.circleCoeff R m h * z ^ m := by
  simp [cauchyPowerSeries, FiniteCauchy.circleCoeff,
    ContinuousMultilinearMap.mkPiRing_apply, smul_eq_mul,
    div_eq_mul_inv, pow_succ, mul_assoc, mul_left_comm, mul_comm]

/-- A coefficient expansion for an arbitrary circle-integrable function. Inside
the contour it sums to the Cauchy transform. This does not require the function
being integrated to be holomorphic. -/
theorem hasSum_circleCoeff_mul_pow_integral {h : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hh : CircleIntegrable h 0 R) (hz : ‖z‖ < R) :
    HasSum (fun m : ℕ => FiniteCauchy.circleCoeff R m h * z ^ m)
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ ζ in C(0, R), h ζ / (ζ - z)) := by
  have hsum := hasSum_cauchyPowerSeries_integral hh hz
  simpa only [cauchyPowerSeries_apply_eq, zero_add, smul_eq_mul, div_eq_mul_inv,
    mul_comm] using hsum

theorem hasSum_circleCoeff_mul_pow_integral_of_continuousOn
    {h : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hh : ContinuousOn h (sphere (0 : ℂ) R)) (hz : ‖z‖ < R) :
    HasSum (fun m : ℕ => FiniteCauchy.circleCoeff R m h * z ^ m)
      ((2 * Real.pi * Complex.I : ℂ)⁻¹ * ∮ ζ in C(0, R), h ζ / (ζ - z)) :=
  hasSum_circleCoeff_mul_pow_integral (hh.circleIntegrable ((norm_nonneg z).trans hz.le)) hz

end AutomaticContinuity.OneVariableCauchy

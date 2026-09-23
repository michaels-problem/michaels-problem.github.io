import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.GCongr

set_option autoImplicit false

/-!
# Summation under a Cauchy contour integral

The hypotheses give a summable uniform bound on the circle. Pulling back to the
angle parameter gives an integrable constant majorant, so dominated convergence
applies without any assumption on the values of the limit away from the circle.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex Metric Set MeasureTheory
open scoped Real Topology

universe u

/-- A normally convergent series on a circle may be integrated term by term. -/
theorem hasSum_circleIntegral_of_summable_bound {ι : Type u} [Countable ι]
    {R : ℝ} (hR : 0 < R) (f : ι → ℂ → ℂ) (g : ℂ → ℂ)
    (hf : ∀ i, ContinuousOn (f i) (sphere (0 : ℂ) R))
    (a : ι → ℝ) (ha : Summable a)
    (hbound : ∀ i ζ, ζ ∈ sphere (0 : ℂ) R → ‖f i ζ‖ ≤ a i)
    (hsum : ∀ ζ ∈ sphere (0 : ℂ) R, HasSum (fun i => f i ζ) (g ζ)) :
    HasSum (fun i => ∮ ζ in C(0, R), f i ζ) (∮ ζ in C(0, R), g ζ) := by
  unfold circleIntegral
  apply intervalIntegral.hasSum_integral_of_dominated_convergence
    (fun i (_θ : ℝ) => R * a i)
  · intro i
    have hc : Continuous (fun θ : ℝ =>
        deriv (circleMap 0 R) θ • f i (circleMap 0 R θ)) := by
      simp only [deriv_circleMap]
      exact ((continuous_circleMap 0 R).mul_const I).smul
        ((hf i).comp_continuous (continuous_circleMap 0 R) (circleMap_mem_sphere 0 hR.le))
    exact hc.aestronglyMeasurable
  · intro i
    exact Filter.Eventually.of_forall fun θ _hθ => by
      simp only [deriv_circleMap, norm_smul, norm_mul, norm_circleMap_zero,
        abs_of_pos hR, norm_I, mul_one]
      exact mul_le_mul_of_nonneg_left (hbound i _ (circleMap_mem_sphere 0 hR.le θ)) hR.le
  · exact Filter.Eventually.of_forall fun _θ _hθ => ha.mul_left R
  · exact intervalIntegrable_const
  · exact Filter.Eventually.of_forall fun θ _hθ =>
      (hsum _ (circleMap_mem_sphere 0 hR.le θ)).const_smul _

/-- The exact kernel-weighted sum exchange used in the finite Taylor induction. -/
theorem hasSum_cauchyIntegral_of_summable_bound {ι : Type u} [Countable ι]
    {R : ℝ} (hR : 0 < R) {z : ℂ} (hz : ‖z‖ < R)
    (f : ι → ℂ → ℂ) (g : ℂ → ℂ) (hf : ∀ i, Continuous (f i))
    (a : ι → ℝ) (ha : Summable a) (ha0 : ∀ i, 0 ≤ a i)
    (hbound : ∀ i ζ, ζ ∈ sphere (0 : ℂ) R → ‖f i ζ‖ ≤ a i)
    (hsum : ∀ ζ ∈ sphere (0 : ℂ) R, HasSum (fun i => f i ζ) (g ζ)) :
    HasSum
      (fun i => (2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, R), f i ζ / (ζ - z))
      ((2 * Real.pi * I : ℂ)⁻¹ * ∮ ζ in C(0, R), g ζ / (ζ - z)) := by
  have hD : 0 < R - ‖z‖ := sub_pos.mpr hz
  have hden (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) : R - ‖z‖ ≤ ‖ζ - z‖ := by
    have hnorm : ‖ζ‖ = R := by simpa only [mem_sphere, dist_zero_right] using hζ
    simpa only [hnorm] using norm_sub_norm_le ζ z
  have hnz (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) : ζ - z ≠ 0 := by
    exact norm_pos_iff.mp (hD.trans_le (hden ζ hζ))
  have hcont (i : ι) : ContinuousOn (fun ζ => f i ζ / (ζ - z)) (sphere (0 : ℂ) R) :=
    (hf i).continuousOn.div (continuous_id.sub continuous_const).continuousOn hnz
  have hbound' (i : ι) (ζ : ℂ) (hζ : ζ ∈ sphere (0 : ℂ) R) :
      ‖f i ζ / (ζ - z)‖ ≤ a i / (R - ‖z‖) := by
    rw [norm_div]
    exact div_le_div₀ (ha0 i) (hbound i ζ hζ) hD (hden ζ hζ)
  have hi := hasSum_circleIntegral_of_summable_bound hR
    (fun i ζ => f i ζ / (ζ - z)) (fun ζ => g ζ / (ζ - z)) hcont
    (fun i => a i / (R - ‖z‖)) (ha.div_const _) hbound'
    (fun ζ hζ => (hsum ζ hζ).div_const _)
  exact hi.mul_left _

end AutomaticContinuity.FiniteCauchy

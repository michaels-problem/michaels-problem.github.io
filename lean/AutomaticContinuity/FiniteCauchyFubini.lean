import AutomaticContinuity.FiniteCauchyIntegral
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false

/-!
# Interchanging finite coefficient contour integrals

The argument applies Fubini only after proving integrability of the continuous
angular kernel on a compact square. It does not assume holomorphic dependence
of an integral on a parameter.
-/

noncomputable section

namespace AutomaticContinuity.FiniteCauchy

open Complex MeasureTheory Set
open scoped Real

def angularKernel (R : ℝ) (m : ℕ) (θ : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I : ℂ)⁻¹ * deriv (circleMap 0 R) θ /
    (circleMap 0 R θ) ^ (m + 1)

theorem continuous_angularKernel {R : ℝ} (hR : 0 < R) (m : ℕ) :
    Continuous (angularKernel R m) := by
  have hne (θ : ℝ) : circleMap 0 R θ ≠ 0 := by
    apply norm_ne_zero_iff.mp
    rw [norm_circleMap_zero, abs_of_pos hR]
    exact hR.ne'
  have hd : Continuous (fun θ => deriv (circleMap 0 R) θ) := by
    simp_rw [deriv_circleMap]
    fun_prop
  exact (continuous_const.mul hd).div ((continuous_circleMap 0 R).pow _)
    (fun θ => pow_ne_zero _ (hne θ))

theorem circleCoeff_eq_integral (R : ℝ) (m : ℕ) (h : ℂ → ℂ) :
    circleCoeff R m h = ∫ θ in Icc 0 (2 * Real.pi),
      angularKernel R m θ * h (circleMap 0 R θ) := by
  rw [circleCoeff, circleIntegral_def_Icc, ← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun θ => by
    simp only [angularKernel, smul_eq_mul, div_eq_mul_inv]
    ring

/-- Positive-radius coefficient extraction commutes in two coordinates. -/
theorem circleCoeff_comm {R S : ℝ} (hR : 0 < R) (hS : 0 < S)
    (m k : ℕ) (h : ℂ → ℂ → ℂ) (hh : Continuous h.uncurry) :
    circleCoeff R m (fun z => circleCoeff S k (h z)) =
      circleCoeff S k (fun w => circleCoeff R m (fun z => h z w)) := by
  let K : ℝ × ℝ → ℂ := fun p =>
    angularKernel R m p.1 * (angularKernel S k p.2 *
      h (circleMap 0 R p.1) (circleMap 0 S p.2))
  have hK : Continuous K := by
    apply ((continuous_angularKernel hR m).comp continuous_fst).mul
    apply ((continuous_angularKernel hS k).comp continuous_snd).mul
    exact hh.comp (((continuous_circleMap 0 R).comp continuous_fst).prodMk
      ((continuous_circleMap 0 S).comp continuous_snd))
  have hi : Integrable K ((volume.restrict (Icc 0 (2 * Real.pi))).prod
      (volume.restrict (Icc 0 (2 * Real.pi)))) := by
    rw [Measure.prod_restrict]
    exact hK.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  simp_rw [circleCoeff_eq_integral, ← integral_const_mul]
  change (∫ θ in Icc 0 (2 * Real.pi), ∫ ψ in Icc 0 (2 * Real.pi), K (θ, ψ)) = _
  rw [integral_integral_swap hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ψ => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun θ => by
      dsimp [K]
      ring

/-- A separate coefficient contour commutes with a finite product of contours. -/
theorem coefficient_circleCoeff {n : ℕ} {R : ℝ} (hR : 0 < R) (m : ℕ)
    (S : Fin n → ℝ) (hS : ∀ j, 0 < S j)
    (h : ℂ → FinitePoint n → ℂ) (hh : Continuous h.uncurry)
    (α : FiniteMultiIndex n) :
    circleCoeff R m (fun z => coefficient S (h z) α) =
      coefficient S (fun w => circleCoeff R m (fun z => h z w)) α := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [coefficient_succ]
      let g : ℂ → ℂ → ℂ := fun z t =>
        coefficient (Fin.tail S) (fun w => h z (Fin.cons t w)) (Fin.tail α)
      have hg : Continuous g.uncurry := by
        apply continuous_coefficient (Fin.tail S) (fun j => hS j.succ)
        change Continuous (h.uncurry ∘ fun p : (ℂ × ℂ) × FinitePoint n =>
          (p.1.1, Fin.cons p.1.2 p.2))
        apply hh.comp
        apply Continuous.prodMk
        · fun_prop
        · apply continuous_pi
          intro j
          refine Fin.cases ?_ (fun j => ?_) j
          · simpa only [Fin.cons_zero] using
              (continuous_fst.snd : Continuous (fun p : (ℂ × ℂ) × FinitePoint n => p.1.2))
          · simpa only [Fin.cons_succ, Function.comp_def] using
              ((continuous_apply j).comp continuous_snd :
                Continuous (fun p : (ℂ × ℂ) × FinitePoint n => p.2 j))
      rw [circleCoeff_comm hR (hS 0) m (α 0) g hg]
      congr 1
      funext t
      apply ih (Fin.tail S) (fun j => hS j.succ)
      change Continuous (h.uncurry ∘ fun p : ℂ × FinitePoint n =>
        (p.1, Fin.cons t p.2))
      apply hh.comp
      apply Continuous.prodMk
      · fun_prop
      · apply continuous_pi
        intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · simp only [Fin.cons_zero]
          fun_prop
        · simpa only [Fin.cons_succ, Function.comp_def] using
            ((continuous_apply j).comp continuous_snd :
              Continuous (fun p : ℂ × FinitePoint n => p.2 j))

end AutomaticContinuity.FiniteCauchy

import AutomaticContinuity.PolynomialFunctionAlgebra
import AutomaticContinuity.ArensBanach
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

set_option autoImplicit false

/-!
# Actual resolvents in the closed polynomial function algebra

Polynomial convexity identifies every character with evaluation. The checked
Banach-algebra Bezout dichotomy then constructs reciprocals of nonvanishing
elements. Weighted contour kernels can consequently be integrated in the
actual closed polynomial algebra, rather than assuming an approximation
principle for holomorphic functions.
-/

noncomputable section

namespace AutomaticContinuity.PolynomialFunctionAlgebra

open Set MeasureTheory
open scoped Topology

variable {σ : Type*} (K : Set (σ → ℂ)) [CompactSpace K]

def evaluation (x : K) : P K →ₐ[ℂ] ℂ :=
  (ContinuousMap.evalAlgHom ℂ ℂ x).comp (algebra K).val

@[simp] theorem evaluation_apply (x : K) (f : P K) :
    evaluation K x f = f.val x := rfl

/-- Nonvanishing in the actual compact set implies invertibility in its
closed polynomial algebra. -/
theorem isUnit_of_nonvanishing
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (f : P K) (hf : ∀ x : K, f.val x ≠ 0) : IsUnit f := by
  rcases Arens.solution_or_character (fun _ : Fin 1 => f) with ⟨b, hb⟩ | ⟨η, _, hη⟩
  · apply isUnit_iff_exists_inv.mpr
    refine ⟨b 0, ?_⟩
    simpa [Bezout.pairing] using hb
  · obtain ⟨x, hx⟩ := character_eq_evaluation K hK η
    exact False.elim (hf x (by simpa only [hx] using hη 0))

theorem isUnit_iff_nonvanishing
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K) (f : P K) :
    IsUnit f ↔ ∀ x : K, f.val x ≠ 0 := by
  refine ⟨?_, isUnit_of_nonvanishing K hK f⟩
  intro hf x
  exact ((evaluation K x).isUnit_map hf).ne_zero

theorem inverse_apply (f : P K) (hf : IsUnit f) (x : K) :
    (Ring.inverse f).val x = (f.val x)⁻¹ := by
  obtain ⟨u, rfl⟩ := hf
  rw [Ring.inverse_unit]
  have hmul := congrArg (evaluation K x) u.inv_mul
  simp only [map_mul, map_one, evaluation_apply] at hmul
  exact eq_inv_of_mul_eq_one_left hmul

/-- The coordinate denominator as an actual element of the polynomial algebra. -/
def coordinateDenominator (j : σ) (ζ : ℂ) : P K :=
  algebraMap ℂ (P K) ζ - polynomial K (MvPolynomial.X j)

@[simp] theorem coordinateDenominator_apply (j : σ) (ζ : ℂ) (x : K) :
    (coordinateDenominator K j ζ).val x = ζ - x.val j := by
  simp [coordinateDenominator, polynomial_apply]

def coordinateResolvent (j : σ) (ζ : ℂ) : P K :=
  Ring.inverse (coordinateDenominator K j ζ)

theorem coordinateDenominator_isUnit
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) (ζ : ℂ) (hζ : ∀ x : K, ζ ≠ x.val j) :
    IsUnit (coordinateDenominator K j ζ) := by
  apply isUnit_of_nonvanishing K hK
  intro x
  simpa only [coordinateDenominator_apply, sub_ne_zero] using hζ x

theorem coordinateResolvent_apply
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) (ζ : ℂ) (hζ : ∀ x : K, ζ ≠ x.val j) (x : K) :
    (coordinateResolvent K j ζ).val x = (ζ - x.val j)⁻¹ := by
  rw [coordinateResolvent, inverse_apply K _
    (coordinateDenominator_isUnit K hK j ζ hζ), coordinateDenominator_apply]

theorem continuousAt_coordinateResolvent
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) (ζ : ℂ) (hζ : ∀ x : K, ζ ≠ x.val j) :
    ContinuousAt (coordinateResolvent K j) ζ := by
  obtain ⟨u, hu⟩ := coordinateDenominator_isUnit K hK j ζ hζ
  have hinv : ContinuousAt Ring.inverse (coordinateDenominator K j ζ) :=
    hu ▸ NormedRing.inverse_continuousAt u
  exact hinv.comp (by
    change ContinuousAt (fun ζ : ℂ => algebraMap ℂ (P K) ζ -
      polynomial K (MvPolynomial.X j)) ζ
    fun_prop)

def evaluationCLM (x : K) : P K →L[ℂ] ℂ :=
  { (evaluation K x).toLinearMap with cont := map_continuous (evaluation K x) }

@[simp] theorem evaluationCLM_apply (x : K) (f : P K) :
    evaluationCLM K x f = f.val x := rfl

theorem continuousOn_coordinateResolvent_comp
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) {T : Set ℝ} (γ : ℝ → ℂ) (hγ : ContinuousOn γ T)
    (havoid : ∀ t ∈ T, ∀ x : K, γ t ≠ x.val j) :
    ContinuousOn (fun t => coordinateResolvent K j (γ t)) T := by
  intro t ht
  exact (continuousAt_coordinateResolvent K hK j (γ t) (havoid t ht)).comp_continuousWithinAt
    (hγ t ht)

/-- A weighted contour kernel integrated inside the actual closed polynomial
algebra. Its values therefore have genuine uniform polynomial approximations. -/
def weightedKernelIntegral (j : σ) (γ w : ℝ → ℂ) (a b : ℝ) : P K :=
  ∫ t in a..b, w t • coordinateResolvent K j (γ t)

theorem weightedKernelIntegral_apply
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hw : ContinuousOn w (uIcc a b))
    (havoid : ∀ t ∈ uIcc a b, ∀ x : K, γ t ≠ x.val j) (x : K) :
    (weightedKernelIntegral K j γ w a b).val x =
      ∫ t in a..b, w t / (γ t - x.val j) := by
  have hc := hw.smul (continuousOn_coordinateResolvent_comp K hK j γ hγ havoid)
  have hi : IntervalIntegrable (fun t => w t • coordinateResolvent K j (γ t)) volume a b :=
    hc.intervalIntegrable
  change evaluationCLM K x (∫ t in a..b, w t • coordinateResolvent K j (γ t)) = _
  rw [← (evaluationCLM K x).intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro t ht
  simp only [map_smul, evaluationCLM_apply,
    coordinateResolvent_apply K hK j (γ t) (havoid t ht) x, smul_eq_mul, div_eq_mul_inv]

theorem exists_polynomial_approx_weightedKernelIntegral
    (hK : IsPolynomiallyConvexOf (fun x : σ → ℂ => x) K)
    (j : σ) (γ w : ℝ → ℂ) {a b : ℝ}
    (hγ : ContinuousOn γ (uIcc a b)) (hw : ContinuousOn w (uIcc a b))
    (havoid : ∀ t ∈ uIcc a b, ∀ x : K, γ t ≠ x.val j)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial σ ℂ, ∀ x : K,
      ‖MvPolynomial.eval x.val p - ∫ t in a..b, w t / (γ t - x.val j)‖ < ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_approx K (weightedKernelIntegral K j γ w a b) hε
  refine ⟨p, fun x => ?_⟩
  have hx := (ContinuousMap.norm_coe_le_norm
    (polynomial K p - weightedKernelIntegral K j γ w a b).val x).trans_lt hp
  simpa only [Subalgebra.coe_sub, ContinuousMap.sub_apply, polynomial_apply,
    weightedKernelIntegral_apply K hK j γ w hγ hw havoid x] using hx

end AutomaticContinuity.PolynomialFunctionAlgebra

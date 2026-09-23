import AutomaticContinuity.Flags
import Mathlib.LinearAlgebra.Prod
import Mathlib.Tactic.Ring

set_option autoImplicit false

/-!
# Complex linear supporting functionals for the Euclidean pair norm

The target of the flag construction uses an explicit Euclidean norm on `ℂ × ℂ`.
This module constructs its norming functionals directly, without changing the
ambient product norm instance. These functionals give polynomial separators for
closed Euclidean balls.
-/

noncomputable section

namespace AutomaticContinuity

open ComplexConjugate

/-- The complex-linear functional given by the conjugate dot product with `a`. -/
def pairDot (a : ℂ × ℂ) : (ℂ × ℂ) →ₗ[ℂ] ℂ where
  toFun v := conj a.1 * v.1 + conj a.2 * v.2
  map_add' v w := by simp only [Prod.fst_add, Prod.snd_add]; ring
  map_smul' c v := by
    simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, RingHom.id_apply]
    ring

theorem norm_pairDot_le (a v : ℂ × ℂ) :
    ‖pairDot a v‖ ≤ euclideanPairNorm a * euclideanPairNorm v := by
  have htriangle : ‖pairDot a v‖ ≤ ‖a.1‖ * ‖v.1‖ + ‖a.2‖ * ‖v.2‖ := by
    simpa only [pairDot, LinearMap.coe_mk, AddHom.coe_mk, norm_mul, Complex.norm_conj]
      using norm_add_le (conj a.1 * v.1) (conj a.2 * v.2)
  apply htriangle.trans
  apply (sq_le_sq₀ (by positivity)
    (mul_nonneg (euclideanPairNorm_nonneg a) (euclideanPairNorm_nonneg v))).mp
  rw [mul_pow, euclideanPairNorm_sq, euclideanPairNorm_sq]
  nlinarith [sq_nonneg (‖a.1‖ * ‖v.2‖ - ‖a.2‖ * ‖v.1‖)]

theorem pairDot_self (a : ℂ × ℂ) :
    pairDot a a = (euclideanPairNorm a ^ 2 : ℝ) := by
  change conj a.1 * a.1 + conj a.2 * a.2 = _
  rw [Complex.conj_mul', Complex.conj_mul', euclideanPairNorm_sq]
  push_cast
  rfl

/-- A supporting functional of norm at most one, attaining the Euclidean norm
at the prescribed nonzero point. -/
theorem exists_pair_norming_functional (a : ℂ × ℂ) (ha : 0 < euclideanPairNorm a) :
    ∃ ℓ : (ℂ × ℂ) →ₗ[ℂ] ℂ,
      (∀ v, ‖ℓ v‖ ≤ euclideanPairNorm v) ∧ ‖ℓ a‖ = euclideanPairNorm a := by
  let ℓ : (ℂ × ℂ) →ₗ[ℂ] ℂ := ((euclideanPairNorm a : ℂ)⁻¹) • pairDot a
  have hnorm : ‖(euclideanPairNorm a : ℂ)‖ = euclideanPairNorm a := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  refine ⟨ℓ, ?_, ?_⟩
  · intro v
    change ‖(euclideanPairNorm a : ℂ)⁻¹ * pairDot a v‖ ≤ _
    rw [norm_mul, norm_inv, hnorm]
    calc
      _ ≤ (euclideanPairNorm a)⁻¹ *
          (euclideanPairNorm a * euclideanPairNorm v) :=
        mul_le_mul_of_nonneg_left (norm_pairDot_le a v) (by positivity)
      _ = euclideanPairNorm v := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]
  · change ‖(euclideanPairNorm a : ℂ)⁻¹ * pairDot a a‖ = _
    rw [pairDot_self, norm_mul, norm_inv, hnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg _)]
    field_simp

end AutomaticContinuity

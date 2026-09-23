import AutomaticContinuity.Evaluation
import AutomaticContinuity.CoefficientTopology
import AutomaticContinuity.Characters

/-!
# Continuous characters of the coefficient algebra

This file proves the elementary classification in Lemma `lem:characters`:
continuous unital complex algebra homomorphisms are precisely evaluations at
bounded complex sequences. It does not assert automatic continuity of arbitrary
algebra homomorphisms.
-/

noncomputable section

namespace AutomaticContinuity
namespace CoefficientSeries

/-- Evaluation at a bounded sequence is continuous for the coefficient topology. -/
theorem continuous_evaluationHom (w : BoundedSequence) : Continuous (evaluationHom w) := by
  obtain ⟨R, hR, hw⟩ := w.exists_integral_radius
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hR.ne'
  apply withSeminorms.continuous_normedSpace_rng ℂ (evaluationHom w).toLinearMap
  refine ⟨{r}, 1, ?_⟩
  intro f
  simpa [Seminorm.comp_apply, definingSeminorm] using
    norm_evaluate_le w f (Nat.succ_pos r) hw

/-- The family of coordinate elements is a bounded subset of the coefficient algebra. -/
theorem isVonNBounded_range_coordinate :
    Bornology.IsVonNBounded ℂ (Set.range coordinate) := by
  apply (bounded_iff_q (Set.range coordinate)).mpr
  intro n
  refine ⟨(n : ℝ) + 2, by positivity, ?_⟩
  rintro f ⟨j, rfl⟩
  simp only [q_coordinate, Nat.cast_add, Nat.cast_one]
  linarith

/-- Continuity bounds the values of a character on all coordinate elements. -/
theorem bounded_coordinateValues (φ : CoefficientSeries →ₐ[ℂ] ℂ)
    (hφ : Continuous φ) : ∃ C : ℝ, ∀ j : ℕ, ‖φ (coordinate j)‖ ≤ C := by
  let L : CoefficientSeries →L[ℂ] ℂ := ⟨φ.toLinearMap, hφ⟩
  have hb := isVonNBounded_range_coordinate.image L
  obtain ⟨C, hC⟩ := (NormedSpace.isVonNBounded_iff' ℂ).mp hb
  refine ⟨C, fun j => ?_⟩
  exact hC (φ (coordinate j)) ⟨coordinate j, ⟨j, rfl⟩, rfl⟩

/-- The bounded sequence of coordinate values of a continuous character. -/
def characterCoordinates (φ : CoefficientSeries →ₐ[ℂ] ℂ) (hφ : Continuous φ) :
    BoundedSequence := ⟨fun j => φ (coordinate j), bounded_coordinateValues φ hφ⟩

@[simp] theorem characterCoordinates_apply (φ : CoefficientSeries →ₐ[ℂ] ℂ)
    (hφ : Continuous φ) (j : ℕ) :
    (characterCoordinates φ hφ).val j = φ (coordinate j) := rfl

/-- Distinct bounded sequences define distinct evaluations. -/
theorem evaluationHom_injective : Function.Injective evaluationHom := by
  intro w v h
  apply Subtype.ext
  funext j
  have hj := congrArg (fun φ : CoefficientSeries →ₐ[ℂ] ℂ => φ (coordinate j)) h
  simpa using hj

/-- A continuous character agrees everywhere with evaluation at its coordinate values. -/
theorem continuous_character_eq_evaluation (φ : CoefficientSeries →ₐ[ℂ] ℂ)
    (hφ : Continuous φ) : φ = evaluationHom (characterCoordinates φ hφ) := by
  have hp : φ.comp polynomialHom =
      (evaluationHom (characterCoordinates φ hφ)).comp polynomialHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simp only [AlgHom.comp_apply, polynomialHom_X, evaluationHom_apply,
      evaluate_coordinate, characterCoordinates_apply]
  have heq : (φ : CoefficientSeries → ℂ) = evaluationHom (characterCoordinates φ hφ) := by
    apply polynomialHom_denseRange.equalizer hφ (continuous_evaluationHom _)
    funext p
    exact DFunLike.congr_fun hp p
  exact DFunLike.ext' heq

/-- Lemma `lem:characters`: continuous characters are exactly the evaluations at
bounded complex sequences; the evaluating sequence is unique. -/
theorem continuous_character_iff_evaluation (φ : CoefficientSeries →ₐ[ℂ] ℂ) :
    Continuous φ ↔ ∃! w : BoundedSequence, φ = evaluationHom w := by
  constructor
  · intro hφ
    refine ⟨characterCoordinates φ hφ, continuous_character_eq_evaluation φ hφ, ?_⟩
    intro v hv
    exact evaluationHom_injective (hv.symm.trans (continuous_character_eq_evaluation φ hφ))
  · rintro ⟨w, rfl, _⟩
    exact continuous_evaluationHom w

/-- The same classification using the nonzero multiplicative linear functional
notion of `Character` in the statement of Theorem A. -/
theorem continuous_Character_iff_evaluation (χ : Character CoefficientSeries) :
    Continuous χ.val ↔ ∃! w : BoundedSequence, χ.toAlgHom = evaluationHom w :=
  continuous_character_iff_evaluation χ.toAlgHom

end CoefficientSeries
end AutomaticContinuity

import AutomaticContinuity.Characters
import AutomaticContinuity.BoundedSequence
import AutomaticContinuity.Evaluation
import AutomaticContinuity.CoefficientTopology
import AutomaticContinuity.ContinuousCharacters

/-!
# Named proof interfaces for Theorem A

Each capitalised `...Statement` below names a proposition without asserting it.
Universal substitution is proved in `Substitution.lean` and connected to its
named proposition in `RemainingInputs.lean`. Arens interpolation is proved in
`Arens.lean`. The escape pair still depends on the finite flag construction.
No axiom or admitted theorem is introduced.
-/

namespace AutomaticContinuity

open CoefficientSeries

universe u

/-- The exact Arens consequence needed here, restricted to this coefficient algebra.
It matches one finite tuple by one continuous character; it does not require
the original algebraic character to be continuous. -/
def ArensInterpolationStatement : Prop :=
  ∀ (φ : CoefficientSeries →ₐ[ℂ] ℂ) (s : Finset CoefficientSeries),
    ∃ η : CoefficientSeries →ₐ[ℂ] ℂ,
      Continuous η ∧ ∀ f ∈ s, η f = φ f

/-- The Arens finite-interpolation consequence after identifying continuous
characters with evaluations. The character `φ` is purely algebraic. -/
def FiniteInterpolationStatement : Prop :=
  ∀ (φ : CoefficientSeries →ₐ[ℂ] ℂ) (s : Finset CoefficientSeries),
    ∃ w : BoundedSequence, ∀ f ∈ s, evaluate w f = φ f

/-- One fixed pair in the actual coefficient algebra escapes on every tail set. -/
def EscapePairStatement : Prop :=
  ∃ f g : CoefficientSeries,
    IsEscapeMap (fun w => (evaluate w f, evaluate w g))

/-- The complete, possibly nonmetrizable substitution specification, proved by
`universalSubstitution` in `RemainingInputs.lean`. The supplied sequence is
bounded in the original target algebra's topology. -/
def UniversalSubstitutionStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra ℂ A]
    [UniformSpace A] [IsUniformAddGroup A] [T2Space A] [CompleteSpace A],
    IsLocallyMultiplicativelyConvex A →
    ∀ x : ℕ → A, Bornology.IsVonNBounded ℂ (Set.range x) →
      ∃ T : CoefficientSeries →ₐ[ℂ] A,
        Continuous T ∧ ∀ j : ℕ, T (coordinate j) = x j

/-- The proved classification of continuous characters converts Arens
interpolation into the evaluation formulation. `Arens.lean` supplies this input. -/
theorem finiteInterpolation_of_arens (hArens : ArensInterpolationStatement) :
    FiniteInterpolationStatement := by
  intro φ s
  obtain ⟨η, hη, hmatch⟩ := hArens φ s
  refine ⟨characterCoordinates η hη, ?_⟩
  intro f hf
  rw [← evaluationHom_apply, ← continuous_character_eq_evaluation η hη]
  exact hmatch f hf

/-- The elementary contradiction once the two named analytic inputs are given.
This declaration is conditional and must not be reported as Theorem A. -/
theorem no_prescribed_character_of_interpolation_and_escape
    (hInterpolation : FiniteInterpolationStatement) (hEscape : EscapePairStatement)
    (φ : CoefficientSeries →ₐ[ℂ] ℂ)
    (hφ : ∀ j : ℕ, φ (coordinate j) = prescribedCoordinate j) : False := by
  classical
  obtain ⟨f, g, hEscape⟩ := hEscape
  apply escape_incompatible_with_interpolation hEscape (φ f, φ g)
  intro k
  let s : Finset CoefficientSeries := (Finset.range k).image coordinate ∪ {f, g}
  obtain ⟨w, hw⟩ := hInterpolation φ s
  refine ⟨w, ?_, ?_⟩
  · intro j hj
    have hjmem : coordinate j ∈ s := by
      apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩
    simpa using (evaluate_coordinate w j).symm.trans ((hw _ hjmem).trans (hφ j))
  · apply Prod.ext
    · exact hw f (by simp [s])
    · exact hw g (by simp [s])

end AutomaticContinuity

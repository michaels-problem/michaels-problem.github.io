import AutomaticContinuity.ProofObligations
import AutomaticContinuity.UnitizationReduction

/-!
# Conditional assembly, with all unresolved inputs exposed

The declarations here are logical reductions. Their mathematical dependencies
are explicit; `RemainingInputs.lean` discharges substitution and records the
remaining analytic boundary. They are not unconditional proofs of Theorem A.
-/

namespace AutomaticContinuity

open CoefficientSeries

universe u

/-- Combine substitution, finite interpolation, and the escape pair in the
unital case. The three inputs must still be supplied by genuine proofs. -/
theorem unitalBoundedness_of_three_inputs
    (hSubstitution : UniversalSubstitutionStatement.{u})
    (hInterpolation : FiniteInterpolationStatement)
    (hEscape : EscapePairStatement) : UnitalBoundednessStatement.{u} := by
  intro A _ _ _ _ _ _ hA χ
  by_contra hχ
  obtain ⟨x, hx, hvalues⟩ := exists_bounded_sequence_of_unbounded_character hA χ hχ
  obtain ⟨T, _, hT⟩ := hSubstitution A hA x hx
  apply no_prescribed_character_of_interpolation_and_escape hInterpolation hEscape
    (χ.toAlgHom.comp T)
  intro j
  simpa [AlgHom.comp_apply, hT, prescribedCoordinate] using hvalues j

/-- Conditional theorem wiring only: the full reviewed nonunital statement
follows from the three explicit unresolved inputs. -/
theorem theoremA_of_three_inputs
    (hSubstitution : UniversalSubstitutionStatement.{u})
    (hArens : ArensInterpolationStatement)
    (hEscape : EscapePairStatement) : TheoremAStatement.{u} :=
  theoremA_of_unitalBoundedness
    (unitalBoundedness_of_three_inputs hSubstitution (finiteInterpolation_of_arens hArens) hEscape)

end AutomaticContinuity

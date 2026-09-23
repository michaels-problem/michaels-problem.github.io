import AutomaticContinuity.ConditionalAssembly
import AutomaticContinuity.AnalyticBridge
import AutomaticContinuity.StageStep
import AutomaticContinuity.Substitution
import AutomaticContinuity.Arens
import AutomaticContinuity.TaylorStageRepresentation
import AutomaticContinuity.FlagUnitExtension

/-!
# Exact remaining proof boundary

Universal substitution, Arens interpolation, and the finite-dimensional
Taylor/Cauchy bridge are now proved. Theorem A is reduced to flag approximation.
The original three-input implication is retained as an explicit proof interface.
-/

namespace AutomaticContinuity

universe u

/-- The full substitution obligation is discharged by the constructed extension. -/
theorem universalSubstitution : UniversalSubstitutionStatement.{u} := by
  intro A _ _ _ _ _ _ hA x hx
  exact PolynomialSubstitution.exists_substitution hA x hx

/-- A checked dependency map, not a completed proof of Theorem A.

This original interface retains all three analytic hypotheses. Arens
interpolation and the finite-dimensional Taylor/Cauchy bridge are now discharged
below; specialised flag approximation remains unproved. -/
theorem theoremA_of_remaining_analytic_inputs
    (hArens : ArensInterpolationStatement)
    (hFlagApproximation : FiniteFlagApproximationStatement)
    (hRepresentation : CoefficientStageRepresentationStatement) : TheoremAStatement.{u} :=
  theoremA_of_three_inputs universalSubstitution hArens
    (escapePair_of_finiteStages_and_representation
      (finiteStageConstruction_of_approximation hFlagApproximation) hRepresentation)

/-- The intermediate two-input interface, retained for inspection. -/
theorem theoremA_of_flag_approximation_and_representation
    (hFlagApproximation : FiniteFlagApproximationStatement)
    (hRepresentation : CoefficientStageRepresentationStatement) : TheoremAStatement.{u} :=
  theoremA_of_remaining_analytic_inputs arensInterpolation hFlagApproximation hRepresentation

/-- The current exact proof boundary: only specialised flag approximation is
assumed. This does not prove that remaining analytic input or Theorem A. -/
theorem theoremA_of_flag_approximation
    (hFlagApproximation : FiniteFlagApproximationStatement) : TheoremAStatement.{u} :=
  theoremA_of_flag_approximation_and_representation hFlagApproximation
    coefficientStageRepresentation

/-- A direct finite-stage construction would also finish Theorem A, without
proving the more general flag approximation statement. -/
theorem theoremA_of_finite_stage_construction
    (hStages : FiniteStageConstructionStatement) : TheoremAStatement.{u} :=
  theoremA_of_three_inputs universalSubstitution arensInterpolation
    (escapePair_of_finiteStages_and_representation hStages coefficientStageRepresentation)

/-- It suffices to enlarge the holomorphic region of an admissible continuous
section across one compact polydisc at a time. The checked exhaustion argument
then supplies the entire flag approximation required above. -/
theorem theoremA_of_local_flag_extension
    (hLocal : FiniteFlagLocalExtensionStatement) : TheoremAStatement.{u} :=
  theoremA_of_flag_approximation (finiteFlagApproximation_of_localExtension hLocal)

/-- Unit-radius compact enlargement alone suffices. It remains an explicit
unproved geometric premise, equivalent to the flag approximation input. -/
theorem theoremA_of_unit_flag_extension
    (hUnit : FiniteFlagUnitExtensionStatement) : TheoremAStatement.{u} :=
  theoremA_of_flag_approximation (finiteFlagUnitExtension_iff_approximation.mp hUnit)

end AutomaticContinuity

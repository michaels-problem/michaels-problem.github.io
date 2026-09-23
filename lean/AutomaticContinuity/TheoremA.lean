import AutomaticContinuity.HalfCutAssembly
import AutomaticContinuity.ProductHalfcutOpenness
import AutomaticContinuity.RemainingInputs

set_option autoImplicit false

/-! # Theorem A

The single-cut analytic approximation is now proved. The finite cut chain,
continuous globalization, and exhaustion yield the exact finite flag
approximation theorem. The checked coefficient algebra, Arens interpolation,
substitution and unitization reductions then give the original full target.
No analytical proposition remains as a hypothesis.
-/

namespace AutomaticContinuity

universe u

theorem finiteFlagHalfCutApproximation : FiniteFlagHalfCutApproximationStatement :=
  halfCut_of_product_stability (fun _n j a ha b D C =>
    ProductHalfcutOpenness.exists_local_stability j a ha b D C)

theorem finiteFlagUnitExtension : FiniteFlagUnitExtensionStatement :=
  FiniteFlagCutReduction.unitExtension_of_halfCut finiteFlagHalfCutApproximation

theorem finiteFlagApproximation : FiniteFlagApproximationStatement :=
  FiniteFlagCutReduction.finiteFlagApproximation_of_halfCut finiteFlagHalfCutApproximation

/-- Every algebraic character of a complete Hausdorff commutative complex
locally multiplicatively convex algebra is bounded on bounded sets. The
algebra need not be unital or metrizable; the character has no continuity
assumption. This is exactly the original, unchanged target proposition. -/
theorem theoremA : TheoremAStatement.{u} :=
  theoremA_of_flag_approximation finiteFlagApproximation

end AutomaticContinuity

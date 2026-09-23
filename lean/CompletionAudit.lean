import AutomaticContinuity
import Lean.Util.CollectAxioms

set_option autoImplicit false
set_option pp.universes true

/-!
Completion gate for the original, universe-polymorphic Theorem A statement.
This file deliberately fails until `AutomaticContinuity.theoremA` supplies the
whole statement with no additional mathematical hypotheses.
-/

universe u

example : AutomaticContinuity.TheoremAStatement.{u} :=
  AutomaticContinuity.theoremA

#check @AutomaticContinuity.theoremA
#print axioms AutomaticContinuity.theoremA

/-! The native compilation exit code and this marker are both required by the
completion verifier. The exhaustive project audit is a separate required check. -/
run_cmd do
  let env ← Lean.getEnv
  let name := ``AutomaticContinuity.theoremA
  let some info := env.find? name
    | throwError "Theorem A declaration is missing."
  unless info.isTheorem do
    throwError "Theorem A must be a theorem declaration."
  if info.isUnsafe then
    throwError "Theorem A declaration is unsafe."
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let axioms ← Lean.collectAxioms name
  for axiomName in axioms do
    unless allowed.contains axiomName do
      throwError "Unexpected Theorem A axiom dependency: {axiomName}"
  Lean.logInfo m!"THEOREM_A_COMPLETION_AXIOMS {axioms}"
  Lean.logInfo "THEOREM_A_COMPLETION_AUDIT exactStatement=true universePolymorphic=true unexpected=0 unsafe=0"

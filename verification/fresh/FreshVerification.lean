import AutomaticContinuity
import Audit
import CompletionAudit

set_option autoImplicit false
set_option pp.universes true

/-!
Portable inspection and axiom gates for the original Theorem A.
This module does not by itself rebuild imports or replay their kernel checks.
The external verification driver must record how its imports were built and
invoke the official fresh checker separately. Module and declaration coverage
below is read from Lean's actual environment, not inferred from source text.
-/

#print AutomaticContinuity.Character
#print AutomaticContinuity.IsSubmultiplicative
#print AutomaticContinuity.IsLocallyMultiplicativelyConvex
#print AutomaticContinuity.BoundedOnBoundedSets
#print AutomaticContinuity.TheoremAStatement
#check @AutomaticContinuity.theoremA
#print AutomaticContinuity.theoremA
#print axioms AutomaticContinuity.theoremA

universe u

/-- A new kernel-checked witness of the original statement at an arbitrary universe. -/
theorem FreshVerification.exactTheoremA : AutomaticContinuity.TheoremAStatement.{u} :=
  AutomaticContinuity.theoremA

#check @FreshVerification.exactTheoremA
#print axioms FreshVerification.exactTheoremA

run_cmd do
  let env ← Lean.getEnv
  let allowed : Array Lean.Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let target := ``AutomaticContinuity.theoremA
  let some targetInfo := env.find? target
    | throwError "The original Theorem A declaration is missing."
  unless targetInfo.isTheorem && !targetInfo.isUnsafe && !targetInfo.isPartial do
    throwError "The original target must be a safe, nonpartial theorem."
  match targetInfo.levelParams, targetInfo.type with
  | [levelName], .const statementName [.param actualLevel] =>
    unless statementName == ``AutomaticContinuity.TheoremAStatement &&
        actualLevel == levelName do
      throwError "The original target does not have the exact original statement."
  | _, _ => throwError "The original target has extra arguments or changed universe parameters."
  let targetAxioms ← Lean.collectAxioms target
  for axiomName in targetAxioms do
    unless allowed.contains axiomName do
      throwError "Unexpected target axiom: {axiomName}"
  let witnessAxioms ← Lean.collectAxioms ``FreshVerification.exactTheoremA
  for axiomName in witnessAxioms do
    unless allowed.contains axiomName do
      throwError "Unexpected witness axiom: {axiomName}"
  Lean.logInfo m!"FRESH_TARGET_AXIOMS {targetAxioms}"
  Lean.logInfo m!"FRESH_WITNESS_AXIOMS {witnessAxioms}"
  Lean.logInfo "FRESH_EXACT_TARGET exactStatement=true universePolymorphic=true extraArguments=0 unsafe=0 partial=0 unexpectedAxioms=0"

  -- Count columns: all, theorems, safe/nonpartial, unsafe, partial.
  -- Unsafe and partial columns are independent; safe/nonpartial is their complement.
  let increment := fun (row : Array Nat) (info : Lean.ConstantInfo) =>
    #[row[0]! + 1, row[1]! + (if info.isTheorem then 1 else 0),
      row[2]! + (if !info.isUnsafe && !info.isPartial then 1 else 0),
      row[3]! + (if info.isUnsafe then 1 else 0),
      row[4]! + (if info.isPartial then 1 else 0)]
  let countsJson := fun (row : Array Nat) => Lean.Json.mkObj
    [("declarations", Lean.toJson row[0]!), ("theorems", Lean.toJson row[1]!),
      ("safeNonpartial", Lean.toJson row[2]!), ("unsafe", Lean.toJson row[3]!),
      ("partial", Lean.toJson row[4]!)]
  let emptyRow : Array Nat := #[0, 0, 0, 0, 0]
  let mut moduleCounts := Array.replicate env.header.modules.size emptyRow
  let mut totalCounts := emptyRow
  let mut localCounts := emptyRow
  let mut projectCounts := emptyRow
  let mut projectAxioms : Array Lean.Name := #[]
  for (name, info) in env.constants.toList do
    totalCounts := increment totalCounts info
    match env.getModuleIdxFor? name with
    | some idx =>
      unless idx.toNat < env.header.modules.size do
        throwError "Declaration has an invalid owning module index: {name}"
      moduleCounts := moduleCounts.modify idx.toNat (fun row => increment row info)
      let owner := env.header.modules[idx]!.module
      if (`AutomaticContinuity).isPrefixOf owner then
        projectCounts := increment projectCounts info
        if info.isUnsafe then
          throwError "Unsafe project declaration: {name}"
        if info.isUnsafe || info.isPartial then
          let record := Lean.Json.mkObj [("name", Lean.toJson name.toString),
            ("module", Lean.toJson owner.toString),
            ("isUnsafe", Lean.toJson info.isUnsafe),
            ("isPartial", Lean.toJson info.isPartial)]
          Lean.logInfo m!"FRESH_PROJECT_CHECKER_SKIPPED {record.compress}"
        let axioms ← Lean.collectAxioms name
        for axiomName in axioms do
          unless allowed.contains axiomName do
            throwError "Unexpected project axiom: {name} uses {axiomName}"
          unless projectAxioms.contains axiomName do
            projectAxioms := projectAxioms.push axiomName
    | none =>
      localCounts := increment localCounts info
      let record := Lean.Json.mkObj [("name", Lean.toJson name.toString),
        ("isTheorem", Lean.toJson info.isTheorem),
        ("isUnsafe", Lean.toJson info.isUnsafe),
        ("isPartial", Lean.toJson info.isPartial)]
      Lean.logInfo m!"FRESH_LOCAL_DECLARATION {record.compress}"
  for idx in [:env.header.modules.size] do
    let imp := env.header.modules[idx]!
    let record := Lean.Json.mkObj [("index", Lean.toJson idx),
      ("module", Lean.toJson imp.module.toString),
      ("hasData", Lean.toJson imp.hasData),
      ("importAll", Lean.toJson imp.importAll),
      ("isExported", Lean.toJson imp.isExported),
      ("isMeta", Lean.toJson imp.isMeta),
      ("irPhases", Lean.toJson (reprStr imp.irPhases)),
      ("counts", countsJson moduleCounts[idx]!)]
    Lean.logInfo m!"FRESH_MODULE {record.compress}"
  let summary := Lean.Json.mkObj
    [("mainModule", Lean.toJson env.header.mainModule.toString),
      ("trustLevel", Lean.toJson env.header.trustLevel.toNat),
      ("effectiveImports", Lean.toJson env.header.modules.size),
      ("wholeEnvironment", countsJson totalCounts),
      ("currentModule", countsJson localCounts),
      ("project", countsJson projectCounts)]
  Lean.logInfo m!"FRESH_ENVIRONMENT_SUMMARY {summary.compress}"
  Lean.logInfo m!"FRESH_PROJECT_AXIOM_UNION {projectAxioms}"
  Lean.logInfo "FRESH_AUDIT_GATES_PASS exactTarget=true projectUnexpectedAxioms=0 projectUnsafe=0 targetUnsafe=0 targetPartial=0"

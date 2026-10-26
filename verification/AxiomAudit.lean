import Erdos1186

/-!
Axiom audit of EVERY declaration in the 342 project modules (`Erdos.Proofs.*`), not only the headline theorems.

For each module of the environment whose name starts with `Erdos.Proofs`, every constant whose home module it is
is passed to Lean's own axiom collector (`Lean.CollectAxioms.collect`, the function behind `#print axioms`), which
walks the full dependency graph (through Mathlib) and records every axiom it reaches. The walk is made once, with
one shared state for all constants, so the recorded set is the UNION of the axiom sets of all constants: every
constant uses only standard axioms if and only if this union is contained in {`propext`, `Classical.choice`,
`Quot.sound`}. (A shared walk visits each constant of the graph once; one walk per constant would traverse
Mathlib again for each of the tens of thousands of generated declarations.) If the union contains anything else,
the audit runs `collectAxioms` on every constant separately and names each offender.

The audit fails if
* the number of project modules is not 342,
* any constant uses an axiom outside the three standard ones: this catches `sorryAx` (an unfinished proof),
  `Lean.ofReduceBool` / `Lean.trustCompiler` (`native_decide`, `decide +native`), and any added axiom, or
* any project module declares an `axiom`.
Run from `lean/`:  lake env lean ../verification/AxiomAudit.lean
-/

open Lean Elab Command

def expectedModules : Nat := 342

def standardAxioms : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]

#eval show CommandElabM Unit from do
  let env ← getEnv
  let mut mods : Array (Name × Nat) := #[]
  for i in [0:env.header.moduleNames.size] do
    let m := env.header.moduleNames[i]!
    if (`Erdos.Proofs).isPrefixOf m then mods := mods.push (m, i)
  let mut names : Array Name := #[]
  let mut nThm := 0
  let mut axiomDecls : Array Name := #[]
  for (_, i) in mods do
    for ci in env.header.moduleData[i]!.constants do
      names := names.push ci.name
      if ci matches .axiomInfo _ then axiomDecls := axiomDecls.push ci.name
      if ci matches .thmInfo _ then nThm := nThm + 1
  logInfo m!"TOTAL: {names.size} constants ({nThm} theorems) in {mods.size} modules"
  -- one walk, shared state: the union of the axioms of all constants
  let (_, st) := ((names.forM CollectAxioms.collect).run env).run {}
  let usedList := st.axioms.toList.map toString
  logInfo m!"axioms used by any of them: {usedList}"
  logInfo m!"constants visited in the dependency walk (project and Mathlib): {st.visited.toList.length}"
  logInfo m!"axiom declarations inside the project modules: {axiomDecls.size}"
  let nonstandard := st.axioms.filter (fun a => !standardAxioms.contains a)
  if mods.size == expectedModules && nonstandard.isEmpty && axiomDecls.isEmpty then
    logInfo m!"AXIOM AUDIT PASSED: every constant of the {mods.size} modules depends only on propext, Classical.choice, Quot.sound"
  else
    if mods.size != expectedModules then
      logError m!"expected {expectedModules} project modules, found {mods.size}"
    for n in axiomDecls do
      logError m!"axiom declared in a project module: {n}"
    if !nonstandard.isEmpty then
      for n in names do
        let axs ← collectAxioms n
        if axs.any (fun a => !standardAxioms.contains a) then
          logError m!"non-standard axioms in {n}: {axs}"
    throwError "AXIOM AUDIT FAILED"

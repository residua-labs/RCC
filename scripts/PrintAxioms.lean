import Lean
import Std.Data.HashMap
import RCC
open Lean

/-- Collects, for every theorem declared in an `RCC.*` module, the set of axioms it
depends on, and prints: a count per exact axiom set, the theorems that use
`Classical.choice`, any theorem that depends on an axiom outside Lean's standard
three (`propext`, `Quot.sound`, `Classical.choice`), and one
`name / axiom set / module` row per theorem. The full output is shipped as
`self-closure/axiom_census.txt`. -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `RCC }] {} 0
  let mut counts : Std.HashMap String Nat := {}
  let mut choiceRows : Array String := #[]
  let mut odd : Array String := #[]
  let mut rows : Array String := #[]
  let mut total := 0
  for (n, ci) in env.constants.toList do
    let some idx := env.getModuleIdxFor? n | continue
    let modName := env.header.moduleNames[idx.toNat]!
    unless (`RCC).isPrefixOf modName do continue
    unless ci matches .thmInfo _ do continue
    if n.isInternal then continue
    total := total + 1
    let (_, s) := ((CollectAxioms.collect n).run env).run {}
    let axs := s.axioms.toList.map toString |>.toArray.qsort (· < ·)
    let key := if axs.isEmpty then "(none)" else ", ".intercalate axs.toList
    counts := counts.insert key (counts.getD key 0 + 1)
    if axs.contains "Classical.choice" then
      choiceRows := choiceRows.push s!"{n}\t{key}\t{modName}"
    for a in axs do
      unless a == "propext" || a == "Quot.sound" || a == "Classical.choice" do
        odd := odd.push s!"{n}: {a}"
    rows := rows.push s!"{n}\t{key}\t{modName}"
  IO.println s!"theorems in RCC.*: {total}"
  IO.println ""
  IO.println "axiom set counts (exact sets):"
  for (k, v) in counts.toList do
    IO.println s!"{v}\t{k}"
  IO.println ""
  IO.println s!"theorems that use Classical.choice: {choiceRows.size}"
  for r in choiceRows do IO.println r
  IO.println ""
  IO.println s!"non-standard axiom uses: {odd.size}"
  for o in odd do IO.println o
  IO.println ""
  IO.println "theorem / axiom set / module:"
  for r in rows do IO.println r

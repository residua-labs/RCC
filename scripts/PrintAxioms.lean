import Lean
import Std.Data.HashMap
import RCC
open Lean

/-- Collects, for every theorem declared in an `RCC.*` module, the set of axioms it
depends on, and prints a count per axiom set plus any theorem that depends on an
axiom outside Lean's standard three (`propext`, `Quot.sound`, `Classical.choice`). -/
def main : IO Unit := do
  initSearchPath (← findSysroot)
  let env ← importModules #[{ module := `RCC }] {} 0
  let mut counts : Std.HashMap String Nat := {}
  let mut odd : Array String := #[]
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
    for a in axs do
      unless a == "propext" || a == "Quot.sound" || a == "Classical.choice" do
        odd := odd.push s!"{n}: {a}"
  IO.println s!"theorems in RCC.*: {total}"
  for (k, v) in counts.toList do
    IO.println s!"{v}\t{k}"
  IO.println s!"non-standard axiom uses: {odd.size}"
  for o in odd do IO.println o

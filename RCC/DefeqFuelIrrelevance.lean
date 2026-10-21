import RCC.DefeqSemanticPreservation

/-!
# RCC defeq fuel irrelevance above the structural bound

This file establishes DQ-4 for the recursively closed `num`/`add` fragment.
It proves that the production `evalLF` result is independent of the selected
fuel once both selections meet the DQ-3 structural bound.

The statement is universal over:

* every proof-carrying supported term;
* every environment and program table;
* any two fuel values above the mechanically derived `requiredFuel`.

No default fuel, finite corpus, hidden runtime budget, or monotonicity
assumption enters the theorem.  The proof factors both executions through the
same DQ-2 normal form using DQ-3 semantic preservation.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.DefeqFuelIrrelevance

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqSemanticPreservation

/-! ## Universal DQ-4 theorem -/

/-- DQ-4: any two production evaluations of a supported term agree once
both fuels meet the structurally derived bound.  Environment and program
table are held fixed only because they are arguments of the production
evaluator; DQ-3 proves that this fragment does not inspect either one. -/
theorem evalLF_fuel_irrelevant_above_required
    (term : NumAddTerm)
    (env : Env)
    (progs : Progs)
    (fuel₁ fuel₂ : Nat)
    (fuel₁Enough : requiredFuel term.1 ≤ fuel₁)
    (fuel₂Enough : requiredFuel term.1 ≤ fuel₂) :
    evalLF fuel₁ term.1 env progs =
      evalLF fuel₂ term.1 env progs := by
  rw [evalLF_normalize_semantics term env progs fuel₁ fuel₁Enough]
  rw [evalLF_normalize_semantics term env progs fuel₂ fuel₂Enough]

/-- Every sufficient-fuel execution equals the execution at the exact
structural bound.  This exposes the canonical representative without
introducing a repository-wide default fuel. -/
theorem evalLF_eq_at_requiredFuel
    (term : NumAddTerm)
    (env : Env)
    (progs : Progs)
    (fuel : Nat)
    (enough : requiredFuel term.1 ≤ fuel) :
    evalLF fuel term.1 env progs =
      evalLF (requiredFuel term.1) term.1 env progs := by
  exact
    evalLF_fuel_irrelevant_above_required
      term env progs fuel (requiredFuel term.1)
      enough (Nat.le_refl _)

/-- Arbitrarily large additive fuel extensions preserve the production
result.  This theorem quantifies over both extensions rather than checking a
fixed pair of large constants. -/
theorem evalLF_arbitrary_excess_fuel
    (term : NumAddTerm)
    (env : Env)
    (progs : Progs)
    (extra₁ extra₂ : Nat) :
    evalLF (requiredFuel term.1 + extra₁) term.1 env progs =
      evalLF (requiredFuel term.1 + extra₂) term.1 env progs := by
  exact
    evalLF_fuel_irrelevant_above_required
      term env progs
      (requiredFuel term.1 + extra₁)
      (requiredFuel term.1 + extra₂)
      (Nat.le_add_right _ _)
      (Nat.le_add_right _ _)

end Residua.RCC.DefeqFuelIrrelevance

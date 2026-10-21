import RCC.DefeqNormalizer

/-!
# RCC defeq universal semantic preservation

This file establishes DQ-3 for the recursively closed `num`/`add` fragment.
It connects the total DQ-2 normalizer to the production, fuel-bounded
`evalLF` authority.

The theorem is universal over:

* every proof-carrying supported term;
* every runtime environment and program table;
* every fuel value at or above a structurally derived bound.

No default fuel, finite example corpus, or candidate-specific witness enters
the statement.
-/

namespace Residua.RCC.DefeqSemanticPreservation

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer

/-! ## Normal-form semantics -/

/-- Interpret the canonical DQ-2 normal form in the production value
universe.  This is the semantic bridge used by DQ-3; the normal form is not
identified with its encoding or with a future digest. -/
def evalNormalForm : NumAddNormalForm → Val
  | .int value => .int value

@[simp]
theorem evalNormalForm_int (value : Int) :
    evalNormalForm (.int value) = .int value := by
  rfl

/-! ## Structurally derived fuel bound -/

/-- The evaluation depth needed by the `num`/`add` fragment.  The definition
is intentionally explicit over the full production `Term` surface so a new
constructor cannot be hidden by a catch-all.  DQ-3 assigns semantic meaning
to this number only under an `InNumAddFragment` proof. -/
def requiredFuel : Term → Nat
  | .num _ =>
      1
  | .var _ =>
      1
  | .add left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .sub left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .mul left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .div left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .ifE cond thenBranch elseBranch =>
      Nat.succ
        (Nat.max (requiredFuel cond)
          (Nat.max (requiredFuel thenBranch) (requiredFuel elseBranch)))
  | .neg term =>
      Nat.succ (requiredFuel term)
  | .lt left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .eq left right =>
      Nat.succ (Nat.max (requiredFuel left) (requiredFuel right))
  | .let_ _ value body =>
      Nat.succ (Nat.max (requiredFuel value) (requiredFuel body))
  | .call _ argument =>
      Nat.succ (requiredFuel argument)

/-! ## Universal preservation -/

private theorem evalLF_normalizeProof
    {term : Term}
    (supported : InNumAddFragment term)
    (env : Env)
    (progs : Progs) :
    ∀ fuel,
      requiredFuel term ≤ fuel →
      evalLF fuel term env progs =
        some (.int (normalizeProof term supported).value) := by
  induction supported with
  | num value =>
      intro fuel enough
      cases fuel with
      | zero =>
          exact False.elim ((Nat.not_succ_le_zero 0) enough)
      | succ remaining =>
          rfl
  | @add left right leftSupported rightSupported leftIH rightIH =>
      intro fuel enough
      cases fuel with
      | zero =>
          exact False.elim
            ((Nat.not_succ_le_zero
              (Nat.max (requiredFuel left) (requiredFuel right))) enough)
      | succ remaining =>
          have maxEnough :
              Nat.max (requiredFuel left) (requiredFuel right) ≤ remaining :=
            Nat.le_of_succ_le_succ enough
          have leftEnough : requiredFuel left ≤ remaining :=
            Nat.le_trans
              (Nat.le_max_left (requiredFuel left) (requiredFuel right))
              maxEnough
          have rightEnough : requiredFuel right ≤ remaining :=
            Nat.le_trans
              (Nat.le_max_right (requiredFuel left) (requiredFuel right))
              maxEnough
          simp only [evalLF]
          rw [leftIH remaining leftEnough]
          rw [rightIH remaining rightEnough]
          rfl

/-- DQ-3: evaluating any supported `num`/`add` term with sufficient fuel
produces exactly the integer represented by its canonical DQ-2 normal form.
The result is independent of environment and program-table contents because
the supported fragment contains neither variables nor calls. -/
theorem evalLF_normalize_semantics
    (term : NumAddTerm)
    (env : Env)
    (progs : Progs)
    (fuel : Nat)
    (enough : requiredFuel term.1 ≤ fuel) :
    evalLF fuel term.1 env progs =
      some (evalNormalForm (normalize term)) := by
  exact evalLF_normalizeProof term.property env progs fuel enough

/-- At the exact structural bound, evaluation and normalization already
agree.  This is a corollary of the universal theorem, not a finite fixture. -/
theorem evalLF_at_requiredFuel
    (term : NumAddTerm)
    (env : Env)
    (progs : Progs) :
    evalLF (requiredFuel term.1) term.1 env progs =
      some (evalNormalForm (normalize term)) := by
  exact
    evalLF_normalize_semantics term env progs (requiredFuel term.1)
      (Nat.le_refl _)

end Residua.RCC.DefeqSemanticPreservation

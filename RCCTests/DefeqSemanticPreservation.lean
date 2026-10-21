import RCC.DefeqSemanticPreservation

/-!
# Tests and load-bearing mutants for DQ-3

The universal theorem is exercised at arbitrary excess fuel.  Two mutants
show why both arithmetic fidelity and recursive branch coverage are
load-bearing:

* subtraction substituted for addition;
* the recursive right branch silently omitted.
-/

namespace Residua.RCC.DefeqSemanticPreservation.Tests

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqSemanticPreservation

def nestedTerm : NumAddTerm :=
  ⟨ .add (.num 4) (.add (.num 5) (.num 6))
  , .add (.num 4) (.add (.num 5) (.num 6))
  ⟩

def arbitraryEnv : Env :=
  fun name => if name = "unused" then some (.bool true) else none

def arbitraryProgs : Progs :=
  fun name =>
    if name = "unused" then some (["x"], .var "x") else none

example (extra : Nat) :
    evalLF (requiredFuel nestedTerm.1 + extra) nestedTerm.1
        arbitraryEnv arbitraryProgs =
      some (.int (normalize nestedTerm).value) := by
  apply evalLF_normalize_semantics
  exact Nat.le_add_right _ _

/-! ## Mutant 1: addition is normalized as subtraction -/

def wrongAddProof :
    (term : Term) → InNumAddFragment term → NumAddNormalForm
  | .num value, _ =>
      .int value
  | .add left right, supported =>
      .int
        ((wrongAddProof left (by
          cases supported with
          | add leftSupported _ => exact leftSupported)).value -
         (wrongAddProof right (by
          cases supported with
          | add _ rightSupported => exact rightSupported)).value)
  | .var _, supported =>
      False.elim (by cases supported)
  | .sub _ _, supported =>
      False.elim (by cases supported)
  | .mul _ _, supported =>
      False.elim (by cases supported)
  | .div _ _, supported =>
      False.elim (by cases supported)
  | .ifE _ _ _, supported =>
      False.elim (by cases supported)
  | .neg _, supported =>
      False.elim (by cases supported)
  | .lt _ _, supported =>
      False.elim (by cases supported)
  | .eq _ _, supported =>
      False.elim (by cases supported)
  | .let_ _ _ _, supported =>
      False.elim (by cases supported)
  | .call _ _, supported =>
      False.elim (by cases supported)

def wrongAddNormalizer (term : NumAddTerm) : NumAddNormalForm :=
  wrongAddProof term.1 term.property

def addWitness : NumAddTerm :=
  ⟨.add (.num 7) (.num 2), .add (.num 7) (.num 2)⟩

theorem wrong_add_mutant_exposed :
    wrongAddNormalizer addWitness = .int 5 ∧
    evalLF (requiredFuel addWitness.1) addWitness.1
        arbitraryEnv arbitraryProgs =
      some (.int 9) ∧
    evalLF (requiredFuel addWitness.1) addWitness.1
        arbitraryEnv arbitraryProgs ≠
      some (.int (wrongAddNormalizer addWitness).value) := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro impossible
      cases impossible

/-! ## Mutant 2: the recursive right branch is omitted -/

def omitRightProof :
    (term : Term) → InNumAddFragment term → NumAddNormalForm
  | .num value, _ =>
      .int value
  | .add left _, supported =>
      omitRightProof left (by
        cases supported with
        | add leftSupported _ => exact leftSupported)
  | .var _, supported =>
      False.elim (by cases supported)
  | .sub _ _, supported =>
      False.elim (by cases supported)
  | .mul _ _, supported =>
      False.elim (by cases supported)
  | .div _ _, supported =>
      False.elim (by cases supported)
  | .ifE _ _ _, supported =>
      False.elim (by cases supported)
  | .neg _, supported =>
      False.elim (by cases supported)
  | .lt _ _, supported =>
      False.elim (by cases supported)
  | .eq _ _, supported =>
      False.elim (by cases supported)
  | .let_ _ _ _, supported =>
      False.elim (by cases supported)
  | .call _ _, supported =>
      False.elim (by cases supported)

def omitRightNormalizer (term : NumAddTerm) : NumAddNormalForm :=
  omitRightProof term.1 term.property

theorem recursive_branch_omission_mutant_exposed :
    omitRightNormalizer nestedTerm = .int 4 ∧
    evalLF (requiredFuel nestedTerm.1) nestedTerm.1
        arbitraryEnv arbitraryProgs =
      some (.int 15) ∧
    evalLF (requiredFuel nestedTerm.1) nestedTerm.1
        arbitraryEnv arbitraryProgs ≠
      some (.int (omitRightNormalizer nestedTerm).value) := by
  constructor
  · rfl
  · constructor
    · rfl
    · intro impossible
      cases impossible

#print axioms evalLF_normalize_semantics
#print axioms evalLF_at_requiredFuel
#print axioms wrong_add_mutant_exposed
#print axioms recursive_branch_omission_mutant_exposed

end Residua.RCC.DefeqSemanticPreservation.Tests

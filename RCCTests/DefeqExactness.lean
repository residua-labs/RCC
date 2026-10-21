import RCC.DefeqExactness

/-!
# Tests and load-bearing mutants for DQ-5

The positive witnesses exercise exact equality, inequality, relation laws,
normal-form uniqueness, and the production-evaluator bridge.  The mutants
expose the two forbidden shortcuts:

* a raw `Bool` maps both unsupported input and proved inequality to `false`;
* a collapsed normal-form comparator declares semantically distinct terms
  equal.

A further syntax-equality mutant demonstrates the dual false negative:
distinct syntax can have the same canonical normal form.
-/

namespace Residua.RCC.DefeqExactness.Tests

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqSemanticPreservation
open Residua.RCC.DefeqExactness

def oneTerm : NumAddTerm :=
  ⟨.num 1, .num 1⟩

def twoTerm : NumAddTerm :=
  ⟨.num 2, .num 2⟩

def threeTerm : NumAddTerm :=
  ⟨.num 3, .num 3⟩

def onePlusTwoTerm : NumAddTerm :=
  ⟨.add (.num 1) (.num 2), .add (.num 1) (.num 2)⟩

def arbitraryEnv : Env :=
  fun name => if name = "unused" then some (.bool true) else none

def arbitraryProgs : Progs :=
  fun name =>
    if name = "unused" then some (["x"], .var "x") else none

/-! ## Positive exactness witnesses -/

theorem distinct_syntax_same_normal_form :
    onePlusTwoTerm.1 ≠ threeTerm.1 ∧
    normalize onePlusTwoTerm = normalize threeTerm ∧
    DefEq onePlusTwoTerm threeTerm := by
  decide

theorem equal_verdict_witness :
    (decideDefEq onePlusTwoTerm threeTerm).state = .equal := by
  rfl

theorem not_equal_verdict_witness :
    (decideDefEq oneTerm twoTerm).state = .notEqual := by
  rfl

theorem relation_laws_witness :
    DefEq onePlusTwoTerm threeTerm ∧
    DefEq threeTerm onePlusTwoTerm ∧
    DefEq onePlusTwoTerm onePlusTwoTerm := by
  constructor
  · exact (normalize_eq_iff_defeq onePlusTwoTerm threeTerm).mp (by rfl)
  · constructor
    · exact
        defeq_symm
          ((normalize_eq_iff_defeq onePlusTwoTerm threeTerm).mp (by rfl))
    · exact defeq_refl onePlusTwoTerm

theorem unique_normal_form_witness :
    (.int 3 : NumAddNormalForm) = normalize onePlusTwoTerm := by
  apply normal_form_unique (term := onePlusTwoTerm)
  · rfl
  · exact normalize_represents onePlusTwoTerm

theorem production_bridge_witness
    (leftFuel rightFuel : Nat)
    (leftEnough : requiredFuel onePlusTwoTerm.1 ≤ leftFuel)
    (rightEnough : requiredFuel threeTerm.1 ≤ rightFuel) :
    DefEq onePlusTwoTerm threeTerm ↔
      evalLF leftFuel onePlusTwoTerm.1 arbitraryEnv arbitraryProgs =
        evalLF rightFuel threeTerm.1 arbitraryEnv arbitraryProgs := by
  exact
    defeq_iff_evalLF_equal
      onePlusTwoTerm threeTerm arbitraryEnv arbitraryProgs
      leftFuel rightFuel leftEnough rightEnough

/-! ## Unsupported stays outside the verdict type -/

def unsupportedMixed : Term :=
  .add (.num 1) (.var "x")

theorem unsupported_right_is_boundary_not_not_equal :
    decideDefEqAtBoundary (.num 1) unsupportedMixed =
      .unsupported .right
        { path := [.addRight], constructor := .var } := by
  rfl

theorem unsupported_left_is_boundary_not_not_equal :
    decideDefEqAtBoundary (.var "x") (.num 1) =
      .unsupported .left
        { path := [], constructor := .var } := by
  rfl

/-! ## Mutant 1: raw Bool conflates Unsupported with NotEqual -/

/-- The forbidden raw-Bool API.  Both a proved supported inequality and an
unsupported input collapse to `false`, destroying the typed boundary. -/
def rawBoolEqualityMutant (left right : Term) : Bool :=
  match prepareComparison left right with
  | .ready leftSupported rightSupported =>
      match
          (decideDefEq
            ⟨left, leftSupported⟩
            ⟨right, rightSupported⟩).state with
      | .equal    => true
      | .notEqual => false
  | .unsupported _ _ =>
      false

theorem raw_bool_unsupported_not_equal_collapse_exposed :
    rawBoolEqualityMutant oneTerm.1 twoTerm.1 = false ∧
    rawBoolEqualityMutant (.num 1) unsupportedMixed = false ∧
    (decideDefEq oneTerm twoTerm).state = .notEqual ∧
    decideDefEqAtBoundary (.num 1) unsupportedMixed =
      .unsupported .right
        { path := [.addRight], constructor := .var } := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

/-! ## Mutant 2: incorrect normal-form equality -/

/-- A malformed normalizer that collapses every supported term to one normal
form.  Equality over this output is total but not sound. -/
def collapsedNormalForm (_ : NumAddTerm) : NumAddNormalForm :=
  .int 0

def collapsedNormalFormEquality
    (left right : NumAddTerm) : Bool :=
  decide (collapsedNormalForm left = collapsedNormalForm right)

theorem collapsed_normal_form_equality_mutant_exposed :
    collapsedNormalFormEquality oneTerm twoTerm = true ∧
    ¬ DefEq oneTerm twoTerm ∧
    normalize oneTerm ≠ normalize twoTerm := by
  decide

/-! ## Mutant 3: syntax equality used in place of normal-form equality -/

def syntaxEqualityMutant
    (left right : NumAddTerm) : Bool :=
  decide (left.1 = right.1)

theorem syntax_equality_mutant_exposed :
    syntaxEqualityMutant onePlusTwoTerm threeTerm = false ∧
    DefEq onePlusTwoTerm threeTerm ∧
    normalize onePlusTwoTerm = normalize threeTerm := by
  decide

#print axioms evalNormalForm_injective
#print axioms normalize_eq_iff_defeq
#print axioms defeq_equivalence
#print axioms normal_form_unique
#print axioms defeq_iff_evalLF_equal
#print axioms verdict_equal_iff
#print axioms verdict_not_equal_iff
#print axioms boundary_preserves_unsupported
#print axioms raw_bool_unsupported_not_equal_collapse_exposed
#print axioms collapsed_normal_form_equality_mutant_exposed
#print axioms syntax_equality_mutant_exposed

end Residua.RCC.DefeqExactness.Tests

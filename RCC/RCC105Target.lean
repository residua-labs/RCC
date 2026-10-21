import RCCTests.DefeqExactness

/-! RCC-105 candidate: defeq exactness, typed boundaries, and evaluator bridge. -/

namespace Residua.RCC.RCC105Target

open Residua.RCC.DefeqExactness.Tests
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqSemanticPreservation
open Residua.RCC.DefeqExactness

abbrev DistinctSyntaxSameNormalForm : Prop :=
  onePlusTwoTerm.1 ≠ threeTerm.1 ∧
  normalize onePlusTwoTerm = normalize threeTerm ∧
  DefEq onePlusTwoTerm threeTerm

abbrev EqualVerdictWitness : Prop :=
  (decideDefEq onePlusTwoTerm threeTerm).state = .equal

abbrev NotEqualVerdictWitness : Prop :=
  (decideDefEq oneTerm twoTerm).state = .notEqual

abbrev RelationLawsWitness : Prop :=
  DefEq onePlusTwoTerm threeTerm ∧
  DefEq threeTerm onePlusTwoTerm ∧
  DefEq onePlusTwoTerm onePlusTwoTerm

abbrev UniqueNormalFormWitness : Prop :=
  (.int 3 : NumAddNormalForm) = normalize onePlusTwoTerm

abbrev UnsupportedRightBoundary : Prop :=
  decideDefEqAtBoundary (.num 1) unsupportedMixed =
    .unsupported .right
      { path := [.addRight], constructor := .var }

abbrev UnsupportedLeftBoundary : Prop :=
  decideDefEqAtBoundary (.var "x") (.num 1) =
    .unsupported .left
      { path := [], constructor := .var }

abbrev RawBoolCollapseExposed : Prop :=
  rawBoolEqualityMutant oneTerm.1 twoTerm.1 = false ∧
  rawBoolEqualityMutant (.num 1) unsupportedMixed = false ∧
  (decideDefEq oneTerm twoTerm).state = .notEqual ∧
  decideDefEqAtBoundary (.num 1) unsupportedMixed =
    .unsupported .right
      { path := [.addRight], constructor := .var }

abbrev CollapsedNormalFormExposed : Prop :=
  collapsedNormalFormEquality oneTerm twoTerm = true ∧
  ¬ DefEq oneTerm twoTerm ∧
  normalize oneTerm ≠ normalize twoTerm

abbrev SyntaxEqualityExposed : Prop :=
  syntaxEqualityMutant onePlusTwoTerm threeTerm = false ∧
  DefEq onePlusTwoTerm threeTerm ∧
  normalize onePlusTwoTerm = normalize threeTerm

theorem productionBridgeWitness
    (leftFuel rightFuel : Nat)
    (leftEnough : requiredFuel onePlusTwoTerm.1 ≤ leftFuel)
    (rightEnough : requiredFuel threeTerm.1 ≤ rightFuel) :
    DefEq onePlusTwoTerm threeTerm ↔
      evalLF leftFuel onePlusTwoTerm.1 arbitraryEnv arbitraryProgs =
        evalLF rightFuel threeTerm.1 arbitraryEnv arbitraryProgs :=
  production_bridge_witness leftFuel rightFuel leftEnough rightEnough

abbrev ProductionBridgeWitness : Prop :=
  ∀ (leftFuel rightFuel : Nat),
    requiredFuel onePlusTwoTerm.1 ≤ leftFuel →
    requiredFuel threeTerm.1 ≤ rightFuel →
    (DefEq onePlusTwoTerm threeTerm ↔
      evalLF leftFuel onePlusTwoTerm.1 arbitraryEnv arbitraryProgs =
        evalLF rightFuel threeTerm.1 arbitraryEnv arbitraryProgs)

structure Certificate where
  distinctSyntaxSameNormalForm : DistinctSyntaxSameNormalForm
  equalVerdictWitness : EqualVerdictWitness
  notEqualVerdictWitness : NotEqualVerdictWitness
  relationLawsWitness : RelationLawsWitness
  uniqueNormalFormWitness : UniqueNormalFormWitness
  unsupportedRightBoundary : UnsupportedRightBoundary
  unsupportedLeftBoundary : UnsupportedLeftBoundary
  rawBoolCollapseExposed : RawBoolCollapseExposed
  collapsedNormalFormExposed : CollapsedNormalFormExposed
  syntaxEqualityExposed : SyntaxEqualityExposed
  productionBridgeWitness :
    ∀ (leftFuel rightFuel : Nat),
      requiredFuel onePlusTwoTerm.1 ≤ leftFuel →
      requiredFuel threeTerm.1 ≤ rightFuel →
      (DefEq onePlusTwoTerm threeTerm ↔
        evalLF leftFuel onePlusTwoTerm.1 arbitraryEnv arbitraryProgs =
          evalLF rightFuel threeTerm.1 arbitraryEnv arbitraryProgs)

def certificate : Certificate where
  distinctSyntaxSameNormalForm := distinct_syntax_same_normal_form
  equalVerdictWitness := equal_verdict_witness
  notEqualVerdictWitness := not_equal_verdict_witness
  relationLawsWitness := relation_laws_witness
  uniqueNormalFormWitness := unique_normal_form_witness
  unsupportedRightBoundary := unsupported_right_is_boundary_not_not_equal
  unsupportedLeftBoundary := unsupported_left_is_boundary_not_not_equal
  rawBoolCollapseExposed := raw_bool_unsupported_not_equal_collapse_exposed
  collapsedNormalFormExposed := collapsed_normal_form_equality_mutant_exposed
  syntaxEqualityExposed := syntax_equality_mutant_exposed
  productionBridgeWitness := productionBridgeWitness

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC105Target

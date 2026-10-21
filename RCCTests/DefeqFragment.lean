import RCC.DefeqFragment

/-!
# Tests and load-bearing mutants for DQ-1

The mutants make the four intended failure classes executable:

* a permissive fragment-outside fallback;
* mixed nesting hidden under `add`;
* an omitted constructor in the sealed surface;
* direct acceptance of an unsupported constructor.
-/

namespace Residua.RCC.DefeqFragment.Tests

open Residua.RCC.DefeqFragment

def supportedLeaf : Term := .num 7

def supportedNested : Term :=
  .add (.num 1) (.add (.num 2) (.num 3))

def unsupportedLeaf : Term :=
  .var "x"

def unsupportedMixedRight : Term :=
  .add (.num 1) (.var "x")

def unsupportedMixedLeft : Term :=
  .add (.sub (.num 4) (.num 1)) (.num 3)

example : (classifyTerm supportedLeaf).isSupported = true := by
  rfl

example : (classifyTerm supportedNested).isSupported = true := by
  rfl

example : InNumAddFragment supportedNested := by
  exact (classify_supported_iff supportedNested).mp rfl

example : (classifyTerm unsupportedLeaf).isSupported = false := by
  rfl

example : ¬ InNumAddFragment unsupportedLeaf := by
  exact (classify_unsupported_iff unsupportedLeaf).mp rfl

/-! ## Mutant 1: fragment-outside fallback collapse -/

/-- A bad classifier that treats every unsupported root as a successful
fallback value. -/
def fallbackCollapseMutant : Term → Bool
  | .num _       => true
  | .add left right =>
      fallbackCollapseMutant left && fallbackCollapseMutant right
  | _            => true

theorem fallback_collapse_mutant_exposed :
    fallbackCollapseMutant unsupportedLeaf = true ∧
    (classifyTerm unsupportedLeaf).isSupported = false := by
  decide

/-! ## Mutant 2: mixed nesting hidden under a supported root -/

theorem mixed_right_has_typed_path :
    (classifyTerm unsupportedMixedRight).residue? =
      some
        { path := [.addRight]
        , constructor := .var
        } := by
  rfl

theorem mixed_left_has_typed_path :
    (classifyTerm unsupportedMixedLeft).residue? =
      some
        { path := [.addLeft]
        , constructor := .sub
        } := by
  rfl

theorem mixed_nesting_is_not_supported :
    (classifyTerm unsupportedMixedRight).isSupported = false := by
  rfl

/-! ## Mutant 3: a constructor omitted from the sealed surface -/

def omittedCallSurface : List TermConstructor :=
  [ .num, .var, .add, .sub, .mul, .div
  , .ifE, .neg, .lt, .eq, .let_
  ]

theorem omitted_constructor_mutant_exposed :
    TermConstructor.call ∉ omittedCallSurface ∧
    TermConstructor.call ∈ allTermConstructors := by
  decide

/-! ## Mutant 4: an unsupported constructor is accepted -/

/-- A bad root predicate that admits `sub` as if it were part of DQ-1. -/
def acceptsSubMutant : Term → Bool
  | .sub _ _ => true
  | term     => (classifyTerm term).isSupported

def unsupportedSub : Term :=
  .sub (.num 5) (.num 2)

theorem unsupported_acceptance_mutant_exposed :
    acceptsSubMutant unsupportedSub = true ∧
    (classifyTerm unsupportedSub).isSupported = false := by
  decide

/-! ## Unsupported is a phase result, not `NotEqual` -/

theorem unsupported_left_is_not_an_equality_verdict :
    prepareComparison unsupportedLeaf supportedLeaf =
      .unsupported .left
        { path := []
        , constructor := .var
        } := by
  rfl

theorem supported_pair_reaches_comparison :
    ∃ leftProof rightProof,
      prepareComparison supportedLeaf supportedNested =
        .ready leftProof rightProof := by
  refine ⟨?_, ?_, ?_⟩
  · exact (classify_supported_iff supportedLeaf).mp rfl
  · exact (classify_supported_iff supportedNested).mp rfl
  · rfl

/-! ## Constructor-surface coverage -/

example (ctor : TermConstructor) : ctor ∈ allTermConstructors :=
  all_term_constructors_complete ctor

example (term : Term) : rootConstructor term ∈ allTermConstructors :=
  root_constructor_covered term

example (ctor : UnsupportedConstructor) :
    ctor.toTermConstructor ∈ allTermConstructors :=
  unsupported_constructor_covered ctor

#print axioms classify_supported_iff
#print axioms classify_unsupported_iff
#print axioms supported_pair_reaches_comparison

end Residua.RCC.DefeqFragment.Tests

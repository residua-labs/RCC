import RCC.DefeqNormalizer

/-!
# Tests and load-bearing mutants for DQ-2

The positive witnesses exercise arbitrary recursive `add` nesting.  The
mutants exhibit the three shortcuts DQ-2 forbids:

* a partial normalizer over the raw `Term` domain;
* a fallback that collapses unsupported terms into a valid normal form;
* a recursive `add` implementation that silently omits one child.
-/

namespace Residua.RCC.DefeqNormalizer.Tests

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer

def supportedZero : NumAddTerm :=
  ⟨.num 0, .num 0⟩

def supportedNested : NumAddTerm :=
  ⟨ .add (.num 1) (.add (.num 2) (.num 3))
  , .add (.num 1) (.add (.num 2) (.num 3))
  ⟩

def unsupportedVariable : Term :=
  .var "outside-fragment"

example : normalize supportedZero = .int 0 := by
  rfl

example : normalize supportedNested = .int 6 := by
  rfl

example (term : NumAddTerm) :
    ∃ normalForm : NumAddNormalForm, normalize term = normalForm :=
  normalize_total term

/-! ## Mutant 1: a partial normalizer over the raw domain -/

/-- Bad API shape: unsupported constructors are hidden behind `none` rather
than being rejected by the proof-carrying classifier boundary. -/
def rawPartialNormalizer : Term → Option NumAddNormalForm
  | .num value =>
      some (.int value)
  | .add left right =>
      match rawPartialNormalizer left, rawPartialNormalizer right with
      | some leftNormal, some rightNormal =>
          some (.int (leftNormal.value + rightNormal.value))
      | _, _ =>
          none
  | _ =>
      none

theorem raw_partial_normalizer_mutant_exposed :
    rawPartialNormalizer unsupportedVariable = none ∧
    ∃ cert,
      normalizeAtBoundary unsupportedVariable = .unsupported cert := by
  constructor
  · rfl
  · refine ⟨?_, ?_⟩
    · exact
        { residue :=
            { path := []
            , constructor := .var
            }
        , notInFragment := by
            intro supported
            cases supported
        }
    · rfl

/-! ## Mutant 2: unsupported input collapses into a valid normal form -/

/-- Bad fallback semantics: every unsupported constructor is identified with
the legitimate normal form `0`. -/
def fallbackCollapseNormalizer : Term → NumAddNormalForm
  | .num value =>
      .int value
  | .add left right =>
      .int
        ((fallbackCollapseNormalizer left).value +
         (fallbackCollapseNormalizer right).value)
  | _ =>
      .int 0

theorem fallback_collapse_mutant_exposed :
    fallbackCollapseNormalizer unsupportedVariable =
      fallbackCollapseNormalizer supportedZero.1 ∧
    normalizeAtBoundary unsupportedVariable ≠
      .normalized (normalize supportedZero) := by
  constructor
  · rfl
  · intro collapse
    cases collapse

/-! ## Mutant 3: recursive `add` omits its right child -/

/-- Bad recursion that traverses only the left spine of the supported term. -/
def omitRightAddProof :
    (term : Term) → InNumAddFragment term → NumAddNormalForm
  | .num value, _ =>
      .int value
  | .add left _, supported =>
      omitRightAddProof left (by
        cases supported with
        | add leftSupported _ =>
            exact leftSupported)
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

def omitRightAdd (term : NumAddTerm) : NumAddNormalForm :=
  omitRightAddProof term.1 term.property

theorem recursive_add_omission_mutant_exposed :
    omitRightAdd supportedNested = .int 1 ∧
    normalize supportedNested = .int 6 ∧
    omitRightAdd supportedNested ≠ normalize supportedNested := by
  decide

/-! ## Boundary separation remains proof carrying -/

theorem unsupported_only_at_classifier_boundary :
    ∃ cert,
      classifyToSubtype unsupportedVariable = .inr cert ∧
      normalizeAtBoundary unsupportedVariable = .unsupported cert := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      { residue :=
          { path := []
          , constructor := .var
          }
      , notInFragment := by
          intro supported
          cases supported
      }
  · rfl
  · rfl

#print axioms normalize_total
#print axioms boundary_normalizes_supported
#print axioms boundary_preserves_unsupported
#print axioms boundary_unsupported_origin
#print axioms recursive_add_omission_mutant_exposed
#print axioms unsupported_only_at_classifier_boundary

end Residua.RCC.DefeqNormalizer.Tests

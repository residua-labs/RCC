import RCC.DefeqFragment

/-!
# Registration site for DQ-1 (ResiduaRCCDefeqFragment)

`classify_supported_iff` / `classify_unsupported_iff` quantify over every
production `Term`; this site reads them at concrete terms.  Positive half: a
supported term classifies supported with membership, an unsupported term
classifies unsupported with a typed residue locating `mul`.  Discriminating
half: an accept-everything mutant disagrees with the real classifier at exactly
the unsupported fixture, and its acceptance contradicts fragment membership.
The library theorems are untouched.
-/

open Residua.RCC.DefeqFragment

namespace Residua.RCC.RegistrationSites.DQ1

/-- Concrete supported fixture. -/
def supportedAt : Term := .add (.num 1) (.num 2)

/-- Concrete unsupported fixture: `mul` is outside the `num`/`add` fragment. -/
def unsupportedAt : Term := .mul (.num 1) (.num 2)

/-- Positive: the supported fixture is classified supported. -/
theorem supported_classification_true :
    (classifyTerm supportedAt).isSupported = true := rfl

/-- Positive: the supported fixture carries membership, via the soundness
direction of the registered theorem. -/
theorem supported_in_fragment : InNumAddFragment supportedAt :=
  (classify_supported_iff supportedAt).mp supported_classification_true

/-- Positive: the unsupported fixture is classified unsupported. -/
theorem unsupported_classification_false :
    (classifyTerm unsupportedAt).isSupported = false := rfl

/-- Positive: completeness at the fixture — the negative classification yields
a proof that membership is impossible. -/
theorem unsupported_not_in_fragment : ¬ InNumAddFragment unsupportedAt :=
  (classify_unsupported_iff unsupportedAt).mp unsupported_classification_false

/-- Positive: the proof-carrying classification locates the first unsupported
constructor (`mul`) at the empty path. -/
theorem unsupported_residue_locates_mul :
    (classifyTerm unsupportedAt).residue? =
      some { path := [], constructor := .mul } := rfl

/-- Positive: `classifyToSubtype` routes the two fixtures to opposite sides. -/
theorem supported_to_subtype_left :
    classifyToSubtype supportedAt =
      .inl ⟨supportedAt, .add (.num 1) (.num 2)⟩ := rfl

theorem unsupported_to_subtype_right :
    ∃ cert, classifyToSubtype unsupportedAt = .inr cert := ⟨_, rfl⟩

/-- The accept-everything mutant: a classifier that reports every term as
supported, erasing the fragment boundary. -/
def acceptAllMutant (_term : Term) : Bool := true

/-- Discriminating: the mutant disagrees with the real classifier at exactly
the unsupported fixture. -/
theorem mutant_disagrees_at_unsupported_fixture :
    acceptAllMutant unsupportedAt = true ∧
      (classifyTerm unsupportedAt).isSupported = false := ⟨rfl, rfl⟩

/-- Discriminating: the mutant's acceptance is unsound — the term it accepts is
provably not in the fragment (membership is what acceptance must mean). -/
theorem mutant_acceptance_unsound :
    acceptAllMutant unsupportedAt = true ∧ ¬ InNumAddFragment unsupportedAt :=
  ⟨rfl, unsupported_not_in_fragment⟩

/-- The mutant never reports a residue: the typed explanation is part of the
contract it fails to honour. -/
theorem mutant_carries_no_residue :
    ∀ term : Term, acceptAllMutant term = true :=
  fun _ => rfl

#print axioms supported_classification_true
#print axioms supported_in_fragment
#print axioms unsupported_classification_false
#print axioms unsupported_not_in_fragment
#print axioms unsupported_residue_locates_mul
#print axioms supported_to_subtype_left
#print axioms unsupported_to_subtype_right
#print axioms mutant_disagrees_at_unsupported_fixture
#print axioms mutant_acceptance_unsound
#print axioms mutant_carries_no_residue

end Residua.RCC.RegistrationSites.DQ1

import RCCTests.OccurrenceAddressing

/-! RCC-83 candidate: typed occurrence identity and collision refusal. -/

namespace Residua.RCC.RCC83Target

open Residua.RCC.OccurrenceExactness.AddressingTests
open Residua.RCC.Addressing
open Residua.RCC.OccurrenceExactness

def occurrenceDigestInjective :
    DigestInjectiveOnCanonicalRange fixtureBinding :=
  fixture_digest_injective
def repeatDistinguished := first_occurrence_and_repeat_differ
def quotientObservationExact := occurrence_quotient_observation_exact
def codecRoundtrip := occurrence_codec_roundtrip
def generationDistinguished := occurrence_codec_distinguishes_generation
def occurrenceAddressExact := fixture_occurrence_address_exact
def retryAddressStable := retry_preserves_typed_occurrence_address
def intentionalRepeatAddressChanges := intentional_repeat_changes_typed_occurrence_address
def constantDigestCollision := constant_digest_mutant_collapses_occurrences
def identicalPreimageReuse := identical_occurrence_preimage_is_reused
def differentOccurrenceCollision := same_address_different_occurrence_is_collision

structure Certificate where
  occurrenceDigestInjective : DigestInjectiveOnCanonicalRange fixtureBinding
  repeatDistinguished : ¬ SameLogicalOccurrence firstOccurrence intentionalRepeat
  codecRoundtrip :
    fixtureCodec.decode (fixtureCodec.encode (fixtureClass firstOccurrence)) =
      some (fixtureClass firstOccurrence)
  generationDistinguished :
    fixtureCodec.encode (fixtureClass firstOccurrence) ≠
      fixtureCodec.encode (fixtureClass intentionalRepeat)
  occurrenceAddressExact :
    occurrenceAddress fixtureBinding firstOccurrence =
        occurrenceAddress fixtureBinding intentionalRepeat ↔
      SameLogicalOccurrence firstOccurrence intentionalRepeat
  retryAddressStable :
    occurrenceAddress fixtureBinding firstOccurrence =
      occurrenceAddress fixtureBinding retryOccurrence
  intentionalRepeatAddressChanges :
    occurrenceAddress fixtureBinding firstOccurrence ≠
      occurrenceAddress fixtureBinding intentionalRepeat
  constantDigestCollision :
    occurrenceAddress constantBinding firstOccurrence =
        occurrenceAddress constantBinding intentionalRepeat ∧
      ¬ SameLogicalOccurrence firstOccurrence intentionalRepeat
  identicalPreimageReuse :
    inspectAddressed storedFirstOccurrence proposedRetryOccurrence = .reuse
  differentOccurrenceCollision :
    inspectAddressed storedFirstOccurrence proposedIntentionalRepeat = .collision

def certificate : Certificate where
  occurrenceDigestInjective := occurrenceDigestInjective
  repeatDistinguished := repeatDistinguished
  codecRoundtrip := codecRoundtrip (fixtureClass firstOccurrence)
  generationDistinguished := generationDistinguished
  occurrenceAddressExact :=
    occurrenceAddressExact firstOccurrence intentionalRepeat
  retryAddressStable := retryAddressStable
  intentionalRepeatAddressChanges := intentionalRepeatAddressChanges
  constantDigestCollision := constantDigestCollision
  identicalPreimageReuse := identicalPreimageReuse
  differentOccurrenceCollision := differentOccurrenceCollision

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC83Target

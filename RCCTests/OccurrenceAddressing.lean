import RCC.OccurrenceAddressing

/-!
# RCC-27 typed occurrence-address witnesses

The positive binding uses a tiny injective digest over a two-generation
fixture.  The constant-digest mutant demonstrates why the explicit
`DigestInjectiveOnCanonicalRange` premise cannot be removed.
-/

namespace Residua.RCC.OccurrenceExactness.AddressingTests

open Residua.RCC.Addressing
open Residua.RCC.OccurrenceExactness

abbrev FixtureOccurrence :=
  Occurrence Unit Unit Bool Unit

abbrev FixtureKey :=
  OccurrenceKey Unit Unit Bool Unit

abbrev FixtureWire :=
  DigestPreimage FixtureKey

def structuralFrame : ExactFrame FixtureKey FixtureWire where
  encode := fun preimage => preimage
  encode_injective := by
    intro left right equal
    exact equal

def fixtureDigest (preimage : FixtureWire) : Digest :=
  match preimage.canonicalBytes.generation with
  | false => ⟨"generation:false"⟩
  | true => ⟨"generation:true"⟩

def fixtureBinding :
    OccurrenceDigestBinding Unit Unit Bool Unit FixtureWire where
  algorithm := ⟨"fixture-injective"⟩
  domainQ := ⟨"residua:occurrence:fixture"⟩
  schemaQ := ⟨"residua:occurrence:fixture:v1"⟩
  frame := structuralFrame
  hash := fixtureDigest

theorem fixture_digest_injective :
    DigestInjectiveOnCanonicalRange fixtureBinding := by
  intro left right equalDigest
  rcases left with ⟨⟨⟩, ⟨⟩, leftGeneration, ⟨⟩⟩
  rcases right with ⟨⟨⟩, ⟨⟩, rightGeneration, ⟨⟩⟩
  cases leftGeneration <;> cases rightGeneration
  · rfl
  · have different :
        (Digest.mk "generation:false") ≠
          Digest.mk "generation:true" := by
      decide
    exact False.elim (different equalDigest)
  · have different :
        (Digest.mk "generation:true") ≠
          Digest.mk "generation:false" := by
      decide
    exact False.elim (different equalDigest)
  · rfl

def firstOccurrence : FixtureOccurrence :=
  ⟨(), (), false, ()⟩

def retryOccurrence : FixtureOccurrence :=
  ⟨(), (), false, ()⟩

def intentionalRepeat : FixtureOccurrence :=
  ⟨(), (), true, ()⟩

abbrev FixtureDomain :=
  occurrenceIdentityDomain Unit Unit Bool Unit

abbrev FixtureClass :=
  OccurrenceClass Unit Unit Bool Unit

def fixtureClass (occurrence : FixtureOccurrence) : FixtureClass :=
  qAbs FixtureDomain
    (occurrenceQuotientAdequate Unit Unit Bool Unit) () occurrence

def fixtureCodec :
    ExactCanonicalCodec FixtureClass FixtureKey :=
  occurrenceClassCodec Unit Unit Bool Unit

theorem first_occurrence_and_repeat_differ :
    ¬ SameLogicalOccurrence firstOccurrence intentionalRepeat := by
  intro same
  exact (by decide : false ≠ true) same.2.2.1

theorem occurrence_quotient_observation_exact
    (left right : FixtureOccurrence) :
    fixtureClass left = fixtureClass right ↔
      occurrenceKey left = occurrenceKey right := by
  exact quotient_exact_iff_observation
    FixtureDomain
    (occurrenceQuotientAdequate Unit Unit Bool Unit)
    (occurrenceObservationExact Unit Unit Bool Unit)
    () left right

theorem occurrence_codec_roundtrip (quotientClass : FixtureClass) :
    fixtureCodec.decode (fixtureCodec.encode quotientClass) =
      some quotientClass :=
  fixtureCodec.decode_encode quotientClass

theorem occurrence_codec_distinguishes_generation :
    fixtureCodec.encode (fixtureClass firstOccurrence) ≠
      fixtureCodec.encode (fixtureClass intentionalRepeat) := by
  decide

theorem fixture_occurrence_address_exact
    (left right : FixtureOccurrence) :
    occurrenceAddress fixtureBinding left =
        occurrenceAddress fixtureBinding right ↔
      SameLogicalOccurrence left right := by
  exact occurrence_address_exact
    fixtureBinding fixture_digest_injective left right

theorem retry_preserves_typed_occurrence_address :
    occurrenceAddress fixtureBinding firstOccurrence =
      occurrenceAddress fixtureBinding retryOccurrence := by
  rfl

theorem intentional_repeat_changes_typed_occurrence_address :
    occurrenceAddress fixtureBinding firstOccurrence ≠
      occurrenceAddress fixtureBinding intentionalRepeat := by
  intro equalAddress
  have sameOccurrence :=
    (fixture_occurrence_address_exact
      firstOccurrence intentionalRepeat).1 equalAddress
  exact first_occurrence_and_repeat_differ sameOccurrence

def constantDigest (_ : FixtureWire) : Digest :=
  ⟨"constant"⟩

def constantBinding :
    OccurrenceDigestBinding Unit Unit Bool Unit FixtureWire where
  algorithm := ⟨"fixture-constant-mutant"⟩
  domainQ := ⟨"residua:occurrence:fixture"⟩
  schemaQ := ⟨"residua:occurrence:fixture:v1"⟩
  frame := structuralFrame
  hash := constantDigest

/--
Without digest-range injectivity, distinct logical occurrences can collide at
the digest address even though their structured keys remain distinct.
-/
theorem constant_digest_mutant_collapses_occurrences :
    occurrenceAddress constantBinding firstOccurrence =
        occurrenceAddress constantBinding intentionalRepeat ∧
      ¬ SameLogicalOccurrence firstOccurrence intentionalRepeat := by
  exact ⟨rfl, first_occurrence_and_repeat_differ⟩

def storedFirstOccurrence : AddressedCanonical constantBinding where
  canonicalBytes := occurrenceKey firstOccurrence

def proposedRetryOccurrence : AddressedCanonical constantBinding where
  canonicalBytes := occurrenceKey retryOccurrence

def proposedIntentionalRepeat : AddressedCanonical constantBinding where
  canonicalBytes := occurrenceKey intentionalRepeat

theorem identical_occurrence_preimage_is_reused :
    inspectAddressed storedFirstOccurrence proposedRetryOccurrence =
      .reuse := by
  decide

theorem same_address_different_occurrence_is_collision :
    inspectAddressed storedFirstOccurrence proposedIntentionalRepeat =
      .collision := by
  decide

#print axioms occurrence_address_exact
#print axioms occurrenceQuotientAdequate
#print axioms occurrenceObservationExact
#print axioms occurrence_key_of_key
#print axioms occurrence_of_key_of_occurrence
#print axioms occurrenceClassCodec
#print axioms occurrence_canonical_bytes_eq_key
#print axioms occurrence_quotient_observation_exact
#print axioms occurrence_codec_roundtrip
#print axioms occurrence_codec_distinguishes_generation
#print axioms fixture_digest_injective
#print axioms fixture_occurrence_address_exact
#print axioms first_occurrence_and_repeat_differ
#print axioms retry_preserves_typed_occurrence_address
#print axioms intentional_repeat_changes_typed_occurrence_address
#print axioms constant_digest_mutant_collapses_occurrences
#print axioms identical_occurrence_preimage_is_reused
#print axioms same_address_different_occurrence_is_collision

end Residua.RCC.OccurrenceExactness.AddressingTests

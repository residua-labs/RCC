import RCCTests.DefeqAddressExactness
import RCCTests.DefeqNormalFormCodec
import RCCTests.DefeqFuelIrrelevance

/-!
# RCC-61 target package

This candidate packages the current executable defeq-address boundary.  It
includes canonical normal-form codec roundtrips/injectivity, conditional bare
address exactness under an explicit digest-injectivity premise,
collision-aware reuse/refusal, and sufficient-fuel irrelevance.  The
constant-digest and insufficient-fuel mutants remain exposed, so this target
does not overclaim an unconditional DQ-8 theorem.
-/

namespace Residua.RCC.RCC61Target

open Residua.RCC.DefeqAddressExactness.Tests
open Residua.RCC.DefeqNormalFormCodec.Tests
open Residua.RCC.DefeqFuelIrrelevance.Tests
open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqNormalFormCodec
open Residua.RCC.DefeqExactness
open Residua.RCC.DefeqTypedAddress
open Residua.RCC.DefeqAddressExactness
open Residua.RCC.DefeqSemanticPreservation
open Residua.RCC.DefeqFuelIrrelevance

def positiveCodecRoundtrip := positive_roundtrip
def negativeCodecRoundtrip := negative_roundtrip
def canonicalDecodeIsUnique := concrete_canonical_decoding
def codecInjective
    {left right : NumAddNormalForm}
    (sameBytes : encode left = encode right) : left = right :=
  concrete_encoder_injective sameBytes
def conditionalAddressExactness := conditional_bare_address_exactness
def operationalReuseIsSound := operational_reuse_is_sound
def distinctTermsRemainDistinct := distinct_terms_are_not_defeq
def constantDigestCollision := constant_digest_collision_is_reported
def collisionHasWitness := reported_collision_carries_conflicting_preimages
def fuelIrrelevance := arbitrary_large_fuel_witness
def insufficientFuelMutant := insufficient_fuel_mutant_exposed

structure Certificate where
  positiveCodec : decode (encode (.int 3)) = some (.int 3)
  negativeCodec : decode (encode (.int (-4))) = some (.int (-4))
  canonicalDecode :
    ∀ bytes,
      decode bytes = some (.int 2) →
      bytes = [nonnegativeTag, magnitudeUnit, magnitudeUnit]
  codecInjective :
    ∀ {left right : NumAddNormalForm},
      encode left = encode right → left = right
  conditionalAddress :
    ∀ (digest : DigestOperation)
      (injective : DigestInjectiveOnDefeqRange profile digest)
      (left right : NumAddTerm),
      defeqAddress profile digest context left =
          defeqAddress profile digest context right ↔
        DefEq left right
  operationalReuse :
    ∀ (left right : NumAddTerm)
      (reused :
        (inspectDefeqAddresses
            profile constantDigest context left right).state = .reuse),
      DefEq left right
  distinctTerms : ¬ DefEq oneTerm twoTerm
  constantCollision :
    (inspectDefeqAddresses
        profile constantDigest context oneTerm twoTerm).state =
      .collision
  collisionWitness :
    ∃ certificate :
        CollisionCertificate
          profile constantDigest context oneTerm twoTerm,
      inspectDefeqAddresses
          profile constantDigest context oneTerm twoTerm =
        .collision certificate
  fuelIrrelevance :
    ∀ (extra₁ extra₂ : Nat),
      evalLF (requiredFuel nestedTerm.1 + extra₁) nestedTerm.1
          arbitraryEnv arbitraryProgs =
        evalLF (requiredFuel nestedTerm.1 + extra₂) nestedTerm.1
          arbitraryEnv arbitraryProgs
  insufficientFuel :
    requiredFuel oneAddTerm.1 = 2 ∧
    evalLF 1 oneAddTerm.1 arbitraryEnv arbitraryProgs = none ∧
    evalLF (requiredFuel oneAddTerm.1) oneAddTerm.1
        arbitraryEnv arbitraryProgs =
      some (.int (normalize oneAddTerm).value) ∧
    evalLF 1 oneAddTerm.1 arbitraryEnv arbitraryProgs ≠
      evalLF (requiredFuel oneAddTerm.1) oneAddTerm.1
        arbitraryEnv arbitraryProgs

def certificate : Certificate where
  positiveCodec := positiveCodecRoundtrip
  negativeCodec := negativeCodecRoundtrip
  canonicalDecode := canonicalDecodeIsUnique
  codecInjective := by
    intro left right sameBytes
    exact codecInjective sameBytes
  conditionalAddress := conditionalAddressExactness
  operationalReuse := operationalReuseIsSound
  distinctTerms := distinctTermsRemainDistinct
  constantCollision := constantDigestCollision
  collisionWitness := collisionHasWitness
  fuelIrrelevance := fuelIrrelevance
  insufficientFuel := insufficientFuelMutant

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC61Target

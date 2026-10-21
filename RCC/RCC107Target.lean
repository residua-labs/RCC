import RCCTests.DefeqAddressExactness

/-! RCC-107 candidate: DQ-8 collision-aware defeq address exactness. -/

namespace Residua.RCC.RCC107Target

open Residua.RCC.DefeqAddressExactness.Tests
open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqExactness
open Residua.RCC.DefeqTypedAddress
open Residua.RCC.DefeqAddressExactness

theorem conditionalBareAddressExactness
    (digest : DigestOperation)
    (injective : DigestInjectiveOnDefeqRange profile digest)
    (left right : NumAddTerm) :
    defeqAddress profile digest context left =
        defeqAddress profile digest context right ↔
      DefEq left right :=
  conditional_bare_address_exactness digest injective left right

def operationalEquivalentReuse := operational_equivalent_terms_reuse

theorem operationalReuseSound
    (left right : NumAddTerm)
    (reused :
      (inspectDefeqAddresses
          profile constantDigest context left right).state = .reuse) :
    DefEq left right :=
  operational_reuse_is_sound left right reused

def distinctTermsRefused := distinct_terms_are_not_defeq
def constantDigestCollapses := constant_digest_collapses_distinct_terms
def constantDigestNoInjectivity := constant_digest_has_no_injective_certificate
def collisionReported := constant_digest_collision_is_reported
def collisionCarriesPreimages := reported_collision_carries_conflicting_preimages

abbrev ConditionalBareAddressExactness : Prop :=
  ∀ (digest : DigestOperation),
    DigestInjectiveOnDefeqRange profile digest →
    ∀ (left right : NumAddTerm),
      defeqAddress profile digest context left =
          defeqAddress profile digest context right ↔
        DefEq left right
abbrev OperationalEquivalentReuse : Prop :=
  (inspectDefeqAddresses
      profile constantDigest context onePlusOneTerm twoTerm).state = .reuse
abbrev OperationalReuseSound : Prop :=
  ∀ (left right : NumAddTerm),
    (inspectDefeqAddresses
        profile constantDigest context left right).state = .reuse →
      DefEq left right
abbrev DistinctTermsRefused : Prop := ¬ DefEq oneTerm twoTerm
abbrev ConstantDigestCollapses : Prop :=
  defeqAddress profile constantDigest context oneTerm =
    defeqAddress profile constantDigest context twoTerm
abbrev ConstantDigestNoInjectivity : Prop :=
  ¬ DigestInjectiveOnDefeqRange profile constantDigest
abbrev CollisionReported : Prop :=
  (inspectDefeqAddresses
      profile constantDigest context oneTerm twoTerm).state = .collision
abbrev CollisionCarriesPreimages : Prop :=
  ∃ certificate :
      CollisionCertificate profile constantDigest context oneTerm twoTerm,
    inspectDefeqAddresses
        profile constantDigest context oneTerm twoTerm =
      .collision certificate

structure Certificate where
  conditionalBareAddressExactness :
    ∀ (digest : DigestOperation)
      (injective : DigestInjectiveOnDefeqRange profile digest)
      (left right : NumAddTerm),
      defeqAddress profile digest context left =
          defeqAddress profile digest context right ↔
        DefEq left right
  operationalEquivalentReuse :
    (inspectDefeqAddresses
        profile constantDigest context onePlusOneTerm twoTerm).state = .reuse
  operationalReuseSound :
    ∀ (left right : NumAddTerm),
      (inspectDefeqAddresses
          profile constantDigest context left right).state = .reuse →
        DefEq left right
  distinctTermsRefused : ¬ DefEq oneTerm twoTerm
  constantDigestCollapses :
    defeqAddress profile constantDigest context oneTerm =
      defeqAddress profile constantDigest context twoTerm
  constantDigestNoInjectivity :
    ¬ DigestInjectiveOnDefeqRange profile constantDigest
  collisionReported :
    (inspectDefeqAddresses
        profile constantDigest context oneTerm twoTerm).state = .collision
  collisionCarriesPreimages :
    ∃ certificate :
        CollisionCertificate profile constantDigest context oneTerm twoTerm,
      inspectDefeqAddresses
          profile constantDigest context oneTerm twoTerm =
        .collision certificate

def certificate : Certificate where
  conditionalBareAddressExactness := conditionalBareAddressExactness
  operationalEquivalentReuse := operationalEquivalentReuse
  operationalReuseSound := operationalReuseSound
  distinctTermsRefused := distinctTermsRefused
  constantDigestCollapses := constantDigestCollapses
  constantDigestNoInjectivity := constantDigestNoInjectivity
  collisionReported := collisionReported
  collisionCarriesPreimages := collisionCarriesPreimages

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC107Target

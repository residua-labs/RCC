import RCC.DefeqAddressExactness

/-!
# Tests and load-bearing countermodels for DQ-8

The positive witnesses instantiate both DQ-8 profiles:

* bare address equality is exact only under an explicit range-injectivity
  premise; and
* collision-aware reuse is exact without that premise because complete framed
  preimages are compared.

The countermodel uses a constant digest.  It proves that two non-defeq terms
receive the same typed address, that no injectivity certificate can exist for
that digest, and that the operational profile reports a collision rather than
upgrading address equality into semantic equality.
-/

namespace Residua.RCC.DefeqAddressExactness.Tests

open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqExactness
open Residua.RCC.DefeqTypedAddress
open Residua.RCC.DefeqAddressExactness

/-! ## Sealed fixtures -/

def algorithmCoordinate : AlgorithmCoordinate :=
  { id := ⟨"sha256"⟩ }

def domainCoordinate : DomainCoordinate :=
  { id := ⟨"residua:defeq"⟩ }

def schemaCoordinate : SchemaCoordinate :=
  { id := ⟨"residua:defeq:v1"⟩ }

def profile : DefeqAddressProfile :=
  { algorithm := algorithmCoordinate
    domain := domainCoordinate
    schema := schemaCoordinate }

def context : ContextSemanticQ :=
  ⟨[42, 7]⟩

def oneTerm : NumAddTerm :=
  ⟨.num 1, .num 1⟩

def twoTerm : NumAddTerm :=
  ⟨.num 2, .num 2⟩

def onePlusOneTerm : NumAddTerm :=
  ⟨.add (.num 1) (.num 1),
    .add (.num 1) (.num 1)⟩

/-- Deliberately non-injective digest for the DQ-8 countermodel. -/
def constantDigest : DigestOperation :=
  fun _ => ⟨"constant"⟩

/-! ## Positive theorem-profile witnesses -/

theorem conditional_bare_address_exactness
    (digest : DigestOperation)
    (injective : DigestInjectiveOnDefeqRange profile digest)
    (left right : NumAddTerm) :
    defeqAddress profile digest context left =
        defeqAddress profile digest context right ↔
      DefEq left right := by
  exact
    address_eq_iff_defeq
      profile digest injective context left right

/-- Operational exactness does not require a hash assumption.  These two
syntactically different supported terms normalize to one canonical form. -/
theorem operational_equivalent_terms_reuse :
    (inspectDefeqAddresses
        profile constantDigest context onePlusOneTerm twoTerm).state =
      .reuse := by
  exact
    (inspect_reuse_iff_defeq
      profile constantDigest context onePlusOneTerm twoTerm).2
        (by decide)

/-- Reuse always proves semantic defeq from complete framed-byte equality. -/
theorem operational_reuse_is_sound
    (left right : NumAddTerm)
    (reused :
      (inspectDefeqAddresses
          profile constantDigest context left right).state = .reuse) :
    DefEq left right := by
  exact
    (inspect_reuse_iff_defeq
      profile constantDigest context left right).1 reused

/-! ## Countermodel: digest equality is not semantic equality -/

theorem distinct_terms_are_not_defeq :
    ¬ DefEq oneTerm twoTerm := by
  decide

/-- Bare address equality is unsound for a non-injective digest. -/
theorem constant_digest_collapses_distinct_terms :
    defeqAddress profile constantDigest context oneTerm =
      defeqAddress profile constantDigest context twoTerm := by
  rfl

/-- Consequently the constant digest cannot inhabit the explicit DQ-8
injectivity premise.  Failure to produce the certificate is not replaced by
an empirical no-collision claim. -/
theorem constant_digest_has_no_injective_certificate :
    ¬ DigestInjectiveOnDefeqRange profile constantDigest := by
  intro purportedInjectivity
  have sameFrame :
      framedBytes profile (preimage context oneTerm) =
        framedBytes profile (preimage context twoTerm) :=
    purportedInjectivity rfl
  exact distinct_terms_are_not_defeq
    ((framedBytes_eq_iff_defeq
      profile context oneTerm twoTerm).1 sameFrame)

/-- Collision-aware resolution refuses the same-address/different-preimage
countermodel instead of reusing either term. -/
theorem constant_digest_collision_is_reported :
    (inspectDefeqAddresses
        profile constantDigest context oneTerm twoTerm).state =
      .collision := by
  unfold inspectDefeqAddresses
  simp only [constant_digest_collapses_distinct_terms, ↓reduceDIte]
  have differentFrame :
      framedBytes profile (preimage context oneTerm) ≠
        framedBytes profile (preimage context twoTerm) := by
    intro sameFrame
    exact distinct_terms_are_not_defeq
      ((framedBytes_eq_iff_defeq
        profile context oneTerm twoTerm).1 sameFrame)
  simp [differentFrame, CollisionAwareResolution.state]

/-- The collision result retains the exact operational witness. -/
theorem reported_collision_carries_conflicting_preimages :
    ∃ certificate :
        CollisionCertificate
          profile constantDigest context oneTerm twoTerm,
      inspectDefeqAddresses
          profile constantDigest context oneTerm twoTerm =
        .collision certificate := by
  exact
    inspect_collision_has_witness
      (inspectDefeqAddresses
        profile constantDigest context oneTerm twoTerm)
      constant_digest_collision_is_reported

#print axioms canonicalNormalFormBytes_injective
#print axioms preimage_eq_iff_defeq
#print axioms framedBytes_eq_iff_defeq
#print axioms defeq_implies_address_eq
#print axioms address_eq_implies_defeq
#print axioms address_eq_iff_defeq
#print axioms reuse_implies_defeq
#print axioms inspect_reuse_iff_defeq
#print axioms constant_digest_has_no_injective_certificate
#print axioms constant_digest_collision_is_reported
#print axioms reported_collision_carries_conflicting_preimages

end Residua.RCC.DefeqAddressExactness.Tests

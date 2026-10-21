import RCC.DefeqTypedAddress

/-!
# RCC defeq address exactness under an explicit digest profile

This file establishes DQ-8 for the DQ-1..DQ-7 `num`/`add` instance.
It provides two deliberately distinct results:

1. bare typed-address equality is exact for defeq only when the digest
   operation carries an explicit injectivity certificate on the canonical
   DQ-7 framed range; and
2. without that premise, an operational comparison may reuse only after
   checking complete framed-preimage equality and must classify an encountered
   same-address/different-preimage pair as a collision.

The second result is an operational safety theorem, not a cryptographic
injectivity theorem.  No corpus, parity seal, or absence of an observed
collision is upgraded into the first premise.
-/

namespace Residua.RCC.DefeqAddressExactness

open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqExactness
open Residua.RCC.DefeqNormalFormCodec
open Residua.RCC.DefeqTypedAddress

/-! ## Canonical-byte and framed-preimage exactness -/

/-- `UInt8.toNat` is injective. -/
private theorem uint8_toNat_injective
    {left right : UInt8}
    (sameNat : left.toNat = right.toNat) :
    left = right := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_toNat_eq
  exact sameNat

/-- Mapping `UInt8.toNat` over a list retains the complete octet sequence. -/
private theorem map_uint8_toNat_injective :
    ∀ {left right : List UInt8},
      left.map UInt8.toNat = right.map UInt8.toNat →
      left = right := by
  intro left
  induction left with
  | nil =>
      intro right sameMap
      cases right with
      | nil =>
          rfl
      | cons _ _ =>
          cases sameMap
  | cons leftHead leftTail inductionHypothesis =>
      intro right sameMap
      cases right with
      | nil =>
          cases sameMap
      | cons rightHead rightTail =>
          simp only [List.map_cons] at sameMap
          have sameParts := List.cons.inj sameMap
          have sameHeadNat :
              leftHead.toNat = rightHead.toNat :=
            sameParts.1
          have sameHead : leftHead = rightHead :=
            uint8_toNat_injective sameHeadNat
          have sameTailMap :
              leftTail.map UInt8.toNat =
                rightTail.map UInt8.toNat :=
            sameParts.2
          have sameTail : leftTail = rightTail :=
            inductionHypothesis sameTailMap
          rw [sameHead, sameTail]

/-- DQ-6 exact encoding remains injective after its octets are embedded into
the DQ-7 preimage carrier. -/
theorem canonicalNormalFormBytes_injective
    {left right : NumAddNormalForm}
    (sameBytes :
      (encode left).map UInt8.toNat =
        (encode right).map UInt8.toNat) :
    left = right := by
  apply encode_injective
  exact map_uint8_toNat_injective sameBytes

/-- In one semantic context, the canonical DQ-7 preimage is equal exactly
when the supported terms are definitionally equal. -/
theorem preimage_eq_iff_defeq
    (context : ContextSemanticQ)
    (left right : NumAddTerm) :
    preimage context left = preimage context right ↔
      DefEq left right := by
  constructor
  · intro samePreimage
    have sameCanonicalBytes :
        canonicalNormalFormBytes left =
          canonicalNormalFormBytes right :=
      congrArg
        DefeqFramedPreimage.canonicalNormalFormBytes
        samePreimage
    have sameNormalForm :
        normalize left = normalize right := by
      apply canonicalNormalFormBytes_injective
      exact sameCanonicalBytes
    exact
      (normalize_eq_iff_defeq left right).1 sameNormalForm
  · intro equivalent
    exact equivalent_has_same_preimage context equivalent

/-- For a fixed typed profile and context, equality of complete framed digest
inputs is exactly DQ-5 definitional equality. -/
theorem framedBytes_eq_iff_defeq
    (profile : DefeqAddressProfile)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) :
    framedBytes profile (preimage context left) =
        framedBytes profile (preimage context right) ↔
      DefEq left right := by
  constructor
  · intro sameFrame
    exact
      (preimage_eq_iff_defeq context left right).1
        (framedBytes_injective profile sameFrame)
  · intro equivalent
    exact congrArg (framedBytes profile)
      ((preimage_eq_iff_defeq context left right).2 equivalent)

/-! ## Exactness relative to an explicit digest premise -/

/-- The sole cryptographic premise accepted by the bare-address DQ-8
theorem.  It is scoped to DQ-7 canonical frames, not asserted globally. -/
def DigestInjectiveOnDefeqRange
    (profile : DefeqAddressProfile)
    (digest : DigestOperation) : Prop :=
  ∀ {left right : DefeqFramedPreimage},
    digest (framedBytes profile left) =
        digest (framedBytes profile right) →
      framedBytes profile left =
        framedBytes profile right

/-- Project the canonical typed address produced by DQ-7. -/
def defeqAddress
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : NumAddTerm) : Address .semantic :=
  (bindAddress profile digest context term).address

/-- Address completeness is unconditional: defeq-equivalent supported terms
produce identical typed addresses in the same context. -/
theorem defeq_implies_address_eq
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    {left right : NumAddTerm}
    (equivalent : DefEq left right) :
    defeqAddress profile digest context left =
      defeqAddress profile digest context right := by
  have samePreimage :
      preimage context left = preimage context right :=
    equivalent_has_same_preimage context equivalent
  change
    ({ algorithm := profile.algorithm.id
       domainQ := profile.domain.id
       schemaQ := profile.schema.id
       digest := digest (framedBytes profile (preimage context left)) } :
      Address .semantic) =
    { algorithm := profile.algorithm.id
      domainQ := profile.domain.id
      schemaQ := profile.schema.id
      digest := digest (framedBytes profile (preimage context right)) }
  rw [samePreimage]

/-- Address soundness is conditional on the explicit range-injectivity
premise. -/
theorem address_eq_implies_defeq
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (injective : DigestInjectiveOnDefeqRange profile digest)
    (context : ContextSemanticQ)
    {left right : NumAddTerm}
    (sameAddress :
      defeqAddress profile digest context left =
        defeqAddress profile digest context right) :
    DefEq left right := by
  have sameDigest :
      digest (framedBytes profile (preimage context left)) =
        digest (framedBytes profile (preimage context right)) :=
    congrArg Address.digest sameAddress
  exact
    (framedBytes_eq_iff_defeq profile context left right).1
      (injective sameDigest)

/-- DQ-8 bare-address exactness, explicitly relative to the declared digest
profile. -/
theorem address_eq_iff_defeq
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (injective : DigestInjectiveOnDefeqRange profile digest)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) :
    defeqAddress profile digest context left =
        defeqAddress profile digest context right ↔
      DefEq left right := by
  exact
    ⟨address_eq_implies_defeq
        profile digest injective context,
      defeq_implies_address_eq profile digest context⟩

/-! ## Collision-aware operational profile -/

/-- Proof that byte-verified reuse is safe for one pair of supported terms. -/
structure ReuseCertificate
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) : Prop where
  sameAddress :
    defeqAddress profile digest context left =
      defeqAddress profile digest context right
  sameFramedPreimage :
    framedBytes profile (preimage context left) =
      framedBytes profile (preimage context right)

/-- Proof of an encountered collision.  It does not assert that the digest is
globally non-injective; it records exactly this conflicting pair. -/
structure CollisionCertificate
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) : Prop where
  sameAddress :
    defeqAddress profile digest context left =
      defeqAddress profile digest context right
  differentFramedPreimage :
    framedBytes profile (preimage context left) ≠
      framedBytes profile (preimage context right)

/-- Proof that two typed addresses differ. -/
structure DistinctAddressCertificate
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) : Prop where
  differentAddress :
    defeqAddress profile digest context left ≠
      defeqAddress profile digest context right

/-- Exhaustive collision-aware operational result. -/
inductive CollisionAwareResolution
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm)
  | reuse :
      ReuseCertificate profile digest context left right →
      CollisionAwareResolution profile digest context left right
  | collision :
      CollisionCertificate profile digest context left right →
      CollisionAwareResolution profile digest context left right
  | distinct :
      DistinctAddressCertificate profile digest context left right →
      CollisionAwareResolution profile digest context left right

/-- Operational state erasure for testing and projection. -/
inductive CollisionAwareState
  | reuse
  | collision
  | distinct
  deriving DecidableEq, Repr

def CollisionAwareResolution.state
    {profile : DefeqAddressProfile}
    {digest : DigestOperation}
    {context : ContextSemanticQ}
    {left right : NumAddTerm} :
    CollisionAwareResolution profile digest context left right →
      CollisionAwareState
  | .reuse _     => .reuse
  | .collision _ => .collision
  | .distinct _  => .distinct

/-- Compare typed addresses, then retain and compare complete framed inputs
before authorizing reuse. -/
def inspectDefeqAddresses
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) :
    CollisionAwareResolution profile digest context left right :=
  if sameAddress :
      defeqAddress profile digest context left =
        defeqAddress profile digest context right then
    if sameFrame :
        framedBytes profile (preimage context left) =
          framedBytes profile (preimage context right) then
      .reuse
        { sameAddress := sameAddress
          sameFramedPreimage := sameFrame }
    else
      .collision
        { sameAddress := sameAddress
          differentFramedPreimage := sameFrame }
  else
    .distinct
      { differentAddress := sameAddress }

/-- Operational reuse is sound without any digest-injectivity assumption
because the complete DQ-7 frames were compared. -/
theorem reuse_implies_defeq
    {profile : DefeqAddressProfile}
    {digest : DigestOperation}
    {context : ContextSemanticQ}
    {left right : NumAddTerm}
    (certificate :
      ReuseCertificate profile digest context left right) :
    DefEq left right := by
  exact
    (framedBytes_eq_iff_defeq profile context left right).1
      certificate.sameFramedPreimage

/-- The collision-aware operational profile is exact for reuse: equivalent
terms always reuse, while reuse never relies on bare digest equality. -/
theorem inspect_reuse_iff_defeq
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (left right : NumAddTerm) :
    (inspectDefeqAddresses profile digest context left right).state =
        .reuse ↔
      DefEq left right := by
  constructor
  · intro reused
    unfold inspectDefeqAddresses at reused
    split at reused
    next sameAddress =>
      split at reused
      next sameFrame =>
        exact
          (framedBytes_eq_iff_defeq profile context left right).1
            sameFrame
      next _ =>
        cases reused
    next _ =>
      cases reused
  · intro equivalent
    have sameAddress :
        defeqAddress profile digest context left =
          defeqAddress profile digest context right :=
      defeq_implies_address_eq profile digest context equivalent
    have sameFrame :
        framedBytes profile (preimage context left) =
          framedBytes profile (preimage context right) :=
      (framedBytes_eq_iff_defeq profile context left right).2 equivalent
    simp [inspectDefeqAddresses, sameAddress, sameFrame,
      CollisionAwareResolution.state]

/-- Every operational collision result exposes equal typed addresses and
different complete preimages. -/
theorem inspect_collision_has_witness
    {profile : DefeqAddressProfile}
    {digest : DigestOperation}
    {context : ContextSemanticQ}
    {left right : NumAddTerm}
    (result :
      CollisionAwareResolution profile digest context left right)
    (isCollision : result.state = .collision) :
    ∃ certificate :
        CollisionCertificate profile digest context left right,
      result = .collision certificate := by
  cases result with
  | reuse _ =>
      cases isCollision
  | collision certificate =>
      exact ⟨certificate, rfl⟩
  | distinct _ =>
      cases isCollision

end Residua.RCC.DefeqAddressExactness

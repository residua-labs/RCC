import RCC.AddressResolution

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressedStore.Tests

/-!
# RCC AK-5 addressed-store insertion tests

These are deliberately small raw-store fixtures.  In particular, the
constant-digest binding is a structural collision witness, not a claim about
a concrete digest algorithm.
-/

private def sha256 : AlgorithmId := ⟨"sha256"⟩
private def valueDomainV1 : DomainQ := ⟨"residua:value"⟩
private def otherValueDomainV1 : DomainQ := ⟨"residua:other-value"⟩
private def valueSchemaV1 : SchemaQ := ⟨"residua:value:v1"⟩
private def repeatedDigest : Digest := ⟨"deadbeef"⟩

def structuralFrame (Bytes : Type) :
    ExactFrame Bytes (DigestPreimage Bytes) where
  encode := fun preimage => preimage
  encode_injective := by
    intro left right equal
    exact equal

/-- A digest fixture which visibly carries the canonical natural-number bytes. -/
def identityBinding :
    DigestBinding .value Nat (DigestPreimage Nat) where
  algorithm := sha256
  domainQ := valueDomainV1
  schemaQ := valueSchemaV1
  frame := structuralFrame Nat
  hash := fun preimage => ⟨preimage.canonicalBytes.repr⟩

/-- A deliberate same-address witness for the collision-refusal branch. -/
def constantBinding
    (domainQ : DomainQ := valueDomainV1) :
    DigestBinding .value Nat (DigestPreimage Nat) where
  algorithm := sha256
  domainQ := domainQ
  schemaQ := valueSchemaV1
  frame := structuralFrame Nat
  hash := fun _ => repeatedDigest

def emptyStore : AddressedStore .value Nat := fun _ => none

def alreadyPresent : AddressedStore .value Nat :=
  fun address =>
    if address = identityBinding.address 7 then some 7 else none

/-- Every slot is occupied by bytes which do not hash to the requested slot. -/
def corruptOccupiedSlot : AddressedStore .value Nat := fun _ => some 0

def occupiedStore : AddressedStore .value Nat := fun _ => some 7

def collisionProposed : AddressedCanonical (constantBinding) := ⟨8⟩

theorem put_empty_is_inserted :
    (putAddressed identityBinding emptyStore 7).disposition = .inserted := by
  rfl

theorem put_same_bytes_is_reused :
    (putAddressed identityBinding alreadyPresent 7).disposition = .reused := by
  rfl

theorem put_corrupt_occupied_slot_is_refused :
    (putAddressed identityBinding corruptOccupiedSlot 7).disposition =
      .occupiedSlotCorrupt := by
  rfl

theorem put_corrupt_slot_preserves_store_extentionally :
    (putAddressed identityBinding corruptOccupiedSlot 7).store =
      corruptOccupiedSlot := by
  funext address
  rfl

theorem put_constant_digest_collision_is_refused :
    (putAddressed
      (constantBinding) occupiedStore collisionProposed.canonicalBytes).disposition =
      .collision := by
  rfl

theorem put_addressed_collision_contract :
    (putAddressed
      (constantBinding) occupiedStore collisionProposed.canonicalBytes).disposition =
        .collision ↔
      ∃ storedBytes,
        occupiedStore
            ((constantBinding).address collisionProposed.canonicalBytes) =
          some storedBytes ∧
        (constantBinding).address storedBytes =
          (constantBinding).address collisionProposed.canonicalBytes ∧
        (constantBinding).preimage storedBytes ≠
          (constantBinding).preimage collisionProposed.canonicalBytes := by
  exact
    put_addressed_collision_iff
      (constantBinding) occupiedStore collisionProposed.canonicalBytes

theorem put_collision_preserves_store_contract
    (collision :
      (putAddressed
        (constantBinding) occupiedStore collisionProposed.canonicalBytes).disposition =
          .collision) :
    (putAddressed
      (constantBinding) occupiedStore collisionProposed.canonicalBytes).store =
        occupiedStore := by
  exact
    put_collision_preserves_store
      (constantBinding) occupiedStore collisionProposed.canonicalBytes collision

theorem put_corrupt_slot_preserves_store_contract
    (corrupt :
      (putAddressed identityBinding corruptOccupiedSlot 7).disposition =
        .occupiedSlotCorrupt) :
    (putAddressed identityBinding corruptOccupiedSlot 7).store =
      corruptOccupiedSlot := by
  exact
    put_corrupt_slot_preserves_store
      identityBinding corruptOccupiedSlot 7 corrupt

/-- Domain envelopes remain distinct store keys even with an identical digest. -/
theorem same_digest_payload_different_domain_inserts :
    (putAddressed
      (constantBinding otherValueDomainV1)
      (putAddressed (constantBinding valueDomainV1) emptyStore 7).store
      7).disposition = .inserted := by
  rfl

end Residua.RCC.Addressing.AddressedStore.Tests

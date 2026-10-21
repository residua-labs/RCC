import RCCTests.AddressedStore

/-! RCC-17 candidate: addressed stores recheck bytes and refuse digest aliases. -/

namespace Residua.RCC.RCC17Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedStore.Tests

structure Certificate where
  emptyInsertIsInserted :
    (putAddressed identityBinding emptyStore 7).disposition = .inserted
  sameBytesAreReused :
    (putAddressed identityBinding alreadyPresent 7).disposition = .reused
  corruptOccupiedSlotRefused :
    (putAddressed identityBinding corruptOccupiedSlot 7).disposition =
      .occupiedSlotCorrupt
  corruptSlotPreservesStore :
    (putAddressed identityBinding corruptOccupiedSlot 7).store =
      corruptOccupiedSlot
  constantDigestCollisionRefused :
    (putAddressed constantBinding occupiedStore
      collisionProposed.canonicalBytes).disposition = .collision
  collisionContractExact :
    (putAddressed constantBinding occupiedStore
      collisionProposed.canonicalBytes).disposition = .collision ↔
      ∃ storedBytes,
        occupiedStore
            (constantBinding.address collisionProposed.canonicalBytes) =
          some storedBytes ∧
        constantBinding.address storedBytes =
          constantBinding.address collisionProposed.canonicalBytes ∧
        constantBinding.preimage storedBytes ≠
          constantBinding.preimage collisionProposed.canonicalBytes
  collisionPreservesStore :
    ∀ (collision :
      (putAddressed constantBinding occupiedStore
        collisionProposed.canonicalBytes).disposition = .collision),
      (putAddressed constantBinding occupiedStore
        collisionProposed.canonicalBytes).store = occupiedStore

def certificate : Certificate where
  emptyInsertIsInserted := put_empty_is_inserted
  sameBytesAreReused := put_same_bytes_is_reused
  corruptOccupiedSlotRefused := put_corrupt_occupied_slot_is_refused
  corruptSlotPreservesStore := put_corrupt_slot_preserves_store_extentionally
  constantDigestCollisionRefused := put_constant_digest_collision_is_refused
  collisionContractExact := put_addressed_collision_contract
  collisionPreservesStore := put_collision_preserves_store_contract

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC17Target

import RCCTests.AddressedStore
import RCCTests.AddressResolution

/-!
# RCC-60 target package

This candidate packages the concrete addressed-store and addressed-resolution
receipts.  It covers insertion/reuse, corrupt-slot refusal, same-address
different-preimage collision refusal, domain separation, rehash validation,
codec refusal, and exact round-trip resolution.  The operational-versus-
semantic mismatch mutant remains visible; no digest-injectivity claim is
manufactured by the fixture.
-/

namespace Residua.RCC.RCC60Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedStore.Tests
open Residua.RCC.Addressing.AddressResolution.Tests

def emptyInsert := put_empty_is_inserted
def sameBytesReuse := put_same_bytes_is_reused
def corruptSlotRefused := put_corrupt_occupied_slot_is_refused
def corruptSlotPreserved := put_corrupt_slot_preserves_store_contract
def collisionRefused := put_constant_digest_collision_is_refused
def collisionContract := put_addressed_collision_contract
def collisionPreservesStore := put_collision_preserves_store_contract
def crossDomainInsert := same_digest_payload_different_domain_inserts
def wrongKeyRefused := resolve_wrong_key_is_rehash_mismatch
def decodeRefused := resolve_decode_refusal_is_explicit
def noncanonicalRefused := resolve_malleable_bytes_are_noncanonical
def honestResolution := resolve_honest_codec_returns_expected_class
def exactResolutionSound := resolve_addressed_exact_sound_contract
def exactRoundTrip := put_empty_then_resolve_exact_contract
def operationalMismatchExposed := no_refinement_countermodel_contract

structure Certificate where
  emptyInsert :
    (putAddressed
      Residua.RCC.Addressing.AddressedStore.Tests.identityBinding
      Residua.RCC.Addressing.AddressedStore.Tests.emptyStore 7).disposition =
      .inserted
  sameBytesReuse :
    (putAddressed
      Residua.RCC.Addressing.AddressedStore.Tests.identityBinding
      alreadyPresent 7).disposition = .reused
  corruptSlotRefused :
    (putAddressed
      Residua.RCC.Addressing.AddressedStore.Tests.identityBinding
      corruptOccupiedSlot 7).disposition =
      .occupiedSlotCorrupt
  corruptSlotPreserved :
    ∀ (corrupt :
      (putAddressed
        Residua.RCC.Addressing.AddressedStore.Tests.identityBinding
        corruptOccupiedSlot 7).disposition =
          .occupiedSlotCorrupt),
      (putAddressed
        Residua.RCC.Addressing.AddressedStore.Tests.identityBinding
        corruptOccupiedSlot 7).store = corruptOccupiedSlot
  collisionRefused :
    (putAddressed
      (constantBinding) occupiedStore collisionProposed.canonicalBytes).disposition =
      .collision
  collisionContract :
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
          (constantBinding).preimage collisionProposed.canonicalBytes
  collisionPreservesStore :
    ∀ (collision :
      (putAddressed
        (constantBinding) occupiedStore collisionProposed.canonicalBytes).disposition =
          .collision),
      (putAddressed
        (constantBinding) occupiedStore collisionProposed.canonicalBytes).store =
        occupiedStore
  crossDomainInsert :
    (putAddressed
      (constantBinding ⟨"residua:other-value"⟩)
      (putAddressed
        (constantBinding ⟨"residua:value"⟩)
        Residua.RCC.Addressing.AddressedStore.Tests.emptyStore 7).store
      7).disposition = .inserted
  wrongKeyRefused :
    resolveAddressed
      Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
      honestCodec wrongKeyStore requested =
      .rehashMismatch
  decodeRefused :
    resolveAddressed
      Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
      refusingCodec validStore requested =
      .decodeRefused
  noncanonicalRefused :
    resolveAddressed
      Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
      malleableCodec validStore requested =
      .noncanonicalBytes
  honestResolution :
    resolveAddressed
      Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
      honestCodec validStore requested =
      .resolved 1
  exactResolutionSound :
    ∀ (actual : Nat)
      (injective : DigestInjectiveOnCanonicalRange
        Residua.RCC.Addressing.AddressResolution.Tests.identityBinding)
      (resolved :
        resolveAddressed
          Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
          honestCodec validStore requested =
          .resolved actual),
      actual = 1
  exactRoundTrip :
    ∀ (expected : Nat),
      resolveAddressed
          Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
          honestCodec
          (putAddressed
            Residua.RCC.Addressing.AddressResolution.Tests.identityBinding
            (fun _ => none) (exactNatCodec.encode expected)).store
          (Residua.RCC.Addressing.AddressResolution.Tests.identityBinding.address
            (exactNatCodec.encode expected)) =
        .resolved expected
  operationalMismatchExposed :
    ∃ (binding : DigestBinding .value Nat (DigestPreimage Nat))
      (exact : ExactCanonicalCodec Nat Nat)
      (runtime : RuntimeCanonicalCodec Nat Nat)
      (store : AddressedStore .value Nat)
      (requested : Address .value),
        resolveAddressed binding runtime store requested = .resolved 1 ∧
        requested = binding.address (exact.encode 0) ∧
        (1 : Nat) ≠ 0 ∧
        ¬ RuntimeCanonicalCodec.RefinesExact runtime exact

def certificate : Certificate where
  emptyInsert := emptyInsert
  sameBytesReuse := sameBytesReuse
  corruptSlotRefused := corruptSlotRefused
  corruptSlotPreserved := corruptSlotPreserved
  collisionRefused := collisionRefused
  collisionContract := collisionContract
  collisionPreservesStore := collisionPreservesStore
  crossDomainInsert := crossDomainInsert
  wrongKeyRefused := wrongKeyRefused
  decodeRefused := decodeRefused
  noncanonicalRefused := noncanonicalRefused
  honestResolution := honestResolution
  exactResolutionSound := exactResolutionSound
  exactRoundTrip := exactRoundTrip
  operationalMismatchExposed := operationalMismatchExposed

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC60Target

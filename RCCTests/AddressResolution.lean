import RCC.AddressResolution

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressResolution.Tests

/-!
# RCC AK-5 addressed-resolution tests

The raw stores below are intentionally adversarial: resolution must validate
the requested key, runtime decoding, and the decoder's re-encoding.
-/

private def sha256 : AlgorithmId := ⟨"sha256"⟩
private def valueDomainV1 : DomainQ := ⟨"residua:value"⟩
private def valueSchemaV1 : SchemaQ := ⟨"residua:value:v1"⟩

def structuralFrame (Bytes : Type) :
    ExactFrame Bytes (DigestPreimage Bytes) where
  encode := fun preimage => preimage
  encode_injective := by
    intro left right equal
    exact equal

/-- The digest is a readable encoding of the canonical natural-number bytes. -/
def identityBinding :
    DigestBinding .value Nat (DigestPreimage Nat) where
  algorithm := sha256
  domainQ := valueDomainV1
  schemaQ := valueSchemaV1
  frame := structuralFrame Nat
  hash := fun preimage => ⟨preimage.canonicalBytes.repr⟩

def exactNatCodec : ExactCanonicalCodec Nat Nat where
  encode := fun value => value
  decode := fun bytes => some bytes
  decode_encode := by
    intro value
    rfl
  encode_decode_canonical := by
    intro bytes value accepted
    exact (Option.some.inj accepted).symm

/-- The executable codec obtained directly from the exact codec. -/
def honestCodec : RuntimeCanonicalCodec Nat Nat where
  encode := exactNatCodec.encode
  decode := exactNatCodec.decode

def honestCodecRefinesExact :
    RuntimeCanonicalCodec.RefinesExact honestCodec exactNatCodec where
  encode_eq := rfl
  decode_eq := rfl

def refusingCodec : RuntimeCanonicalCodec Nat Nat where
  encode := exactNatCodec.encode
  decode := fun _ => none

/-- Self-consistent at byte `0`, but not a refinement of `exactNatCodec`. -/
def malleableCodec : RuntimeCanonicalCodec Nat Nat where
  encode := fun _ => 0
  decode := fun _ => some 1

def requested : Address .value := identityBinding.address 1

def emptyStore : AddressedStore .value Nat := fun _ => none

def validStore : AddressedStore .value Nat :=
  fun address => if address = requested then some 1 else none

/-- Returns valid bytes under the wrong requested key. -/
def wrongKeyStore : AddressedStore .value Nat :=
  fun address => if address = requested then some 0 else none

def zeroRequested : Address .value := identityBinding.address 0

def zeroStore : AddressedStore .value Nat :=
  fun address => if address = zeroRequested then some 0 else none

theorem resolve_empty_is_not_found :
    resolveAddressed identityBinding honestCodec emptyStore requested = .notFound := by
  rfl

theorem resolve_wrong_key_is_rehash_mismatch :
    resolveAddressed identityBinding honestCodec wrongKeyStore requested =
      .rehashMismatch := by
  rfl

theorem resolve_decode_refusal_is_explicit :
    resolveAddressed identityBinding refusingCodec validStore requested =
      .decodeRefused := by
  rfl

theorem resolve_malleable_bytes_are_noncanonical :
    resolveAddressed identityBinding malleableCodec validStore requested =
      .noncanonicalBytes := by
  rfl

theorem resolve_honest_codec_returns_expected_class :
    resolveAddressed identityBinding honestCodec validStore requested =
      .resolved 1 := by
  rfl

/-- Operational agreement alone can resolve `1` at the exact address of `0`. -/
theorem malicious_operational_resolution_is_not_semantic_sound :
    resolveAddressed identityBinding malleableCodec zeroStore zeroRequested =
      .resolved 1 := by
  rfl

theorem resolve_addressed_resolved_contract (actual : Nat) :
    resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual ↔
      ∃ fetchedBytes,
        validStore requested = some fetchedBytes ∧
        identityBinding.address fetchedBytes = requested ∧
        honestCodec.decode fetchedBytes = some actual ∧
        honestCodec.encode actual = fetchedBytes := by
  exact
    resolve_addressed_resolved_iff
      identityBinding honestCodec validStore requested actual

theorem requested_is_expected_address :
    requested = identityBinding.address (exactNatCodec.encode 1) := by
  rfl

theorem resolve_addressed_exact_sound_contract
    (actual : Nat)
    (injective : DigestInjectiveOnCanonicalRange identityBinding)
    (resolved :
      resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual) :
    actual = 1 := by
  exact
    resolve_addressed_exact_sound
      identityBinding exactNatCodec honestCodec honestCodecRefinesExact injective
      validStore requested 1 actual requested_is_expected_address resolved

theorem put_empty_then_resolve_exact_contract (expected : Nat) :
    resolveAddressed
        identityBinding
        honestCodec
        (putAddressed
          identityBinding (fun _ => none) (exactNatCodec.encode expected)).store
        (identityBinding.address (exactNatCodec.encode expected)) =
      .resolved expected := by
  exact
    put_empty_then_resolve_exact
      identityBinding exactNatCodec honestCodec honestCodecRefinesExact expected

theorem no_refinement_countermodel_contract :
    ∃ (binding : DigestBinding .value Nat (DigestPreimage Nat))
      (exact : ExactCanonicalCodec Nat Nat)
      (runtime : RuntimeCanonicalCodec Nat Nat)
      (store : AddressedStore .value Nat)
      (requested : Address .value),
        resolveAddressed binding runtime store requested = .resolved 1 ∧
        requested = binding.address (exact.encode 0) ∧
        (1 : Nat) ≠ 0 ∧
        ¬ RuntimeCanonicalCodec.RefinesExact runtime exact := by
  exact operational_resolution_without_codec_refinement_is_not_semantic_sound

#print axioms put_addressed_eq_collision_iff
#print axioms put_collision_preserves_store
#print axioms put_corrupt_slot_preserves_store
#print axioms resolve_addressed_eq_resolved_iff
#print axioms resolve_addressed_exact_sound
#print axioms put_empty_then_resolve_exact
#print axioms operational_resolution_without_codec_refinement_is_not_semantic_sound

end Residua.RCC.Addressing.AddressResolution.Tests

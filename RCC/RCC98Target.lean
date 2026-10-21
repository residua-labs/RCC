import RCCTests.AddressResolution

/-! RCC-98 candidate: addressed-store resolution and runtime codec binding. -/

namespace Residua.RCC.RCC98Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressResolution.Tests

def emptyResolveRefused := resolve_empty_is_not_found
def wrongKeyResolveRefused := resolve_wrong_key_is_rehash_mismatch
def decodeRefusalExplicit := resolve_decode_refusal_is_explicit
def noncanonicalBytesRefused := resolve_malleable_bytes_are_noncanonical
def honestResolveReturnsClass := resolve_honest_codec_returns_expected_class
def maliciousOperationalResolutionRefused :=
  malicious_operational_resolution_is_not_semantic_sound
def requestedAddressPinned := requested_is_expected_address
def noRefinementCountermodel := no_refinement_countermodel_contract

theorem resolvedContract (actual : Nat) :
    resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual ↔
      ∃ fetchedBytes,
        validStore requested = some fetchedBytes ∧
        identityBinding.address fetchedBytes = requested ∧
        honestCodec.decode fetchedBytes = some actual ∧
        honestCodec.encode actual = fetchedBytes :=
  resolve_addressed_resolved_contract actual

theorem exactSoundContract
    (actual : Nat)
    (injective : DigestInjectiveOnCanonicalRange identityBinding)
    (resolved :
      resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual) :
    actual = 1 :=
  resolve_addressed_exact_sound_contract actual injective resolved

theorem putThenResolveExact (expected : Nat) :
    resolveAddressed
        identityBinding
        honestCodec
        (putAddressed
          identityBinding (fun _ => none) (exactNatCodec.encode expected)).store
        (identityBinding.address (exactNatCodec.encode expected)) =
      .resolved expected :=
  put_empty_then_resolve_exact_contract expected

abbrev EmptyResolveRefused : Prop :=
  resolveAddressed identityBinding honestCodec emptyStore requested = .notFound
abbrev WrongKeyResolveRefused : Prop :=
  resolveAddressed identityBinding honestCodec wrongKeyStore requested =
    .rehashMismatch
abbrev DecodeRefusalExplicit : Prop :=
  resolveAddressed identityBinding refusingCodec validStore requested =
    .decodeRefused
abbrev NoncanonicalBytesRefused : Prop :=
  resolveAddressed identityBinding malleableCodec validStore requested =
    .noncanonicalBytes
abbrev HonestResolveReturnsClass : Prop :=
  resolveAddressed identityBinding honestCodec validStore requested = .resolved 1
abbrev MaliciousOperationalResolutionRefused : Prop :=
  resolveAddressed identityBinding malleableCodec zeroStore zeroRequested =
    .resolved 1
abbrev RequestedAddressPinned : Prop :=
  requested = identityBinding.address (exactNatCodec.encode 1) ∧
    resolveAddressed identityBinding honestCodec validStore requested =
      .resolved 1
abbrev NoRefinementCountermodel : Prop :=
  ∃ (binding : DigestBinding .value Nat (DigestPreimage Nat))
    (exact : ExactCanonicalCodec Nat Nat)
    (runtime : RuntimeCanonicalCodec Nat Nat)
    (store : AddressedStore .value Nat)
    (requested : Address .value),
    resolveAddressed binding runtime store requested = .resolved 1 ∧
    requested = binding.address (exact.encode 0) ∧
    (1 : Nat) ≠ 0 ∧
    ¬ RuntimeCanonicalCodec.RefinesExact runtime exact
abbrev ResolvedContract : Prop :=
  ∀ actual : Nat,
    resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual ↔
      ∃ fetchedBytes,
        validStore requested = some fetchedBytes ∧
        identityBinding.address fetchedBytes = requested ∧
        honestCodec.decode fetchedBytes = some actual ∧
        honestCodec.encode actual = fetchedBytes
abbrev ExactSoundContract : Prop :=
  ∀ (actual : Nat)
    (injective : DigestInjectiveOnCanonicalRange identityBinding)
    (resolved :
      resolveAddressed identityBinding honestCodec validStore requested =
        .resolved actual),
    actual = 1
abbrev PutThenResolveExact : Prop :=
  ∀ expected : Nat,
    resolveAddressed
        identityBinding
        honestCodec
        (putAddressed
          identityBinding (fun _ => none) (exactNatCodec.encode expected)).store
        (identityBinding.address (exactNatCodec.encode expected)) =
      .resolved expected

structure Certificate where
  emptyResolveRefused : EmptyResolveRefused
  wrongKeyResolveRefused : WrongKeyResolveRefused
  decodeRefusalExplicit : DecodeRefusalExplicit
  noncanonicalBytesRefused : NoncanonicalBytesRefused
  honestResolveReturnsClass : HonestResolveReturnsClass
  maliciousOperationalResolutionRefused : MaliciousOperationalResolutionRefused
  requestedAddressPinned : RequestedAddressPinned
  noRefinementCountermodel : NoRefinementCountermodel
  resolvedContract : ResolvedContract
  exactSoundContract : ExactSoundContract
  putThenResolveExact : PutThenResolveExact

def certificate : Certificate where
  emptyResolveRefused := resolve_empty_is_not_found
  wrongKeyResolveRefused := resolve_wrong_key_is_rehash_mismatch
  decodeRefusalExplicit := resolve_decode_refusal_is_explicit
  noncanonicalBytesRefused := resolve_malleable_bytes_are_noncanonical
  honestResolveReturnsClass := resolve_honest_codec_returns_expected_class
  maliciousOperationalResolutionRefused :=
    malicious_operational_resolution_is_not_semantic_sound
  requestedAddressPinned :=
    ⟨requested_is_expected_address, resolve_honest_codec_returns_expected_class⟩
  noRefinementCountermodel := no_refinement_countermodel_contract
  resolvedContract := resolvedContract
  exactSoundContract := exactSoundContract
  putThenResolveExact := putThenResolveExact

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC98Target


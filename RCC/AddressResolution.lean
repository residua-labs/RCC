import RCC.DigestBinding

/-!
# RCC faithful addressed store resolution

This module defines the logical byte store, collision-aware insertion kernel,
and total resolver.  Resolution treats fetched bytes and the runtime codec as
untrusted: it rehashes, decodes, and re-encodes before returning an object.
-/

namespace Residua.RCC.Addressing

universe u v

/-- A logical store has one optional byte value at each full typed address. -/
abbrev AddressedStore
    (kind : AddressKind) (Bytes : Type u) :=
  Address kind → Option Bytes

/-- The logical store with no occupied addresses. -/
def emptyAddressedStore : AddressedStore kind Bytes :=
  fun _ => none

/-- Replace exactly one full typed-address slot. -/
def updateAddressedStore
    (store : AddressedStore kind Bytes)
    (target : Address kind)
    (bytes : Bytes) :
    AddressedStore kind Bytes :=
  fun requested =>
    if requested = target then some bytes else store requested

@[simp] theorem update_addressed_store_target
    (store : AddressedStore kind Bytes)
    (target : Address kind)
    (bytes : Bytes) :
    updateAddressedStore store target bytes target = some bytes := by
  simp [updateAddressedStore]

theorem update_addressed_store_non_target
    (store : AddressedStore kind Bytes)
    (target requested : Address kind)
    (bytes : Bytes)
    (different : requested ≠ target) :
    updateAddressedStore store target bytes requested = store requested := by
  simp [updateAddressedStore, different]

/-- The exhaustive operational outcome of attempting an addressed put. -/
inductive StorePutDisposition
  | inserted
  | reused
  | occupiedSlotCorrupt
  | collision
  deriving DecidableEq, Repr

/-- A put returns both the resulting logical store and its disposition. -/
structure StorePutOutcome
    (kind : AddressKind) (Bytes : Type u) where
  store : AddressedStore kind Bytes
  disposition : StorePutDisposition

/-- The operational encoder and partial decoder used during store resolution. -/
structure RuntimeCanonicalCodec
    (Class : Type u) (Bytes : Type v) where
  encode : Class → Bytes
  decode : Bytes → Option Class

/--
Evidence that both runtime codec operations are exactly the AK-2 operations.
-/
structure RuntimeCanonicalCodec.RefinesExact
    (runtime : RuntimeCanonicalCodec Class Bytes)
    (exact : ExactCanonicalCodec Class Bytes) : Prop where
  encode_eq : runtime.encode = exact.encode
  decode_eq : runtime.decode = exact.decode

/-- Exhaustive result of validating and decoding one addressed store slot. -/
inductive StoreResolveResult (Class : Type u)
  | resolved : Class → StoreResolveResult Class
  | notFound
  | rehashMismatch
  | decodeRefused
  | noncanonicalBytes
  deriving DecidableEq, Repr

/--
Resolve only after checking slot presence, byte rehash, decode acceptance, and
exact byte equality after re-encoding, in that order.
-/
def resolveAddressed [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (codec : RuntimeCanonicalCodec Class Bytes)
    (store : AddressedStore kind Bytes)
    (requested : Address kind) :
    StoreResolveResult Class :=
  match store requested with
  | none => .notFound
  | some bytes =>
      if binding.address bytes = requested then
        match codec.decode bytes with
        | none => .decodeRefused
        | some object =>
            if codec.encode object = bytes then
              .resolved object
            else
              .noncanonicalBytes
      else
        .rehashMismatch

/-- A resolved result carries every successful validation check as evidence. -/
theorem resolve_addressed_eq_resolved_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (codec : RuntimeCanonicalCodec Class Bytes)
    (store : AddressedStore kind Bytes)
    (requested : Address kind)
    (object : Class) :
    resolveAddressed binding codec store requested = .resolved object ↔
      ∃ bytes,
        store requested = some bytes ∧
        binding.address bytes = requested ∧
        codec.decode bytes = some object ∧
        codec.encode object = bytes := by
  cases found : store requested with
  | none =>
      simp [resolveAddressed, found]
  | some bytes =>
      by_cases rehashed : binding.address bytes = requested
      · cases decoded : codec.decode bytes with
        | none =>
            simp [resolveAddressed, found, rehashed, decoded]
        | some decodedObject =>
            by_cases reencoded : codec.encode decodedObject = bytes
            · simp [resolveAddressed, found, rehashed, decoded, reencoded]
              intro equalObject
              cases equalObject
              exact reencoded
            · simp [resolveAddressed, found, rehashed, decoded, reencoded]
              intro equalObject
              cases equalObject
              exact reencoded
      · simp [resolveAddressed, found, rehashed]

/-- Compatibility name for the resolved-result certificate. -/
theorem resolve_addressed_resolved_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (codec : RuntimeCanonicalCodec Class Bytes)
    (store : AddressedStore kind Bytes)
    (requested : Address kind)
    (object : Class) :
    resolveAddressed binding codec store requested = .resolved object ↔
      ∃ bytes,
        store requested = some bytes ∧
        binding.address bytes = requested ∧
        codec.decode bytes = some object ∧
        codec.encode object = bytes :=
  resolve_addressed_eq_resolved_iff binding codec store requested object

/--
Under exact runtime refinement and the explicit digest-injectivity premise, a
resolved object is the unique AK-2 class expected at the requested address.
-/
theorem resolve_addressed_exact_sound [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (exact : ExactCanonicalCodec Class Bytes)
    (runtime : RuntimeCanonicalCodec Class Bytes)
    (refinement : RuntimeCanonicalCodec.RefinesExact runtime exact)
    (injective : DigestInjectiveOnCanonicalRange binding)
    (store : AddressedStore kind Bytes)
    (requested : Address kind)
    (expected actual : Class)
    (requestedIsExpected :
      requested = binding.address (exact.encode expected))
    (resolved :
      resolveAddressed binding runtime store requested = .resolved actual) :
    actual = expected := by
  rcases
      (resolve_addressed_eq_resolved_iff
        binding runtime store requested actual).1 resolved with
    ⟨bytes, _found, rehashed, _decoded, reencoded⟩
  have equalAddress :
      binding.address bytes = binding.address (exact.encode expected) :=
    rehashed.trans requestedIsExpected
  have equalBytes : bytes = exact.encode expected :=
    (digest_address_eq_iff_bytes_eq
      binding injective bytes (exact.encode expected)).1 equalAddress
  have refinedEncoding :
      runtime.encode actual = exact.encode actual :=
    congrFun refinement.encode_eq actual
  have equalCanonical :
      exact.encode actual = exact.encode expected :=
    refinedEncoding.symm.trans (reencoded.trans equalBytes)
  exact canonical_encode_injective exact equalCanonical

/--
Insert canonical bytes at their derived typed address.

The checks are deliberately ordered: empty slot, corrupt occupied slot, exact
complete-preimage reuse, then same-address/different-preimage collision.
-/
def putAddressed [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    StorePutOutcome kind Bytes :=
  match store (binding.address proposedBytes) with
  | none =>
      ⟨updateAddressedStore
        store (binding.address proposedBytes) proposedBytes, .inserted⟩
  | some storedBytes =>
      if binding.address storedBytes = binding.address proposedBytes then
        if binding.preimage storedBytes = binding.preimage proposedBytes then
          ⟨store, .reused⟩
        else
          ⟨store, .collision⟩
      else
        ⟨store, .occupiedSlotCorrupt⟩

theorem put_addressed_eq_inserted_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .inserted ↔
      store (binding.address proposedBytes) = none := by
  cases stored : store (binding.address proposedBytes) with
  | none =>
      simp [putAddressed, stored]
  | some storedBytes =>
      by_cases equalAddress :
          binding.address storedBytes = binding.address proposedBytes
      · by_cases equalPreimage :
          binding.preimage storedBytes = binding.preimage proposedBytes
        · simp [putAddressed, stored, equalAddress, equalPreimage]
        · simp [putAddressed, stored, equalAddress, equalPreimage]
      · simp [putAddressed, stored, equalAddress]

theorem put_addressed_inserted_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .inserted ↔
      store (binding.address proposedBytes) = none :=
  put_addressed_eq_inserted_iff binding store proposedBytes

/-- An inserted payload is durable at the address it was derived from. -/
theorem put_inserted_writes_target [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes)
    (inserted :
      (putAddressed binding store proposedBytes).disposition = .inserted) :
    (putAddressed binding store proposedBytes).store
        (binding.address proposedBytes) = some proposedBytes := by
  have emptySlot :=
    (put_addressed_eq_inserted_iff binding store proposedBytes).1 inserted
  simp [putAddressed, emptySlot, update_addressed_store_target]

theorem put_addressed_eq_reused_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .reused ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes = binding.address proposedBytes ∧
        binding.preimage storedBytes = binding.preimage proposedBytes := by
  cases stored : store (binding.address proposedBytes) with
  | none =>
      simp [putAddressed, stored]
  | some storedBytes =>
      by_cases equalAddress :
          binding.address storedBytes = binding.address proposedBytes
      · by_cases equalPreimage :
          binding.preimage storedBytes = binding.preimage proposedBytes
        · simp [putAddressed, stored, equalAddress, equalPreimage]
        · simp [putAddressed, stored, equalAddress, equalPreimage]
      · simp [putAddressed, stored, equalAddress]

theorem put_addressed_reused_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .reused ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes = binding.address proposedBytes ∧
        binding.preimage storedBytes = binding.preimage proposedBytes :=
  put_addressed_eq_reused_iff binding store proposedBytes

theorem put_addressed_eq_occupied_slot_corrupt_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition =
        .occupiedSlotCorrupt ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes ≠ binding.address proposedBytes := by
  cases stored : store (binding.address proposedBytes) with
  | none =>
      simp [putAddressed, stored]
  | some storedBytes =>
      by_cases equalAddress :
          binding.address storedBytes = binding.address proposedBytes
      · by_cases equalPreimage :
          binding.preimage storedBytes = binding.preimage proposedBytes
        · simp [putAddressed, stored, equalAddress, equalPreimage]
        · simp [putAddressed, stored, equalAddress, equalPreimage]
      · simp [putAddressed, stored, equalAddress]

theorem put_addressed_occupied_slot_corrupt_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition =
        .occupiedSlotCorrupt ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes ≠ binding.address proposedBytes :=
  put_addressed_eq_occupied_slot_corrupt_iff binding store proposedBytes

theorem put_addressed_eq_collision_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .collision ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes = binding.address proposedBytes ∧
        binding.preimage storedBytes ≠ binding.preimage proposedBytes := by
  cases stored : store (binding.address proposedBytes) with
  | none =>
      simp [putAddressed, stored]
  | some storedBytes =>
      by_cases equalAddress :
          binding.address storedBytes = binding.address proposedBytes
      · by_cases equalPreimage :
          binding.preimage storedBytes = binding.preimage proposedBytes
        · simp [putAddressed, stored, equalAddress, equalPreimage]
        · simp [putAddressed, stored, equalAddress, equalPreimage]
      · simp [putAddressed, stored, equalAddress]

theorem put_addressed_collision_iff [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes) :
    (putAddressed binding store proposedBytes).disposition = .collision ↔
      ∃ storedBytes,
        store (binding.address proposedBytes) = some storedBytes ∧
        binding.address storedBytes = binding.address proposedBytes ∧
        binding.preimage storedBytes ≠ binding.preimage proposedBytes :=
  put_addressed_eq_collision_iff binding store proposedBytes

theorem put_reused_preserves_store [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes)
    (reused :
      (putAddressed binding store proposedBytes).disposition = .reused) :
    (putAddressed binding store proposedBytes).store = store := by
  rcases
      (put_addressed_eq_reused_iff binding store proposedBytes).1 reused with
    ⟨storedBytes, found, equalAddress, equalPreimage⟩
  simp [putAddressed, found, equalAddress, equalPreimage]

theorem put_corrupt_slot_preserves_store [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes)
    (corrupt :
      (putAddressed binding store proposedBytes).disposition =
        .occupiedSlotCorrupt) :
    (putAddressed binding store proposedBytes).store = store := by
  rcases
      (put_addressed_eq_occupied_slot_corrupt_iff
        binding store proposedBytes).1 corrupt with
    ⟨storedBytes, found, unequalAddress⟩
  simp [putAddressed, found, unequalAddress]

theorem put_collision_preserves_store [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (store : AddressedStore kind Bytes)
    (proposedBytes : Bytes)
    (collision :
      (putAddressed binding store proposedBytes).disposition = .collision) :
    (putAddressed binding store proposedBytes).store = store := by
  rcases
      (put_addressed_eq_collision_iff binding store proposedBytes).1 collision with
    ⟨storedBytes, found, equalAddress, unequalPreimage⟩
  simp [putAddressed, found, equalAddress, unequalPreimage]

/--
Putting an exact encoding into the empty logical store and resolving its
derived address succeeds without any digest-injectivity assumption.
-/
theorem put_empty_then_resolve_exact [DecidableEq Bytes]
    (binding : DigestBinding kind Bytes Wire)
    (exact : ExactCanonicalCodec Class Bytes)
    (runtime : RuntimeCanonicalCodec Class Bytes)
    (refinement : RuntimeCanonicalCodec.RefinesExact runtime exact)
    (expected : Class) :
    resolveAddressed
        binding
        runtime
        (putAddressed
          binding emptyAddressedStore (exact.encode expected)).store
        (binding.address (exact.encode expected)) =
      .resolved expected := by
  simp only [putAddressed, emptyAddressedStore]
  simp only [resolveAddressed]
  rw [update_addressed_store_target]
  simp only [
    refinement.decode_eq,
    refinement.encode_eq,
    exact.decode_encode
  ]
  simp

/--
Concrete positive countermodel: operational rehash/decode/re-encode agreement
can resolve an object distinct from the AK-2 object when refinement is absent.
-/
theorem operational_resolution_without_codec_refinement_is_not_semantic_sound :
    ∃ (binding : DigestBinding .value Nat (DigestPreimage Nat))
      (exact : ExactCanonicalCodec Nat Nat)
      (runtime : RuntimeCanonicalCodec Nat Nat)
      (store : AddressedStore .value Nat)
      (requested : Address .value),
        resolveAddressed binding runtime store requested = .resolved 1 ∧
        requested = binding.address (exact.encode 0) ∧
        (1 : Nat) ≠ 0 ∧
        ¬ RuntimeCanonicalCodec.RefinesExact runtime exact := by
  let frame : ExactFrame Nat (DigestPreimage Nat) := {
    encode := fun preimage => preimage
    encode_injective := by
      intro left right equal
      exact equal
  }
  let binding : DigestBinding .value Nat (DigestPreimage Nat) := {
    algorithm := ⟨"countermodel"⟩
    domainQ := ⟨"residua:countermodel"⟩
    schemaQ := ⟨"residua:countermodel:v1"⟩
    frame := frame
    hash := fun _ => ⟨"constant-digest"⟩
  }
  let exactCodec : ExactCanonicalCodec Nat Nat := {
    encode := fun value => value
    decode := fun bytes => some bytes
    decode_encode := by
      intro value
      rfl
    encode_decode_canonical := by
      intro bytes value accepted
      exact (Option.some.inj accepted).symm
  }
  let runtimeCodec : RuntimeCanonicalCodec Nat Nat := {
    encode := fun _ => 0
    decode := fun _ => some 1
  }
  let store : AddressedStore .value Nat := fun _ => some 0
  let requested := binding.address (exactCodec.encode 0)
  refine
    ⟨binding, exactCodec, runtimeCodec, store, requested, ?_⟩
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · decide
  · intro refinement
    have equalEncoding := congrFun refinement.encode_eq 1
    change (0 : Nat) = 1 at equalEncoding
    exact (by decide : (0 : Nat) ≠ 1) equalEncoding

end Residua.RCC.Addressing

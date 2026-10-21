import RCC.CanonicalCodec

/-!
# RCC domain-separated digest binding

This Prelude-only module discharges AK-3's structural digest-binding floor.
The hashed preimage contains the address kind, digest algorithm, quotient
domain, canonical schema, and canonical bytes.  A binding may use only an
injective frame, so no ambiguous raw concatenation can be certified.

Digest injectivity is deliberately not asserted.  Exact address theorems take
`DigestInjectiveOnCanonicalRange` as an explicit premise.  Without that
premise, `inspectAddressed` compares the complete framed preimage and refuses a
same-address/different-preimage collision instead of choosing either value.

This module does not prove a concrete serialization refines `ExactFrame`, SHA
collision freedom, durable store resolution, or schema migration.
-/

namespace Residua.RCC.Addressing

universe u v

/--
The complete semantic preimage committed to by a typed address.

`canonicalBytes` alone is not an address identity: kind, algorithm, domain,
and schema separation are part of the commitment.
-/
structure DigestPreimage (Bytes : Type u) where
  kind : AddressKind
  algorithm : AlgorithmId
  domainQ : DomainQ
  schemaQ : SchemaQ
  canonicalBytes : Bytes
  deriving DecidableEq, Repr

/--
An unambiguous structural frame for digest inputs.

A runtime byte serializer may inhabit this structure only after proving that
equal wire values imply equal complete preimages.
-/
structure ExactFrame (Bytes : Type u) (Wire : Type v) where
  encode : DigestPreimage Bytes → Wire
  encode_injective :
    ∀ {left right}, encode left = encode right → left = right

/--
A typed, domain- and schema-separated digest construction.

The address kind is a type parameter, preventing a value address from being
silently passed as an occurrence address.
-/
structure DigestBinding
    (kind : AddressKind) (Bytes : Type u) (Wire : Type v) where
  algorithm : AlgorithmId
  domainQ : DomainQ
  schemaQ : SchemaQ
  frame : ExactFrame Bytes Wire
  hash : Wire → Digest

/-- Construct the complete preimage certified by a binding. -/
def DigestBinding.preimage
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    DigestPreimage Bytes where
  kind := kind
  algorithm := binding.algorithm
  domainQ := binding.domainQ
  schemaQ := binding.schemaQ
  canonicalBytes := bytes

@[simp] theorem DigestBinding.preimage_kind
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.preimage bytes).kind = kind := by
  rfl

@[simp] theorem DigestBinding.preimage_algorithm
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.preimage bytes).algorithm = binding.algorithm := by
  rfl

@[simp] theorem DigestBinding.preimage_domainQ
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.preimage bytes).domainQ = binding.domainQ := by
  rfl

@[simp] theorem DigestBinding.preimage_schemaQ
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.preimage bytes).schemaQ = binding.schemaQ := by
  rfl

@[simp] theorem DigestBinding.preimage_canonicalBytes
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.preimage bytes).canonicalBytes = bytes := by
  rfl

/-- Encode the complete preimage through the certified exact frame. -/
def DigestBinding.framedWire
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) : Wire :=
  binding.frame.encode (binding.preimage bytes)

/-- Derive the only certified typed address envelope for these bytes. -/
def DigestBinding.address
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) : Address kind where
  algorithm := binding.algorithm
  domainQ := binding.domainQ
  schemaQ := binding.schemaQ
  digest := binding.hash (binding.framedWire bytes)

@[simp] theorem DigestBinding.address_algorithm
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.address bytes).algorithm = binding.algorithm := by
  rfl

@[simp] theorem DigestBinding.address_domainQ
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.address bytes).domainQ = binding.domainQ := by
  rfl

@[simp] theorem DigestBinding.address_schemaQ
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.address bytes).schemaQ = binding.schemaQ := by
  rfl

@[simp] theorem DigestBinding.address_digest
    (binding : DigestBinding kind Bytes Wire) (bytes : Bytes) :
    (binding.address bytes).digest =
      binding.hash (binding.framedWire bytes) := by
  rfl

/--
Canonical bytes carried together with the binding that commits to them.

Construction of this object derives all address metadata from `binding`;
callers cannot independently choose a mismatched envelope.
-/
structure AddressedCanonical
    (binding : DigestBinding kind Bytes Wire) where
  canonicalBytes : Bytes

/-- Recover the complete certified preimage. -/
def AddressedCanonical.preimage
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) : DigestPreimage Bytes :=
  binding.preimage object.canonicalBytes

/-- Recover the exact framed digest input. -/
def AddressedCanonical.framedWire
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) : Wire :=
  binding.framedWire object.canonicalBytes

/-- Recover the certified typed address. -/
def AddressedCanonical.address
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) : Address kind :=
  binding.address object.canonicalBytes

/--
An `AddressedCanonical` carries no caller-supplied envelope: its address is
definitionally the one derived by its binding.
-/
theorem AddressedCanonical.address_is_derived
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) :
    object.address = binding.address object.canonicalBytes := by
  rfl

@[simp] theorem AddressedCanonical.address_algorithm
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) :
    object.address.algorithm = binding.algorithm := by
  rfl

@[simp] theorem AddressedCanonical.address_domainQ
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) :
    object.address.domainQ = binding.domainQ := by
  rfl

@[simp] theorem AddressedCanonical.address_schemaQ
    {binding : DigestBinding kind Bytes Wire}
    (object : AddressedCanonical binding) :
    object.address.schemaQ = binding.schemaQ := by
  rfl

/--
The conditional cryptographic premise used by address-exactness theorems.

It is scoped to the framed canonical range of this binding.  Concrete digest
algorithms must prove or explicitly assume it elsewhere.
-/
def DigestInjectiveOnCanonicalRange
    (binding : DigestBinding kind Bytes Wire) : Prop :=
  ∀ {left right},
    binding.hash (binding.framedWire left) =
        binding.hash (binding.framedWire right) →
      binding.framedWire left = binding.framedWire right

/-- Under the explicit injectivity premise, address equality is byte equality. -/
theorem digest_address_eq_iff_bytes_eq
    (binding : DigestBinding kind Bytes Wire)
    (injective : DigestInjectiveOnCanonicalRange binding)
    (left right : Bytes) :
    binding.address left = binding.address right ↔ left = right := by
  constructor
  · intro equalAddress
    have equalDigest :
        binding.hash (binding.framedWire left) =
          binding.hash (binding.framedWire right) :=
      congrArg Address.digest equalAddress
    have equalWire := injective equalDigest
    have equalPreimage := binding.frame.encode_injective equalWire
    exact congrArg DigestPreimage.canonicalBytes equalPreimage
  · intro equalBytes
    cases equalBytes
    rfl

/-- Address an object only after quotient abstraction and exact encoding. -/
def canonicalObjectAddress {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context)
    (codec :
      ExactCanonicalCodec
        (Quotient (domain.setoid adequate context)) Bytes)
    (binding : DigestBinding kind Bytes Wire)
    (object : domain.Object) : Address kind :=
  binding.address (canonicalBytes domain adequate context codec object)

/--
AK-2 + AK-3: under the explicit digest premise, concrete typed address
equality is exactly the declared abstract quotient relation.
-/
theorem canonical_object_address_eq_iff_equivalent {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context)
    (codec :
      ExactCanonicalCodec
        (Quotient (domain.setoid adequate context)) Bytes)
    (binding : DigestBinding kind Bytes Wire)
    (injective : DigestInjectiveOnCanonicalRange binding)
    (left right : domain.Object) :
    canonicalObjectAddress domain adequate context codec binding left =
        canonicalObjectAddress domain adequate context codec binding right ↔
      domain.equivalent context left right := by
  exact
    (digest_address_eq_iff_bytes_eq
      binding injective
      (canonicalBytes domain adequate context codec left)
      (canonicalBytes domain adequate context codec right)).trans
        (canonical_bytes_eq_iff_equivalent
          domain adequate context codec left right)

/-- Operational disposition for comparing an existing and proposed entry. -/
inductive AddressLookupDisposition
  | miss
  | reuse
  | collision
  deriving DecidableEq, Repr

/--
Inspect an address hit without assuming digest injectivity.

`reuse` requires both typed-address equality and complete-preimage equality.
A same-address/different-preimage hit is an explicit collision refusal.
-/
def inspectAddressed [DecidableEq Bytes]
    {binding : DigestBinding kind Bytes Wire}
    (stored proposed : AddressedCanonical binding) :
    AddressLookupDisposition :=
  if stored.address = proposed.address then
    if stored.preimage = proposed.preimage then
      .reuse
    else
      .collision
  else
    .miss

theorem inspect_addressed_eq_miss_iff [DecidableEq Bytes]
    {binding : DigestBinding kind Bytes Wire}
    (stored proposed : AddressedCanonical binding) :
    inspectAddressed stored proposed = .miss ↔
      stored.address ≠ proposed.address := by
  by_cases equalAddress : stored.address = proposed.address
  · by_cases equalPreimage : stored.preimage = proposed.preimage
    · simp [inspectAddressed, equalAddress, equalPreimage]
    · simp [inspectAddressed, equalAddress, equalPreimage]
  · simp [inspectAddressed, equalAddress]

theorem inspect_addressed_eq_reuse_iff [DecidableEq Bytes]
    {binding : DigestBinding kind Bytes Wire}
    (stored proposed : AddressedCanonical binding) :
    inspectAddressed stored proposed = .reuse ↔
      stored.address = proposed.address ∧
        stored.preimage = proposed.preimage := by
  by_cases equalAddress : stored.address = proposed.address
  · by_cases equalPreimage : stored.preimage = proposed.preimage
    · simp [inspectAddressed, equalAddress, equalPreimage]
    · simp [inspectAddressed, equalAddress, equalPreimage]
  · simp [inspectAddressed, equalAddress]

theorem inspect_addressed_eq_collision_iff [DecidableEq Bytes]
    {binding : DigestBinding kind Bytes Wire}
    (stored proposed : AddressedCanonical binding) :
    inspectAddressed stored proposed = .collision ↔
      stored.address = proposed.address ∧
        stored.preimage ≠ proposed.preimage := by
  by_cases equalAddress : stored.address = proposed.address
  · by_cases equalPreimage : stored.preimage = proposed.preimage
    · simp [inspectAddressed, equalAddress, equalPreimage]
    · simp [inspectAddressed, equalAddress, equalPreimage]
  · simp [inspectAddressed, equalAddress]

end Residua.RCC.Addressing

import RCC.DefeqNormalFormCodec

/-!
# RCC typed, framed, context-bound defeq address

This file establishes DQ-7 for the supported `num`/`add` fragment.  It binds
the exact DQ-6 normal-form bytes into a typed semantic address whose digest
preimage also contains:

* the digest algorithm coordinate;
* a dedicated defeq domain coordinate;
* the canonical schema coordinate; and
* the semantic context coordinate.

Every variable-length field uses a tagged length frame.  The frame has an
executable left inverse, so changes to context or canonical normal-form bytes
cannot disappear before the digest boundary.

The digest operation is deliberately an explicit parameter.  No injectivity,
collision resistance, or DQ-8 address-exactness theorem is asserted here.
Raw unsupported terms remain at the DQ-1 typed-residue boundary.
-/

namespace Residua.RCC.DefeqTypedAddress

open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqExactness
open Residua.RCC.DefeqNormalFormCodec

/-! ## Typed profile and canonical framing coordinates -/

/-- Byte carrier used only for digest preimages.  `Nat` keeps the framing
proof independent of a particular octet/string implementation. -/
abbrev PreimageBytes := List Nat

/-- A nominal digest algorithm.  Its framed bytes are derived from `id`; a
caller cannot pair one address identifier with unrelated committed bytes. -/
structure AlgorithmCoordinate where
  id : AlgorithmId
  deriving DecidableEq, Repr

/-- A nominal quotient domain. -/
structure DomainCoordinate where
  id : DomainQ
  deriving DecidableEq, Repr

/-- A nominal canonical schema. -/
structure SchemaCoordinate where
  id : SchemaQ
  deriving DecidableEq, Repr

/-- The unique UTF-8 byte representation of a nominal coordinate. -/
def coordinateBytes (value : String) : PreimageBytes :=
  (String.toUTF8 value).data.toList.map UInt8.toNat

def AlgorithmCoordinate.canonicalBytes
    (coordinate : AlgorithmCoordinate) : PreimageBytes :=
  coordinateBytes coordinate.id.value

def DomainCoordinate.canonicalBytes
    (coordinate : DomainCoordinate) : PreimageBytes :=
  coordinateBytes coordinate.id.value

def SchemaCoordinate.canonicalBytes
    (coordinate : SchemaCoordinate) : PreimageBytes :=
  coordinateBytes coordinate.id.value

/-- The semantic context identity is proof-relevant input to a defeq
judgment address.  It is not ambient process state. -/
structure ContextSemanticQ where
  canonicalBytes : PreimageBytes
  deriving DecidableEq, Repr

/-- The complete typed profile for the DQ-7 address surface.  Its result kind
is statically fixed to `AddressKind.semantic`. -/
structure DefeqAddressProfile where
  algorithm : AlgorithmCoordinate
  domain : DomainCoordinate
  schema : SchemaCoordinate
  deriving DecidableEq, Repr

/-- The exact semantic material committed before applying a digest. -/
structure DefeqFramedPreimage where
  contextSemanticQ : ContextSemanticQ
  canonicalNormalFormBytes : PreimageBytes
  deriving DecidableEq, Repr

/-! ## Unambiguous tagged length framing -/

private def algorithmTag : Nat := 1
private def domainTag : Nat := 2
private def schemaTag : Nat := 3
private def contextTag : Nat := 4
private def normalFormTag : Nat := 5

/-- A field is framed by its tag and exact payload length. -/
def frameField
    (tag : Nat) (payload : PreimageBytes) : PreimageBytes :=
  tag :: payload.length :: payload

/-- Read exactly one field with the expected tag. -/
def readField
    (expectedTag : Nat) :
    PreimageBytes → Option (PreimageBytes × PreimageBytes)
  | tag :: payloadLength :: rest =>
      if tag = expectedTag then
        if payloadLength ≤ rest.length then
          some (rest.take payloadLength, rest.drop payloadLength)
        else
          none
      else
        none
  | _ =>
      none

/-- The field reader is a left inverse of tagged length framing, even in the
presence of an arbitrary following suffix. -/
@[simp]
theorem readField_frameField
    (tag : Nat)
    (payload suffix : PreimageBytes) :
    readField tag (frameField tag payload ++ suffix) =
      some (payload, suffix) := by
  simp [frameField, readField]

/-- DQ-6 octets embedded losslessly into the preimage byte carrier. -/
def canonicalNormalFormBytes
    (term : NumAddTerm) : PreimageBytes :=
  (encode (normalize term)).map UInt8.toNat

/-- The exact five-field digest preimage. -/
def framedBytes
    (profile : DefeqAddressProfile)
    (preimage : DefeqFramedPreimage) : PreimageBytes :=
  frameField algorithmTag profile.algorithm.canonicalBytes ++
    frameField domainTag profile.domain.canonicalBytes ++
    frameField schemaTag profile.schema.canonicalBytes ++
    frameField contextTag preimage.contextSemanticQ.canonicalBytes ++
    frameField normalFormTag preimage.canonicalNormalFormBytes

/-- Decode only the exact profile-specific five-field grammar. -/
def decodeFramedBytes
    (profile : DefeqAddressProfile)
    (bytes : PreimageBytes) : Option DefeqFramedPreimage := do
  let (algorithmBytes, afterAlgorithm) ← readField algorithmTag bytes
  if algorithmBytes ≠ profile.algorithm.canonicalBytes then
    none
  else
    let (domainBytes, afterDomain) ← readField domainTag afterAlgorithm
    if domainBytes ≠ profile.domain.canonicalBytes then
      none
    else
      let (schemaBytes, afterSchema) ← readField schemaTag afterDomain
      if schemaBytes ≠ profile.schema.canonicalBytes then
        none
      else
        let (contextBytes, afterContext) ←
          readField contextTag afterSchema
        let (normalFormBytes, suffix) ←
          readField normalFormTag afterContext
        if suffix ≠ [] then
          none
        else
          some
            { contextSemanticQ := ⟨contextBytes⟩
              canonicalNormalFormBytes := normalFormBytes }

/-- The five-field decoder replays every canonical DQ-7 preimage exactly. -/
@[simp]
theorem decode_framedBytes
    (profile : DefeqAddressProfile)
    (preimage : DefeqFramedPreimage) :
    decodeFramedBytes profile (framedBytes profile preimage) =
      some preimage := by
  have finalField :
      readField normalFormTag
          (frameField normalFormTag preimage.canonicalNormalFormBytes) =
        some (preimage.canonicalNormalFormBytes, []) := by
    simpa using
      readField_frameField
        normalFormTag preimage.canonicalNormalFormBytes []
  simp [decodeFramedBytes, framedBytes, finalField]

/-- Tagged framing is injective for a fixed typed profile. -/
theorem framedBytes_injective
    (profile : DefeqAddressProfile)
    {left right : DefeqFramedPreimage}
    (sameBytes :
      framedBytes profile left = framedBytes profile right) :
    left = right := by
  have decodedEqual :=
    congrArg (decodeFramedBytes profile) sameBytes
  simpa using decodedEqual

/-! ## Supported-domain address construction -/

/-- Build the canonical framed preimage for one supported term and context. -/
def preimage
    (context : ContextSemanticQ)
    (term : NumAddTerm) : DefeqFramedPreimage :=
  { contextSemanticQ := context
    canonicalNormalFormBytes := canonicalNormalFormBytes term }

/-- A digest implementation consumes the entire framed preimage.  DQ-7
requires no property of this function. -/
abbrev DigestOperation := PreimageBytes → Digest

/-- A proof-carrying binding between a typed semantic address and the exact
framed bytes supplied to its digest operation. -/
structure DefeqAddressBinding
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : NumAddTerm) where
  framedPreimage : DefeqFramedPreimage
  preimageIsCanonical : framedPreimage = preimage context term
  address : Address .semantic
  algorithmBound : address.algorithm = profile.algorithm.id
  domainBound : address.domainQ = profile.domain.id
  schemaBound : address.schemaQ = profile.schema.id
  digestBound :
    address.digest = digest (framedBytes profile framedPreimage)

/-- Construct the DQ-7 typed address and retain its exact digest binding. -/
def bindAddress
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : NumAddTerm) :
    DefeqAddressBinding profile digest context term :=
  let canonicalPreimage := preimage context term
  { framedPreimage := canonicalPreimage
    preimageIsCanonical := rfl
    address :=
      { algorithm := profile.algorithm.id
        domainQ := profile.domain.id
        schemaQ := profile.schema.id
        digest := digest (framedBytes profile canonicalPreimage) }
    algorithmBound := rfl
    domainBound := rfl
    schemaBound := rfl
    digestBound := rfl }

/-- Defeq-equivalent supported terms have the same canonical DQ-7 preimage
in one semantic context.  This direction uses no digest assumption. -/
theorem equivalent_has_same_preimage
    (context : ContextSemanticQ)
    {left right : NumAddTerm}
    (equivalent : DefEq left right) :
    preimage context left = preimage context right := by
  have sameNormalForm :
      normalize left = normalize right :=
    (normalize_eq_iff_defeq left right).2 equivalent
  unfold preimage canonicalNormalFormBytes
  rw [sameNormalForm]

/-- Context is a load-bearing field: changing it changes the framed
preimage before the digest is applied. -/
theorem context_change_changes_framed_preimage
    (profile : DefeqAddressProfile)
    {leftContext rightContext : ContextSemanticQ}
    (term : NumAddTerm)
    (differentContext : leftContext ≠ rightContext) :
    framedBytes profile (preimage leftContext term) ≠
      framedBytes profile (preimage rightContext term) := by
  intro sameBytes
  have samePreimage :
      preimage leftContext term = preimage rightContext term :=
    framedBytes_injective profile sameBytes
  exact differentContext
    (congrArg DefeqFramedPreimage.contextSemanticQ samePreimage)

/-! ## Raw ingress preserves the DQ-1 unsupported residue -/

/-- Raw callers either receive a typed supported-domain address binding or
the exact DQ-1 unsupported certificate. -/
inductive DefeqAddressIngress
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : Term)
  | addressed :
      (supported : InNumAddFragment term) →
      DefeqAddressBinding profile digest context ⟨term, supported⟩ →
      DefeqAddressIngress profile digest context term
  | unsupported :
      UnsupportedFragmentCert term →
      DefeqAddressIngress profile digest context term

/-- Classify raw input before constructing any digest preimage or address. -/
def bindAddressAtBoundary
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : Term) :
    DefeqAddressIngress profile digest context term :=
  match classifyTerm term with
  | .supported supported =>
      .addressed supported
        (bindAddress profile digest context ⟨term, supported⟩)
  | .unsupported unsupported =>
      .unsupported unsupported

/-- An unsupported raw term keeps its typed residue and never receives an
address, digest, or false inequality judgment. -/
theorem boundary_preserves_unsupported
    (profile : DefeqAddressProfile)
    (digest : DigestOperation)
    (context : ContextSemanticQ)
    (term : Term)
    (unsupported : UnsupportedFragmentCert term)
    (classified : classifyTerm term = .unsupported unsupported) :
    bindAddressAtBoundary profile digest context term =
      .unsupported unsupported := by
  rw [bindAddressAtBoundary, classified]

end Residua.RCC.DefeqTypedAddress

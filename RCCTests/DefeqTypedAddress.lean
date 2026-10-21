import RCC.DefeqTypedAddress

/-!
# Tests and load-bearing mutants for DQ-7

The positive witnesses exercise the typed semantic-address envelope, exact
five-field frame replay, context binding, and the raw unsupported boundary.
The mutants expose four forbidden shortcuts:

* digest-only authority with no retained preimage;
* omission of the defeq domain field;
* omission of the schema field; and
* omission of the semantic context field.

No test assumes digest injectivity or claims DQ-8 address exactness.
-/

namespace Residua.RCC.DefeqTypedAddress.Tests

open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqTypedAddress

/-! ## Frozen test profile -/

def sha256Coordinate : AlgorithmCoordinate :=
  { id := ⟨"sha256"⟩ }

def defeqDomain : DomainCoordinate :=
  { id := ⟨"residua:defeq"⟩ }

def alternateDomain : DomainCoordinate :=
  { id := ⟨"residua:syntax"⟩ }

def defeqSchemaV1 : SchemaCoordinate :=
  { id := ⟨"residua:defeq:v1"⟩ }

def defeqSchemaV2 : SchemaCoordinate :=
  { id := ⟨"residua:defeq:v2"⟩ }

def profileV1 : DefeqAddressProfile :=
  { algorithm := sha256Coordinate
    domain := defeqDomain
    schema := defeqSchemaV1 }

def alternateDomainProfile : DefeqAddressProfile :=
  { algorithm := sha256Coordinate
    domain := alternateDomain
    schema := defeqSchemaV1 }

def profileV2 : DefeqAddressProfile :=
  { algorithm := sha256Coordinate
    domain := defeqDomain
    schema := defeqSchemaV2 }

def contextA : ContextSemanticQ :=
  ⟨[10, 11]⟩

def contextB : ContextSemanticQ :=
  ⟨[10, 12]⟩

def twoTerm : NumAddTerm :=
  ⟨.add (.num 1) (.num 1),
    .add (.num 1) (.num 1)⟩

/-- A deliberately weak digest implementation is sufficient for DQ-7:
the binding theorem records what was digested but does not pretend this
operation is injective. -/
def lengthDigest : DigestOperation :=
  fun bytes => ⟨toString bytes.length⟩

/-! ## Positive witnesses -/

theorem canonical_frame_replays :
    decodeFramedBytes profileV1 (framedBytes profileV1 (preimage contextA twoTerm)) =
      some (preimage contextA twoTerm) := by
  exact decode_framedBytes profileV1 (preimage contextA twoTerm)

theorem typed_address_fields_are_bound :
    let binding := bindAddress profileV1 lengthDigest contextA twoTerm
    binding.address.algorithm = sha256Coordinate.id ∧
      binding.address.domainQ = defeqDomain.id ∧
      binding.address.schemaQ = defeqSchemaV1.id := by
  decide

theorem address_kind_is_semantic :
    (bindAddress profileV1 lengthDigest contextA twoTerm).address =
      ({ algorithm := sha256Coordinate.id
         domainQ := defeqDomain.id
         schemaQ := defeqSchemaV1.id
         digest :=
           lengthDigest
             (framedBytes profileV1 (preimage contextA twoTerm)) } :
        Address .semantic) := by
  rfl

theorem changed_context_changes_preimage :
    framedBytes profileV1 (preimage contextA twoTerm) ≠
      framedBytes profileV1 (preimage contextB twoTerm) := by
  apply context_change_changes_framed_preimage
  decide

theorem unsupported_raw_term_keeps_typed_residue :
    ∃ cert : UnsupportedFragmentCert (.var "outside"),
      bindAddressAtBoundary
          profileV1 lengthDigest contextA (.var "outside") =
        .unsupported cert := by
  cases classified : classifyTerm (.var "outside") with
  | supported supported =>
      cases supported
  | unsupported cert =>
      exact
        ⟨cert,
          boundary_preserves_unsupported
            profileV1 lengthDigest contextA
            (.var "outside") cert classified⟩

/-! ## Mutant 1: a naked digest cannot authorize context substitution -/

/-- Forbidden operation: every preimage is collapsed to one naked digest. -/
def constantDigestMutant : DigestOperation :=
  fun _ => ⟨"constant"⟩

theorem naked_digest_mutant_exposed :
    constantDigestMutant
        (framedBytes profileV1 (preimage contextA twoTerm)) =
      constantDigestMutant
        (framedBytes profileV1 (preimage contextB twoTerm)) ∧
    framedBytes profileV1 (preimage contextA twoTerm) ≠
      framedBytes profileV1 (preimage contextB twoTerm) := by
  exact ⟨rfl, changed_context_changes_preimage⟩

/-! ## Mutant 2: cross-domain framing omission -/

/-- Forbidden preimage: the domain coordinate is absent. -/
def omitDomainMutant
    (profile : DefeqAddressProfile)
    (context : ContextSemanticQ)
    (term : NumAddTerm) : PreimageBytes :=
  profile.algorithm.canonicalBytes ++
    profile.schema.canonicalBytes ++
    context.canonicalBytes ++
    canonicalNormalFormBytes term

theorem cross_domain_omission_mutant_exposed :
    profileV1.domain ≠ alternateDomainProfile.domain ∧
      omitDomainMutant profileV1 contextA twoTerm =
        omitDomainMutant alternateDomainProfile contextA twoTerm := by
  decide

/-! ## Mutant 3: schema framing omission -/

/-- Forbidden preimage: schema version is absent. -/
def omitSchemaMutant
    (profile : DefeqAddressProfile)
    (context : ContextSemanticQ)
    (term : NumAddTerm) : PreimageBytes :=
  profile.algorithm.canonicalBytes ++
    profile.domain.canonicalBytes ++
    context.canonicalBytes ++
    canonicalNormalFormBytes term

theorem schema_omission_mutant_exposed :
    profileV1.schema ≠ profileV2.schema ∧
      omitSchemaMutant profileV1 contextA twoTerm =
        omitSchemaMutant profileV2 contextA twoTerm := by
  decide

/-! ## Mutant 4: semantic-context framing omission -/

/-- Forbidden preimage: semantic context is absent. -/
def omitContextMutant
    (profile : DefeqAddressProfile)
    (_context : ContextSemanticQ)
    (term : NumAddTerm) : PreimageBytes :=
  profile.algorithm.canonicalBytes ++
    profile.domain.canonicalBytes ++
    profile.schema.canonicalBytes ++
    canonicalNormalFormBytes term

theorem context_omission_mutant_exposed :
    contextA ≠ contextB ∧
      omitContextMutant profileV1 contextA twoTerm =
        omitContextMutant profileV1 contextB twoTerm := by
  decide

#print axioms readField_frameField
#print axioms decode_framedBytes
#print axioms framedBytes_injective
#print axioms equivalent_has_same_preimage
#print axioms context_change_changes_framed_preimage
#print axioms boundary_preserves_unsupported
#print axioms naked_digest_mutant_exposed
#print axioms cross_domain_omission_mutant_exposed
#print axioms schema_omission_mutant_exposed
#print axioms context_omission_mutant_exposed

end Residua.RCC.DefeqTypedAddress.Tests

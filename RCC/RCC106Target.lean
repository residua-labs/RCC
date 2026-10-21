import RCCTests.DefeqTypedAddress

/-! RCC-106 candidate: typed defeq address framing and context binding. -/

namespace Residua.RCC.RCC106Target

open Residua.RCC.DefeqTypedAddress.Tests
open Residua.RCC.Addressing
open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqTypedAddress

def canonicalFrameReplays := canonical_frame_replays
def typedAddressFieldsBound := typed_address_fields_are_bound
def addressKindSemantic := address_kind_is_semantic
def changedContextChangesPreimage := changed_context_changes_preimage
def unsupportedRawKeepsTypedResidue := unsupported_raw_term_keeps_typed_residue
def nakedDigestMutantExposed := naked_digest_mutant_exposed
def crossDomainOmissionExposed := cross_domain_omission_mutant_exposed
def schemaOmissionExposed := schema_omission_mutant_exposed
def contextOmissionExposed := context_omission_mutant_exposed


abbrev CanonicalFrameReplays : Prop :=
  decodeFramedBytes profileV1 (framedBytes profileV1 (preimage contextA twoTerm)) =
    some (preimage contextA twoTerm)
abbrev TypedAddressFieldsBound : Prop :=
  let binding := bindAddress profileV1 lengthDigest contextA twoTerm
  binding.address.algorithm = sha256Coordinate.id ∧
    binding.address.domainQ = defeqDomain.id ∧
    binding.address.schemaQ = defeqSchemaV1.id
abbrev AddressKindSemantic : Prop :=
  (bindAddress profileV1 lengthDigest contextA twoTerm).address =
    ({ algorithm := sha256Coordinate.id
       domainQ := defeqDomain.id
       schemaQ := defeqSchemaV1.id
       digest := lengthDigest
         (framedBytes profileV1 (preimage contextA twoTerm)) } :
      Address .semantic)
abbrev ChangedContextChangesPreimage : Prop :=
  framedBytes profileV1 (preimage contextA twoTerm) ≠
    framedBytes profileV1 (preimage contextB twoTerm)
abbrev UnsupportedRawKeepsTypedResidue : Prop :=
  ∃ cert : UnsupportedFragmentCert (.var "outside"),
    bindAddressAtBoundary profileV1 lengthDigest contextA (.var "outside") =
      .unsupported cert
abbrev NakedDigestMutantExposed : Prop :=
  constantDigestMutant (framedBytes profileV1 (preimage contextA twoTerm)) =
    constantDigestMutant (framedBytes profileV1 (preimage contextB twoTerm)) ∧
  framedBytes profileV1 (preimage contextA twoTerm) ≠
    framedBytes profileV1 (preimage contextB twoTerm)
abbrev CrossDomainOmissionExposed : Prop :=
  profileV1.domain ≠ alternateDomainProfile.domain ∧
    omitDomainMutant profileV1 contextA twoTerm =
      omitDomainMutant alternateDomainProfile contextA twoTerm
abbrev SchemaOmissionExposed : Prop :=
  profileV1.schema ≠ profileV2.schema ∧
    omitSchemaMutant profileV1 contextA twoTerm =
      omitSchemaMutant profileV2 contextA twoTerm
abbrev ContextOmissionExposed : Prop :=
  contextA ≠ contextB ∧
    omitContextMutant profileV1 contextA twoTerm =
      omitContextMutant profileV1 contextB twoTerm

structure Certificate where
  canonicalFrameReplays :
    decodeFramedBytes profileV1 (framedBytes profileV1 (preimage contextA twoTerm)) =
      some (preimage contextA twoTerm)
  typedAddressFieldsBound :
    let binding := bindAddress profileV1 lengthDigest contextA twoTerm
    binding.address.algorithm = sha256Coordinate.id ∧
      binding.address.domainQ = defeqDomain.id ∧
      binding.address.schemaQ = defeqSchemaV1.id
  addressKindSemantic :
    (bindAddress profileV1 lengthDigest contextA twoTerm).address =
      ({ algorithm := sha256Coordinate.id
         domainQ := defeqDomain.id
         schemaQ := defeqSchemaV1.id
         digest := lengthDigest
           (framedBytes profileV1 (preimage contextA twoTerm)) } :
        Address .semantic)
  changedContextChangesPreimage :
    framedBytes profileV1 (preimage contextA twoTerm) ≠
      framedBytes profileV1 (preimage contextB twoTerm)
  unsupportedRawKeepsTypedResidue :
    ∃ cert : UnsupportedFragmentCert (.var "outside"),
      bindAddressAtBoundary profileV1 lengthDigest contextA (.var "outside") =
        .unsupported cert
  nakedDigestMutantExposed :
    constantDigestMutant
        (framedBytes profileV1 (preimage contextA twoTerm)) =
      constantDigestMutant
        (framedBytes profileV1 (preimage contextB twoTerm)) ∧
    framedBytes profileV1 (preimage contextA twoTerm) ≠
      framedBytes profileV1 (preimage contextB twoTerm)
  crossDomainOmissionExposed :
    profileV1.domain ≠ alternateDomainProfile.domain ∧
      omitDomainMutant profileV1 contextA twoTerm =
        omitDomainMutant alternateDomainProfile contextA twoTerm
  schemaOmissionExposed :
    profileV1.schema ≠ profileV2.schema ∧
      omitSchemaMutant profileV1 contextA twoTerm =
        omitSchemaMutant profileV2 contextA twoTerm
  contextOmissionExposed :
    contextA ≠ contextB ∧
    omitContextMutant profileV1 contextA twoTerm =
      omitContextMutant profileV1 contextB twoTerm

def certificate : Certificate where
  canonicalFrameReplays := canonicalFrameReplays
  typedAddressFieldsBound := typedAddressFieldsBound
  addressKindSemantic := addressKindSemantic
  changedContextChangesPreimage := changedContextChangesPreimage
  unsupportedRawKeepsTypedResidue := unsupportedRawKeepsTypedResidue
  nakedDigestMutantExposed := nakedDigestMutantExposed
  crossDomainOmissionExposed := crossDomainOmissionExposed
  schemaOmissionExposed := schemaOmissionExposed
  contextOmissionExposed := contextOmissionExposed

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC106Target

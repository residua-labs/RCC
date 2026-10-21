import RCC.RCC58Target

/-! Thin admission checks for RCC-58 concrete AddressUseKernel projection. -/

namespace Residua.RCC.RCC58Target.Tests

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseRegistry.Tests

theorem target_registry_is_derived_complete :
    Residua.RCC.Addressing.AddressUseRegistry.assessAddressUseRegistry
          Residua.RCC.RCC58Target.concreteKernel.sealedUniverse
          Residua.RCC.RCC58Target.concreteKernel.registry =
      Residua.RCC.Addressing.AddressUseRegistry.AddressUseRegistryAssessment.complete := by
  exact Residua.RCC.RCC58Target.registry_is_derived_complete

theorem target_declared_value_use_is_justified :
    Residua.RCC.Addressing.AddressUseRegistry.assessAddressUse
          Residua.RCC.RCC58Target.concreteKernel.registry
          Residua.RCC.Addressing.AddressUseKernel.Tests.kernelRequirement =
      Residua.RCC.Addressing.AddressUseRegistry.AddressUseAssessment.justified := by
  exact Residua.RCC.RCC58Target.declared_value_use_is_justified

theorem target_registry_projection_is_not_empty :
    Residua.RCC.RCC58Target.concreteKernel.registry.entries ≠ [] := by
  exact Residua.RCC.RCC58Target.registry_projection_is_not_empty

theorem target_certificate_is_nonempty :
    Nonempty Residua.RCC.RCC58Target.Certificate := by
  exact Residua.RCC.RCC58Target.certificate_is_nonempty

theorem target_address_use_mutants_are_refused :
    (assessAddressUseRegistry addressUseUniverse missingOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered occurrenceCoordinate)) ∧
    (assessAddressUseRegistry
        addressUseUniverse valueAsOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.kindMismatch occurrenceCoordinate .occurrence .value)) ∧
    (assessAddressUseRegistry addressUseUniverse nakedDigestRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority valueCoordinate)) ∧
    (assessAddressUseRegistry addressUseUniverse foreignDomainRegistry =
      AddressUseRegistryAssessment.refuse
        (.domainMismatch
          valueCoordinate valueRequirement.domainQ
            foreignValueRequirement.domainQ)) ∧
    (assessAddressUseRegistry addressUseUniverse staleSchemaRegistry =
      AddressUseRegistryAssessment.refuse
        (.schemaMismatch
          valueCoordinate valueRequirement.schemaQ
            staleValueRequirement.schemaQ)) ∧
    (assessAddressUseRegistry
        addressUseUniverse missingFactorizationRegistry =
      AddressUseRegistryAssessment.refuse
        (.consumerFactorizationMissing valueCoordinate)) := by
  exact ⟨omitted_q_field_is_refused, value_q_cannot_authorize_occurrence_q,
    cross_domain_naked_digest_has_no_authority,
    cross_domain_registration_is_refused, schema_mismatch_is_refused,
    missing_consumer_factorization_is_refused⟩

#print axioms target_registry_is_derived_complete
#print axioms target_declared_value_use_is_justified
#print axioms target_registry_projection_is_not_empty

end Residua.RCC.RCC58Target.Tests

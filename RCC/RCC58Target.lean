import RCCTests.AddressUseKernel
import RCCTests.AddressUseRegistry

/-!
# RCC-58 target package

This candidate packages the first concrete `AddressUseKernel` projection over
the unit value address domain.  Unlike the generic FC-1 adapter, the fixture
contains an inhabited sealed universe, a concrete registry, and the derived
completeness witness.  The target deliberately remains a candidate: it does
not claim that this fixture is the live Residua repository registry.
-/

namespace Residua.RCC.RCC58Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseKernel.Tests
open Residua.RCC.Addressing.AddressKernel.Tests
open Residua.RCC.Addressing.AddressUseRegistry.Tests

def concreteKernel := useKernel

theorem registry_is_derived_complete :
    assessAddressUseRegistry
        concreteKernel.sealedUniverse concreteKernel.registry =
      AddressUseRegistryAssessment.complete := by
  exact concreteKernel.complete_is_derived

theorem declared_value_use_is_justified :
    assessAddressUse concreteKernel.registry kernelRequirement =
      AddressUseAssessment.justified := by
  exact concreteKernel.every_declared_use_justified kernelRequirement rfl

theorem bound_requirement_preserves_kind_domain_schema :
    concreteKernel.boundRequirement.kind = AddressKind.value ∧
      concreteKernel.boundRequirement.domainQ = unitKernel.digest.domainQ ∧
      concreteKernel.boundRequirement.schemaQ = unitKernel.digest.schemaQ := by
  exact concreteKernel.bound_requirement_matches_base

theorem registry_projection_is_not_empty :
    concreteKernel.registry.entries ≠ [] := by
  simp [concreteKernel, useKernel, kernelRegistry]

/-! The certificate binds both the positive registry projection and every
    concrete address-use mutant, rather than merely packaging a nonempty
    fixture. -/

structure Certificate : Prop where
  registryComplete :
    assessAddressUseRegistry
        concreteKernel.sealedUniverse concreteKernel.registry =
      AddressUseRegistryAssessment.complete
  declaredUseJustified :
    assessAddressUse concreteKernel.registry kernelRequirement =
      AddressUseAssessment.justified
  requirementIdentity :
    concreteKernel.boundRequirement.kind = AddressKind.value ∧
      concreteKernel.boundRequirement.domainQ = unitKernel.digest.domainQ ∧
      concreteKernel.boundRequirement.schemaQ = unitKernel.digest.schemaQ
  registryNonempty : concreteKernel.registry.entries ≠ []
  omittedFieldRefused :
    assessAddressUseRegistry addressUseUniverse missingOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered occurrenceCoordinate)
  kindMismatchRefused :
    assessAddressUseRegistry
        addressUseUniverse valueAsOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.kindMismatch occurrenceCoordinate .occurrence .value)
  nakedDigestRefused :
    assessAddressUseRegistry addressUseUniverse nakedDigestRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority valueCoordinate)
  domainMismatchRefused :
    assessAddressUseRegistry addressUseUniverse foreignDomainRegistry =
      AddressUseRegistryAssessment.refuse
        (.domainMismatch
          valueCoordinate valueRequirement.domainQ
            foreignValueRequirement.domainQ)
  schemaMismatchRefused :
    assessAddressUseRegistry addressUseUniverse staleSchemaRegistry =
      AddressUseRegistryAssessment.refuse
        (.schemaMismatch
          valueCoordinate valueRequirement.schemaQ
            staleValueRequirement.schemaQ)
  factorizationMissingRefused :
    assessAddressUseRegistry
        addressUseUniverse missingFactorizationRegistry =
      AddressUseRegistryAssessment.refuse
        (.consumerFactorizationMissing valueCoordinate)
  collisionPolicyMissingRefused :
    assessAddressUseRegistry
        addressUseUniverse missingCollisionPolicyRegistry =
      AddressUseRegistryAssessment.refuse
        (.collisionPolicyMissing valueCoordinate)

def certificate : Certificate where
  registryComplete := registry_is_derived_complete
  declaredUseJustified := declared_value_use_is_justified
  requirementIdentity := bound_requirement_preserves_kind_domain_schema
  registryNonempty := registry_projection_is_not_empty
  omittedFieldRefused := omitted_q_field_is_refused
  kindMismatchRefused := value_q_cannot_authorize_occurrence_q
  nakedDigestRefused := cross_domain_naked_digest_has_no_authority
  domainMismatchRefused := cross_domain_registration_is_refused
  schemaMismatchRefused := schema_mismatch_is_refused
  factorizationMissingRefused := missing_consumer_factorization_is_refused
  collisionPolicyMissingRefused := missing_collision_policy_is_refused

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC58Target

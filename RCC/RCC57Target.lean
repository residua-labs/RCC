import RCCTests.AddressUseRegistry

/-!
# RCC-57 target package

This candidate is the first concrete AddressUseRegistry instance: the sealed
surface contains both value and occurrence q-bearing fields, each with typed
envelope, consumer-factorization, and collision-policy evidence.  The
registry mutants refuse omitted fields, kind/domain/schema mismatches, naked
digests, and missing proof families.
-/

namespace Residua.RCC.RCC57Target

open Residua.RCC.Addressing.AddressUseRegistry.Tests
open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry

structure Certificate where
  complete :
    assessAddressUseRegistry addressUseUniverse completeRegistry =
      AddressUseRegistryAssessment.complete
  occurrenceConsumer :
    assessAddressUse completeRegistry occurrenceRequirement =
      AddressUseAssessment.justified
  omittedField :
    assessAddressUseRegistry addressUseUniverse missingOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered occurrenceCoordinate)
  kindMismatch :
    assessAddressUseRegistry
        addressUseUniverse valueAsOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.kindMismatch occurrenceCoordinate .occurrence .value)
  nakedDigest :
    assessAddressUseRegistry addressUseUniverse nakedDigestRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority valueCoordinate)
  domainMismatch :
    assessAddressUseRegistry addressUseUniverse foreignDomainRegistry =
      AddressUseRegistryAssessment.refuse
        (.domainMismatch
          valueCoordinate valueRequirement.domainQ
            foreignValueRequirement.domainQ)
  schemaMismatch :
    assessAddressUseRegistry addressUseUniverse staleSchemaRegistry =
      AddressUseRegistryAssessment.refuse
        (.schemaMismatch
          valueCoordinate valueRequirement.schemaQ
            staleValueRequirement.schemaQ)
  missingFactorization :
    assessAddressUseRegistry
        addressUseUniverse missingFactorizationRegistry =
      AddressUseRegistryAssessment.refuse
        (.consumerFactorizationMissing valueCoordinate)
  missingCollisionPolicy :
    assessAddressUseRegistry
        addressUseUniverse missingCollisionPolicyRegistry =
      AddressUseRegistryAssessment.refuse
        (.collisionPolicyMissing valueCoordinate)

def certificate : Certificate where
  complete := complete_registry_is_accepted
  occurrenceConsumer := complete_registry_justifies_occurrence_receiver
  omittedField := omitted_q_field_is_refused
  kindMismatch := value_q_cannot_authorize_occurrence_q
  nakedDigest := cross_domain_naked_digest_has_no_authority
  domainMismatch := cross_domain_registration_is_refused
  schemaMismatch := schema_mismatch_is_refused
  missingFactorization := missing_consumer_factorization_is_refused
  missingCollisionPolicy := missing_collision_policy_is_refused

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC57Target

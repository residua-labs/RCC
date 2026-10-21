import RCCTests.AddressKernel
import RCCTests.AddressUseRegistry

/-! RCC-0 candidate: typed address kernels and closed-world q-use registry. -/

namespace Residua.RCC.RCC0Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressKernel.Tests
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseRegistry.Tests

structure Certificate where
  addressEqIffEquivalent :
    ∀ (left right : Bool),
      twoClassKernel.address left = twoClassKernel.address right ↔
        TwoClassDomain.equivalent () left right
  addressConsumerSubstitution :
    ∀ (left right : Bool),
      twoClassKernel.address left = twoClassKernel.address right →
        twoClassKernel.consumer left = twoClassKernel.consumer right
  nonfactorableConsumerRefused :
    ¬ ConsumerFactorsThroughQuotient
      BooleanDomain () (fun value : Bool => value)
  completeRegistryAccepted :
    assessAddressUseRegistry addressUseUniverse completeRegistry =
      AddressUseRegistryAssessment.complete
  completeRegistryJustifiesOccurrence :
    assessAddressUse completeRegistry occurrenceRequirement =
      AddressUseAssessment.justified
  omittedUseRefused :
    assessAddressUseRegistry addressUseUniverse missingOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered occurrenceCoordinate)
  kindMismatchRefused :
    assessAddressUseRegistry addressUseUniverse valueAsOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.kindMismatch occurrenceCoordinate .occurrence .value)
  nakedDigestRefused :
    assessAddressUseRegistry addressUseUniverse nakedDigestRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority valueCoordinate)
  domainMismatchRefused :
    assessAddressUseRegistry addressUseUniverse foreignDomainRegistry =
      AddressUseRegistryAssessment.refuse
        (.domainMismatch valueCoordinate valueRequirement.domainQ
          foreignValueRequirement.domainQ)
  schemaMismatchRefused :
    assessAddressUseRegistry addressUseUniverse staleSchemaRegistry =
      AddressUseRegistryAssessment.refuse
        (.schemaMismatch valueCoordinate valueRequirement.schemaQ
          staleValueRequirement.schemaQ)
  factorizationMissingRefused :
    assessAddressUseRegistry addressUseUniverse missingFactorizationRegistry =
      AddressUseRegistryAssessment.refuse
        (.consumerFactorizationMissing valueCoordinate)
  collisionPolicyMissingRefused :
    assessAddressUseRegistry addressUseUniverse missingCollisionPolicyRegistry =
      AddressUseRegistryAssessment.refuse
        (.collisionPolicyMissing valueCoordinate)

def certificate : Certificate where
  addressEqIffEquivalent := by
    intro left right
    exact twoClass_kernel_address_exact left right
  addressConsumerSubstitution := twoClass_kernel_consumer_exact
  nonfactorableConsumerRefused := nonconstant_consumer_not_factorable
  completeRegistryAccepted := complete_registry_is_accepted
  completeRegistryJustifiesOccurrence :=
    complete_registry_justifies_occurrence_receiver
  omittedUseRefused := omitted_q_field_is_refused
  kindMismatchRefused := value_q_cannot_authorize_occurrence_q
  nakedDigestRefused := cross_domain_naked_digest_has_no_authority
  domainMismatchRefused := cross_domain_registration_is_refused
  schemaMismatchRefused := schema_mismatch_is_refused
  factorizationMissingRefused := missing_consumer_factorization_is_refused
  collisionPolicyMissingRefused := missing_collision_policy_is_refused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC0Target

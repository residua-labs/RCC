import RCCTests.AddressUseKernel

/-! RCC-101 candidate: sealed AddressUseKernel registry completeness. -/

namespace Residua.RCC.RCC101Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseRegistry.Tests
open Residua.RCC.Addressing.AddressKernel.Tests
open Residua.RCC.Addressing.AddressUseKernel.Tests

theorem registryAccepted :
    assessAddressUseRegistry
        twoClassUseKernel.sealedUniverse twoClassUseKernel.registry =
      AddressUseRegistryAssessment.complete :=
  twoClassUseKernel.complete_is_derived

theorem declaredUseJustified :
    assessAddressUse
        twoClassUseKernel.registry twoClassKernelRequirement =
      AddressUseAssessment.justified :=
  twoClassUseKernel.every_declared_use_justified
    twoClassKernelRequirement rfl

theorem boundRequirementMatchesBase :
    twoClassUseKernel.boundRequirement.kind = AddressKind.value ∧
      twoClassUseKernel.boundRequirement.domainQ =
        twoClassKernel.digest.domainQ ∧
      twoClassUseKernel.boundRequirement.schemaQ =
        twoClassKernel.digest.schemaQ :=
  twoClassUseKernel.bound_requirement_matches_base

structure Certificate where
  registryAccepted :
    assessAddressUseRegistry
        twoClassUseKernel.sealedUniverse twoClassUseKernel.registry =
      AddressUseRegistryAssessment.complete
  declaredUseJustified :
    assessAddressUse
        twoClassUseKernel.registry twoClassKernelRequirement =
      AddressUseAssessment.justified
  boundRequirementMatchesBase :
    twoClassUseKernel.boundRequirement.kind = AddressKind.value ∧
      twoClassUseKernel.boundRequirement.domainQ =
        twoClassKernel.digest.domainQ ∧
      twoClassUseKernel.boundRequirement.schemaQ =
        twoClassKernel.digest.schemaQ
  twoClassKernelSeparatesClasses :
    twoClassKernel.address false ≠ twoClassKernel.address true
  omittedFieldRefused :
    assessAddressUseRegistry
        twoClassKernelUniverse missingTwoClassRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered twoClassKernelRequirement.coordinate)
  nakedDigestRefused :
    assessAddressUseRegistry
        twoClassKernelUniverse nakedTwoClassRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority twoClassKernelRequirement.coordinate)

def certificate : Certificate where
  registryAccepted := registryAccepted
  declaredUseJustified := declaredUseJustified
  boundRequirementMatchesBase := boundRequirementMatchesBase
  twoClassKernelSeparatesClasses := twoClass_kernel_separates_classes
  omittedFieldRefused := omitted_two_class_q_field_is_refused
  nakedDigestRefused := two_class_naked_digest_has_no_authority

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC101Target

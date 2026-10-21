import RCC.AddressUseKernel
import RCCTests.AddressUseRegistry
import RCCTests.AddressKernel

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseRegistry.Tests
open Residua.RCC.Addressing.AddressKernel.Tests

namespace Residua.RCC.Addressing.AddressUseKernel.Tests

def kernelRequirement : AddressUseRequirement where
  coordinate := valueCoordinate
  kind := .value
  domainQ := unitKernel.digest.domainQ
  schemaQ := unitKernel.digest.schemaQ

def kernelUniverse : SealedAddressUseUniverse where
  surfaceSchemaQ := kernelRequirement.schemaQ
  InUniverse requirement := requirement = kernelRequirement
  enumeration := [kernelRequirement]
  sound := by
    intro requirement member
    simpa using member
  complete := by
    intro requirement inUniverse
    simp [inUniverse]

inductive KernelTypedEnvelope : AddressUseRequirement → Type
  | value : KernelTypedEnvelope kernelRequirement

inductive KernelConsumerFactorization : AddressUseRequirement → Type
  | value : KernelConsumerFactorization kernelRequirement

inductive KernelCollisionPolicy : AddressUseRequirement → Type
  | value : KernelCollisionPolicy kernelRequirement

abbrev KernelEntry :=
  AddressUseEntry
    KernelTypedEnvelope KernelConsumerFactorization KernelCollisionPolicy

abbrev KernelRegistry :=
  AddressUseRegistry
    KernelTypedEnvelope KernelConsumerFactorization KernelCollisionPolicy

def kernelEntry : KernelEntry where
  requirement := kernelRequirement
  typedEnvelope := some .value
  consumerFactorization := some .value
  collisionPolicy := some .value

def kernelRegistry : KernelRegistry where
  entries := [kernelEntry]

theorem kernel_registry_is_accepted :
    assessAddressUseRegistry kernelUniverse kernelRegistry =
      AddressUseRegistryAssessment.complete := by
  rfl

def useKernel :
    AddressUseKernel
      unitKernel
      KernelTypedEnvelope
      KernelConsumerFactorization
      KernelCollisionPolicy where
  boundRequirement := kernelRequirement
  kindBound := rfl
  domainBound := rfl
  schemaBound := rfl
  sealedUniverse := kernelUniverse
  registry := kernelRegistry
  derivedComplete := kernel_registry_is_accepted

/-! A non-degenerate registry fixture bound to the two-class AddressKernel. -/

def twoClassKernelRequirement : AddressUseRequirement where
  coordinate := {
    fieldPath := "event.payload.two_class_value_q"
    consumerQ := "consumer:two-class-value-cache:v1"
  }
  kind := .value
  domainQ := twoClassKernel.digest.domainQ
  schemaQ := twoClassKernel.digest.schemaQ

def twoClassKernelUniverse : SealedAddressUseUniverse where
  surfaceSchemaQ := twoClassKernelRequirement.schemaQ
  InUniverse requirement := requirement = twoClassKernelRequirement
  enumeration := [twoClassKernelRequirement]
  sound := by
    intro requirement member
    simpa using member
  complete := by
    intro requirement inUniverse
    simp [inUniverse]

inductive TwoClassTypedEnvelope : AddressUseRequirement → Type
  | value : TwoClassTypedEnvelope twoClassKernelRequirement

inductive TwoClassConsumerFactorization : AddressUseRequirement → Type
  | value : TwoClassConsumerFactorization twoClassKernelRequirement

inductive TwoClassCollisionPolicy : AddressUseRequirement → Type
  | value : TwoClassCollisionPolicy twoClassKernelRequirement

abbrev TwoClassEntry :=
  AddressUseEntry
    TwoClassTypedEnvelope TwoClassConsumerFactorization TwoClassCollisionPolicy

abbrev TwoClassRegistry :=
  AddressUseRegistry
    TwoClassTypedEnvelope TwoClassConsumerFactorization TwoClassCollisionPolicy

def twoClassEntry : TwoClassEntry where
  requirement := twoClassKernelRequirement
  typedEnvelope := some .value
  consumerFactorization := some .value
  collisionPolicy := some .value

def twoClassRegistry : TwoClassRegistry where
  entries := [twoClassEntry]

theorem twoClass_registry_is_accepted :
    assessAddressUseRegistry twoClassKernelUniverse twoClassRegistry =
      AddressUseRegistryAssessment.complete := by
  rfl

def twoClassUseKernel :
    AddressUseKernel
      twoClassKernel
      TwoClassTypedEnvelope
      TwoClassConsumerFactorization
      TwoClassCollisionPolicy where
  boundRequirement := twoClassKernelRequirement
  kindBound := rfl
  domainBound := rfl
  schemaBound := rfl
  sealedUniverse := twoClassKernelUniverse
  registry := twoClassRegistry
  derivedComplete := twoClass_registry_is_accepted

def missingTwoClassRegistry : TwoClassRegistry where
  entries := []

theorem omitted_two_class_q_field_is_refused :
    assessAddressUseRegistry
        twoClassKernelUniverse missingTwoClassRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered twoClassKernelRequirement.coordinate) := by
  rfl

def nakedTwoClassEntry : TwoClassEntry where
  requirement := twoClassKernelRequirement
  typedEnvelope := none
  consumerFactorization := some .value
  collisionPolicy := some .value

def nakedTwoClassRegistry : TwoClassRegistry where
  entries := [nakedTwoClassEntry]

theorem two_class_naked_digest_has_no_authority :
    assessAddressUseRegistry
        twoClassKernelUniverse nakedTwoClassRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority twoClassKernelRequirement.coordinate) := by
  rfl

example :
    assessAddressUseRegistry useKernel.sealedUniverse useKernel.registry =
      AddressUseRegistryAssessment.complete := by
  exact useKernel.complete_is_derived

example :
    assessAddressUse useKernel.registry kernelRequirement =
      AddressUseAssessment.justified := by
  exact useKernel.every_declared_use_justified kernelRequirement rfl

example :
    useKernel.boundRequirement.kind = AddressKind.value ∧
      useKernel.boundRequirement.domainQ = unitKernel.digest.domainQ ∧
      useKernel.boundRequirement.schemaQ = unitKernel.digest.schemaQ := by
  exact useKernel.bound_requirement_matches_base

end Residua.RCC.Addressing.AddressUseKernel.Tests

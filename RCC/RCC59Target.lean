import RCCTests.ConcreteAddressRegistryAdapter

/-! RCC-59 candidate: concrete sealed-snapshot address-registry adapter. -/

namespace Residua.RCC.RCC59Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseKernel.Tests
open Residua.RCC.ConcreteAddressRegistryAdapter.Tests

def sealedCoordinate := snapshotRegistryQ
def selectedKernel := kernelAtRegistry sealedCoordinate

theorem sealed_coordinate_is_13 : sealedCoordinate = 13 := by
  exact snapshot_registry_coordinate_is_sealed

theorem selected_kernel_is_concrete : selectedKernel = some useKernel := by
  change kernelAtRegistry snapshotRegistryQ = some useKernel
  exact snapshot_selects_concrete_kernel

theorem selected_kernel_has_derived_registry_completeness :
    ∃ kernel : ConcreteKernel,
      selectedKernel = some kernel ∧
        assessAddressUseRegistry kernel.sealedUniverse kernel.registry =
          AddressUseRegistryAssessment.complete := by
  exact snapshot_selected_kernel_is_complete

theorem unknown_coordinate_does_not_fallback :
    ∀ registryQ, registryQ ≠ sealedCoordinate →
      kernelAtRegistry registryQ = none := by
  intro registryQ h
  rw [sealed_coordinate_is_13] at h
  simpa [kernelAtRegistry, h]

structure Certificate where
  sealedCoordinateClaim : sealedCoordinate = 13
  concreteKernelClaim : selectedKernel = some useKernel
  derivedCompletenessClaim :
    ∃ kernel : ConcreteKernel,
      selectedKernel = some kernel ∧
        assessAddressUseRegistry kernel.sealedUniverse kernel.registry =
          AddressUseRegistryAssessment.complete
  unknownRefusedClaim :
    ∀ registryQ : Nat, registryQ ≠ RCC59Target.sealedCoordinate →
      kernelAtRegistry registryQ = none

def certificate : Certificate where
  sealedCoordinateClaim := sealed_coordinate_is_13
  concreteKernelClaim := selected_kernel_is_concrete
  derivedCompletenessClaim := selected_kernel_has_derived_registry_completeness
  unknownRefusedClaim := unknown_coordinate_does_not_fallback

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC59Target

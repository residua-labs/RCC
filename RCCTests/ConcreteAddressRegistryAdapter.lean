import RCCTests.FacetCoherence
import RCCTests.AddressUseKernel

/-!
# Concrete snapshot-to-address-registry adapter fixture

The FC-1 snapshot fixture carries an abstract numeric `AddressRegistry`
coordinate.  This file gives that coordinate an explicit, finite adapter to
the concrete unit-value `AddressUseKernel` fixture.  Unknown coordinates are
refused rather than silently receiving the same kernel.

This is an adapter fixture, not the live repository registry.
-/

namespace Residua.RCC.ConcreteAddressRegistryAdapter.Tests

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry
open Residua.RCC.Addressing.AddressUseKernel.Tests
open Residua.RCC.Addressing.AddressKernel.Tests
open Residua.RCC.FacetSnapshot
open Residua.RCC.FacetCoherence.Tests

def snapshotRegistryQ : Nat := snapshotH1.coordinates.addressRegistry

abbrev ConcreteKernel :=
  AddressUseKernel
    unitKernel
    KernelTypedEnvelope
    KernelConsumerFactorization
    KernelCollisionPolicy

def kernelAtRegistry (registryQ : Nat) :
    Option ConcreteKernel :=
  if registryQ = 13 then some useKernel else none

theorem snapshot_registry_coordinate_is_sealed :
    snapshotRegistryQ = 13 := by
  rfl

theorem snapshot_selects_concrete_kernel :
    kernelAtRegistry snapshotRegistryQ = some useKernel := by
  rfl

theorem snapshot_selected_kernel_is_complete :
    ∃ kernel : ConcreteKernel,
      kernelAtRegistry snapshotRegistryQ = some kernel ∧
        assessAddressUseRegistry kernel.sealedUniverse kernel.registry =
          AddressUseRegistryAssessment.complete := by
  exact ⟨useKernel, snapshot_selects_concrete_kernel,
    useKernel.complete_is_derived⟩

theorem unknown_registry_coordinate_is_refused :
    kernelAtRegistry 12 = none := by
  rfl

end Residua.RCC.ConcreteAddressRegistryAdapter.Tests

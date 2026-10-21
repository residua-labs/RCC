import RCCTests.SeamIntegratedAdapter
import RCCTests.SeamIntegratedFamily

/-! RCC-74 candidate: integrated seam gluing and refusal boundaries. -/

namespace Residua.RCC.RCC74Target

open Residua.RCC.SeamIntegratedAdapter.Tests
open Residua.RCC.SeamIntegratedFamily.Tests
open Residua.RCC.SeamIntegratedAdapter
open Residua.RCC.SeamIntegratedFamily
open Residua.RCC.SeamComponentAdapter
open Residua.RCC.SeamAssumptionAdapter
open Residua.RCC.SeamFamily
open Residua.RCC.SeamExactness
open Residua.RCC.SeamWriterAdapter

def integratedFullExactness := integrated_certificate_derives_full_exactness
def integratedComponentClosure := integrated_certificate_derives_component_closure
def integratedDependencyTransport := integrated_certificate_transports_active_dependency
def missingComponentRefused := missing_component_closure_blocks_integration
def integratedFamilyExactness := sealed_integrated_family_derives_exact_family
def integratedIdentitySeamClosed := sealed_integrated_family_closes_declared_identity_seam
def emptyEnumerationRefused := empty_enumeration_blocks_integrated_family
def dualOwnerFamilyRefused := dual_owner_seam_blocks_integrated_family

abbrev DualOwnerAssumptions : Type 1 :=
  AssumptionSeamBinding SeamExactness.Tests.DualOwner.world

abbrev DualOwnerRefusedClaim : Prop :=
  ∀ {Judgment Version : Type}
    {writerSpec :
      Residua.RCC.AdmissionLinearizer.FencedWriterSpec
        SeamExactness.Tests.DualOwner.world.EffectSlot
        SeamExactness.Tests.DualOwner.world.HistoryHead}
    {equivalence :
      Residua.RCC.AdmissionLinearizer.JudgmentEquivalence Judgment}
    {linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
        SeamExactness.Tests.DualOwner.world.EffectSlot
        SeamExactness.Tests.DualOwner.world.HistoryHead
        Judgment
        SeamExactness.Tests.DualOwner.world.EffectOwner
        Version
        writerSpec
        equivalence}
    {version : Version}
    {sourceState targetState :
      Residua.RCC.AdmissionLinearizer.FencedWriterState
        SeamExactness.Tests.DualOwner.world.EffectSlot
        SeamExactness.Tests.DualOwner.world.HistoryHead
        Judgment
        SeamExactness.Tests.DualOwner.world.EffectOwner}
    {component : ComponentRelationBinding SeamExactness.Tests.DualOwner.world}
    {assumptions : DualOwnerAssumptions},
    ¬ IntegratedSeamCertificateAt
      SeamExactness.Tests.DualOwner.world
      linearizer
      version
      sourceState
      targetState
      component
      assumptions

def dualOwnerRefused : DualOwnerRefusedClaim :=
  @dual_owner_world_blocks_integration

structure Certificate where
  integratedFullExactness : ExactSeamAt Positive.World
  integratedComponentClosure :
    SeamComponentAdapter.Tests.Positive.binding.targetClosed
      (Positive.integrated.toFormalSeam.map true)
  integratedDependencyTransport :
    SeamAssumptionAdapter.Tests.Assumption.clock ∈
        SeamAssumptionAdapter.Tests.Positive.binding.targetDependencies
          (Positive.World.encode true) ∧
      SeamAssumptionAdapter.Tests.Positive.binding.targetActive
        Positive.World.targetAssumptionRoot
        .clock
  missingComponentRefused :
    ¬ IntegratedSeamCertificateAt
      Positive.World
      SeamWriterAdapter.Tests.linearizer
      ()
      SeamWriterAdapter.Tests.sourceState
      SeamWriterAdapter.Tests.targetState
      SeamComponentAdapter.Tests.MissingClosure.binding
      SeamAssumptionAdapter.Tests.Positive.binding
  dualOwnerRefused : DualOwnerRefusedClaim
  integratedFamilyExactness : ExactSeamFamily Positive.Scope
  integratedIdentitySeamClosed :
    Residua.RCC.SeamExactness.ExactSeamAt
      (Positive.Scope.world SeamFamily.Tests.Positive.Seam.identity)
  emptyEnumerationRefused :
    SealedIntegratedSeamFamily
        SeamFamily.Tests.EmptyEnumeration.scope → False
  dualOwnerFamilyRefused :
    SealedIntegratedSeamFamily
        SeamFamily.Tests.BadSeam.scope → False

def certificate : Certificate where
  integratedFullExactness := integratedFullExactness
  integratedComponentClosure := integratedComponentClosure
  integratedDependencyTransport := integratedDependencyTransport
  missingComponentRefused := missingComponentRefused
  dualOwnerRefused := dualOwnerRefused
  integratedFamilyExactness := integratedFamilyExactness
  integratedIdentitySeamClosed := integratedIdentitySeamClosed
  emptyEnumerationRefused := emptyEnumerationRefused
  dualOwnerFamilyRefused := dualOwnerFamilyRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC74Target

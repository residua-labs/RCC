import RCCTests.SeamAssumptionAdapter
import RCCTests.SeamComponentAdapter
import RCC.SeamIntegratedAdapter
import RCCTests.SeamWriterAdapter

namespace Residua.RCC.SeamIntegratedAdapter.Tests

open Residua.RCC.SeamAssumptionAdapter
open Residua.RCC.SeamComponentAdapter
open Residua.RCC.SeamExactness
open Residua.RCC.SeamIntegratedAdapter
open Residua.RCC.SeamWriterAdapter

namespace Positive

abbrev World := SeamWriterAdapter.Tests.World

def integrated :
    IntegratedSeamCertificateAt
      World
      SeamWriterAdapter.Tests.linearizer
      ()
      SeamWriterAdapter.Tests.sourceState
      SeamWriterAdapter.Tests.targetState
      SeamComponentAdapter.Tests.Positive.binding
      SeamAssumptionAdapter.Tests.Positive.binding where
  writer := SeamWriterAdapter.Tests.writerSeam
  stepPreserved := fun step => step
  closedPreserved := fun closed => closed
  activeExact := by
    intro assumption
    exact
      SeamAssumptionAdapter.Tests.Positive.assumptionSeam.activeExact
        assumption
  dependenciesExact := by
    intro source assumption
    exact
      SeamAssumptionAdapter.Tests.Positive.assumptionSeam.dependenciesExact
        source assumption

end Positive

theorem integrated_certificate_derives_full_exactness :
    ExactSeamAt Positive.World :=
  Positive.integrated.toExactSeam

theorem integrated_certificate_derives_component_closure :
    SeamComponentAdapter.Tests.Positive.binding.targetClosed
      (Positive.integrated.toFormalSeam.map true) :=
  Positive.integrated.toFormalSeam.closedPreserved rfl

theorem integrated_certificate_transports_active_dependency :
    SeamAssumptionAdapter.Tests.Assumption.clock ∈
        SeamAssumptionAdapter.Tests.Positive.binding.targetDependencies
          (Positive.World.encode true) ∧
      SeamAssumptionAdapter.Tests.Positive.binding.targetActive
        Positive.World.targetAssumptionRoot
        .clock :=
  Positive.integrated.toAssumptionSeam.transportActiveDependency
    (source := true)
    (assumption := SeamAssumptionAdapter.Tests.Assumption.clock)
    (List.Mem.head [])
    ⟨rfl, rfl⟩

/--
Sharing a world and writer cannot hide a missing component closure law.
-/
theorem missing_component_closure_blocks_integration :
    ¬ IntegratedSeamCertificateAt
      Positive.World
      SeamWriterAdapter.Tests.linearizer
      ()
      SeamWriterAdapter.Tests.sourceState
      SeamWriterAdapter.Tests.targetState
      SeamComponentAdapter.Tests.MissingClosure.binding
      SeamAssumptionAdapter.Tests.Positive.binding := by
  intro integrated
  exact integrated.closedPreserved (source := true) rfl

/--
Component and assumption laws cannot replace the canonical-writer facet:
the dual-owner world has no integrated certificate for any supplied
linearizer, states, or endpoint bindings.
-/
theorem dual_owner_world_blocks_integration
    {Judgment Version : Type}
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
    {component :
      ComponentRelationBinding SeamExactness.Tests.DualOwner.world}
    {assumptions :
      AssumptionSeamBinding SeamExactness.Tests.DualOwner.world} :
    ¬ IntegratedSeamCertificateAt
      SeamExactness.Tests.DualOwner.world
      linearizer
      version
      sourceState
      targetState
      component
      assumptions := by
  intro integrated
  exact
    SeamExactness.Tests.dual_effect_owner_is_refused
      integrated.toExactSeam

end Residua.RCC.SeamIntegratedAdapter.Tests

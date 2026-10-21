import RCC.RuntimeClosureBridge

/-! Generic projection and refusal checks for the runtime/source-window bridge. -/

namespace Residua.RCC.RuntimeClosureBridge.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSettledAdmission
open Residua.RCC.RuntimeAdmissionBinding
open Residua.RCC.RuntimeFinalizedBridge
open Residua.RCC.ClosurePrerequisites

universe u

theorem runtime_head_projects_to_closure_snapshot
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ Config SourceAuthority
      Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal : GloballySettledAdmission linearizer version proposal}
    {historyRuntime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime Epoch Head EffectSlot Generation Occurrence FailureName}
    {actual :
      ActuallyGloballySettledAdmission formal historyRuntime receiptView storeQ effectRuntime}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {config : Config}
    {runtimeFinalized :
      RuntimeFinalizedBridge.Binding formal actual history ConfigLawful config}
    {protocol : SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment) (history := history)
        (ConfigLawful := ConfigLawful) (protocol := protocol)
        (ConfigStable := ConfigStable)}
    (binding : Binding formal actual runtimeFinalized closure) :
    historyRuntime.actualHead actual.transition.append.postStore = closure.snapshot.head :=
  binding.runtime_head_matches_closure_snapshot

theorem wrong_closure_head_refuses_binding
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ Config SourceAuthority
      Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal : GloballySettledAdmission linearizer version proposal}
    {historyRuntime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime Epoch Head EffectSlot Generation Occurrence FailureName}
    {actual :
      ActuallyGloballySettledAdmission formal historyRuntime receiptView storeQ effectRuntime}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {config : Config}
    {runtimeFinalized :
      RuntimeFinalizedBridge.Binding formal actual history ConfigLawful config}
    {protocol : SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment) (history := history)
        (ConfigLawful := ConfigLawful) (protocol := protocol)
        (ConfigStable := ConfigStable)}
    (binding : Binding formal actual runtimeFinalized closure)
    (wrong : closure.finalizedHead.certificate.head ≠ runtimeFinalized.finalized.head) :
    False :=
  wrong binding.closureHeadAligned

end Residua.RCC.RuntimeClosureBridge.Tests

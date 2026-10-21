import RCC.RuntimeFinalizedBridge
import RCC.ClosurePrerequisites

/-!
# Runtime-finalized closure bridge

`FinalizedClosureEvidence` binds an RCC-45 finalized head to a sealed source
window, while `RuntimeFinalizedBridge.Binding` binds an actual append/receipt
to a finalized event.  This module requires the two envelopes to name the same
event and successor head before projecting closure coordinates.  A source
window certificate alone therefore cannot bless an unrelated runtime append.

This is a safety bridge only: source-window adequacy and runtime storage
liveness remain separate instance obligations.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RuntimeClosureBridge

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSettledAdmission
open Residua.RCC.RuntimeAdmissionBinding
open Residua.RCC.RuntimeFinalizedBridge
open Residua.RCC.ClosurePrerequisites

universe u

structure Binding
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
    (formal : GloballySettledAdmission linearizer version proposal)
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    (actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {config : Config}
    (runtimeFinalized :
      RuntimeFinalizedBridge.Binding
        formal actual history ConfigLawful config)
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)) : Type u where
  closureEventAligned :
    closure.finalizedHead.certificate.admission.history.event =
      formal.history.event
  closureHeadAligned :
    closure.finalizedHead.certificate.head =
      runtimeFinalized.finalized.head

theorem Binding.runtime_head_matches_closure_snapshot
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
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {config : Config}
    {runtimeFinalized :
      RuntimeFinalizedBridge.Binding formal actual history ConfigLawful config}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)}
    (binding :
      Binding formal actual runtimeFinalized closure) :
    historyRuntime.actualHead actual.transition.append.postStore =
        closure.snapshot.head := by
  have runtimeHead := runtimeFinalized.actual_post_head_matches_finalized
  have closureHead := closure.headMatches
  exact runtimeHead.trans
    (binding.closureHeadAligned.symm.trans closureHead)

theorem Binding.runtime_event_is_closure_finalized
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
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {config : Config}
    {runtimeFinalized :
      RuntimeFinalizedBridge.Binding formal actual history ConfigLawful config}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)}
    (binding :
      Binding formal actual runtimeFinalized closure) :
    history.finalized formal.history.event
      ∧ closure.finalizedHead.certificate.head =
          runtimeFinalized.finalized.head := by
  constructor
  · rw [← binding.closureEventAligned]
    exact closure.finalizedHead.certificate.historyFinalized
  · exact binding.closureHeadAligned

end Residua.RCC.RuntimeClosureBridge

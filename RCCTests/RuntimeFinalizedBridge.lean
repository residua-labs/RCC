import RCC.RuntimeFinalizedBridge

/-!
# Runtime/finalized-head bridge tests

The tests are generic projection/refusal lemmas: a bridge exposes the same
post-store head as the finalized certificate, and a receipt/head mismatch
cannot inhabit the binding.
-/

namespace Residua.RCC.RuntimeFinalizedBridge.Tests

open Residua.RCC.RuntimeFinalizedBridge
open Residua.RCC.RuntimeAdmissionBinding
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.GlobalSettledAdmission
open Residua.RCC.FinalizedHeadWindow

universe u

theorem aligned_head_is_runtime_head
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ Config : Type u}
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
    {formal :
      Residua.RCC.GlobalSettledAdmission.GloballySettledAdmission
        linearizer version proposal}
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
    (binding :
      Residua.RCC.RuntimeFinalizedBridge.Binding
        formal actual history ConfigLawful config) :
    historyRuntime.actualHead actual.transition.append.postStore =
        binding.finalized.head :=
  binding.actual_post_head_matches_finalized

theorem receipt_head_mismatch_refuses_binding
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ Config : Type u}
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
    {formal :
      Residua.RCC.GlobalSettledAdmission.GloballySettledAdmission
        linearizer version proposal}
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head AppendReceipt AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head AppendReceipt AppendReceipt}
    {storeQ : AppendReceipt → AppendReceipt}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime}
    {history : FinalizedHistoryView EventQ Slot Head AppendReceipt}
    {ConfigLawful : AppendReceipt → Prop}
    {config : AppendReceipt}
    (binding :
      Residua.RCC.RuntimeFinalizedBridge.Binding
        formal actual history ConfigLawful config)
    (mismatch :
      receiptView.successorHead actual.transition.append.receipt ≠
        history.successorHead formal.history.event) :
    False :=
  mismatch binding.receiptFinalizedHeadAligned

end Residua.RCC.RuntimeFinalizedBridge.Tests

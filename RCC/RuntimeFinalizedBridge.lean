import RCC.RuntimeAdmissionBinding
import RCC.FinalizedHeadWindow

/-!
# Runtime/finalized-head bridge

This module is the narrow bridge between the actual runtime admission binding
and the RCC-45 finalized-head certificate.  The two certificates are not
allowed to name unrelated history events: `eventAligned` is an explicit
same-event witness.  Consequently the finalized successor head is the actual
post-store head, while the runtime receipt remains bound to the same event and
parent.  Effect settlement remains the existing globally-settled carrier.

The module deliberately does not prove storage implementation correctness,
finality liveness, or event discovery.  Those remain instance/refinement
obligations.  It only proves that once the two proof-carrying surfaces are
aligned, they cannot silently describe different durable histories.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RuntimeFinalizedBridge

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.EffectSettlement
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSettledAdmission
open Residua.RCC.RuntimeAdmissionBinding

universe u

/-! A runtime admission and a finalized-head certificate must share one event. -/
structure Binding
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
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (config : Config) : Type u where
  finalized :
    FinalizedHeadCert
      environment history ConfigLawful config proposal.expectedParent proposal
  eventAligned :
    finalized.admission.history.event = formal.history.event
  receiptFinalizedHeadAligned :
    receiptView.successorHead actual.transition.append.receipt =
      history.successorHead formal.history.event

theorem Binding.finalized_event
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
    (binding :
      Binding formal actual history ConfigLawful config) :
    history.finalized formal.history.event := by
  rw [← binding.eventAligned]
  exact binding.finalized.historyFinalized

/-! The finalized view and actual store cannot disagree about the successor. -/
theorem Binding.actual_post_head_is_finalized
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
    (binding :
      Binding formal actual history ConfigLawful config) :
    history.successorHead formal.history.event = binding.finalized.head ∧
      history.config formal.history.event = config ∧
      history.finalized formal.history.event := by
  have successorAtFinalized := binding.finalized.historyHeadBound
  have configAtFinalized := binding.finalized.historyConfigBound
  have finalizedAtFormal := binding.finalized_event
  constructor
  · simpa only [← binding.eventAligned] using successorAtFinalized
  · constructor
    · simpa only [← binding.eventAligned] using configAtFinalized
    · exact finalizedAtFormal

theorem Binding.actual_post_head_matches_finalized
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
    (binding :
      Binding formal actual history ConfigLawful config) :
    historyRuntime.actualHead actual.transition.append.postStore =
        binding.finalized.head := by
  have receiptSuccessor :=
    actual.transition.receiptSuccessorExact
  have historySuccessor :
      history.successorHead formal.history.event = binding.finalized.head := by
    simpa only [← binding.eventAligned] using binding.finalized.historyHeadBound
  exact receiptSuccessor.symm.trans
    (binding.receiptFinalizedHeadAligned.trans historySuccessor)

/-! A single headline exposes runtime authenticity, finality, and settlement. -/
theorem Binding.runtime_finalized_headline
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
    (binding :
      Binding formal actual history ConfigLawful config) :
    history.finalized formal.history.event ∧
      historyRuntime.actualContains
        actual.transition.append.postStore formal.history.event ∧
      historyRuntime.actualHead actual.transition.append.postStore =
        binding.finalized.head ∧
      receiptView.authentic actual.transition.append.receipt ∧
      receiptView.event actual.transition.append.receipt =
        formal.history.event ∧
      formal.effectObservation.historyRecorded = true := by
  have runtimeHeadline := actual.transition_headline
  have finalizedFacts := binding.actual_post_head_is_finalized
  constructor
  · exact finalizedFacts.2.2
  constructor
  · exact runtimeHeadline.2.1
  constructor
  · exact binding.actual_post_head_matches_finalized
  constructor
  · exact runtimeHeadline.2.2.1
  constructor
  · exact runtimeHeadline.2.2.2.1
  · have historyRecorded : formal.effectObservation.historyRecorded = true := by
      have coherent := formal.settled.coherent
      cases phase : formal.effectReceipt.phase <;>
        simp [SettlementCoherent, phase] at coherent
      all_goals exact coherent.2.1
    exact historyRecorded

end Residua.RCC.RuntimeFinalizedBridge

import RCCTests.RuntimeClosureBridge
import RCCTests.RuntimeFinalizedBridge

/-! RCC-73 candidate: finalized-head/runtime closure binding. -/

namespace Residua.RCC.RCC73Target

open Residua.RCC.RuntimeClosureBridge.Tests
open Residua.RCC.RuntimeFinalizedBridge.Tests
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.RuntimeAdmissionBinding
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSettledAdmission

universe u

abbrev RuntimeHeadClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
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
    (binding : RuntimeClosureBridge.Binding formal actual runtimeFinalized closure),
    historyRuntime.actualHead actual.transition.append.postStore = closure.snapshot.head

def runtimeHeadMatchesClosure : RuntimeHeadClaim :=
  @runtime_head_projects_to_closure_snapshot

abbrev WrongClosureClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
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
    (binding : RuntimeClosureBridge.Binding formal actual runtimeFinalized closure)
    (wrong : closure.finalizedHead.certificate.head ≠ runtimeFinalized.finalized.head),
    False

def wrongClosureHeadRefused : WrongClosureClaim :=
  @wrong_closure_head_refuses_binding

abbrev AlignedHeadClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
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
        formal actual history ConfigLawful config),
    historyRuntime.actualHead actual.transition.append.postStore =
      binding.finalized.head

def alignedHeadMatchesRuntime : AlignedHeadClaim :=
  @aligned_head_is_runtime_head

/-
  Keep the fully polymorphic receipt mismatch theorem at its stated type.
  Leaving it as a bare `@` term makes Lean try to synthesize the theorem's
  `DecidableEq` instances before the surrounding certificate has fixed the
  quantified types.  Naming the proposition first makes the evidence packet
  explicit and preserves the theorem without introducing an axiom or a
  `sorry`.
-/
abbrev ReceiptHeadMismatchClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version AppendReceipt : Type u}
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
        history.successorHead formal.history.event), False

def receiptHeadMismatchRefused : ReceiptHeadMismatchClaim :=
  by
    intro Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version AppendReceipt AuthorityEvidence
      instHead instGeneration environment linearizer version proposal formal
      historyRuntime receiptView storeQ effectRuntime actual history
      ConfigLawful config binding mismatch
    exact receipt_head_mismatch_refuses_binding
      (Store := PUnit) (StoreQ := PUnit) (Config := PUnit) binding mismatch

structure Certificate where
  /- These claims are used as a concrete RCC certificate.  Pin their otherwise
     unconstrained proposition universe to zero so Lean 4.29 cannot leave a
     proof-only universe metavariable in the packet type. -/
  runtimeHeadMatchesClosure : RuntimeHeadClaim.{0}
  wrongClosureHeadRefused : WrongClosureClaim.{0}
  alignedHeadMatchesRuntime : AlignedHeadClaim.{0}
  receiptHeadMismatchRefused : ReceiptHeadMismatchClaim.{0}

def certificate : Certificate where
  runtimeHeadMatchesClosure := Residua.RCC.RCC73Target.runtimeHeadMatchesClosure
  wrongClosureHeadRefused := Residua.RCC.RCC73Target.wrongClosureHeadRefused
  alignedHeadMatchesRuntime := Residua.RCC.RCC73Target.alignedHeadMatchesRuntime
  receiptHeadMismatchRefused := Residua.RCC.RCC73Target.receiptHeadMismatchRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC73Target

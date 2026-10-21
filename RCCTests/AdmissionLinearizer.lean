import RCC.AdmissionLinearizer

/-!
# RCC-42 / RCC-43 Admission Linearizer Witnesses

The tests pin two independent layers:

* a consistent finalized-decision log is single-valued per decision slot;
* the executable fenced finalizer and complete RCC-31/history bridge below
  realize that law without accepting an opaque effect tag.

The final countermodel shows why mere append order is insufficient: without
the consistency certificate a log can contain two different judgments for one
slot.
-/

namespace Residua.RCC.AdmissionLinearizer.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality

inductive Slot
  | deploy
  deriving DecidableEq

inductive Judgment
  | activate
  | rollback
  deriving DecidableEq

def activateDecision : FinalizedDecision Slot Judgment :=
  ⟨.deploy, .activate⟩

def rollbackDecision : FinalizedDecision Slot Judgment :=
  ⟨.deploy, .rollback⟩

def singletonLog : List (FinalizedDecision Slot Judgment) :=
  [activateDecision]

theorem singleton_log_consistent : ConsistentLog singletonLog := by
  intro first firstIn second secondIn sameSlot
  simp [singletonLog] at firstIn secondIn
  subst first
  subst second
  rfl

theorem singleton_log_finality_is_single_valued
    {j₁ j₂ : Judgment}
    (first : FinalizedByLog singletonLog .deploy j₁)
    (second : FinalizedByLog singletonLog .deploy j₂) :
    j₁ = j₂ := by
  exact finalized_by_consistent_log_unique
    singleton_log_consistent first second

def conflictingLog : List (FinalizedDecision Slot Judgment) :=
  [activateDecision, rollbackDecision]

theorem conflicting_log_is_not_consistent :
    ¬ ConsistentLog conflictingLog := by
  intro consistent
  have conflict := consistent
    activateDecision (by simp [conflictingLog])
    rollbackDecision (by simp [conflictingLog])
    rfl
  exact Judgment.noConfusion conflict

#print axioms finalized_by_consistent_log_unique
#print axioms singleton_log_finality_is_single_valued
#print axioms conflicting_log_is_not_consistent

end Residua.RCC.AdmissionLinearizer.Tests

namespace Residua.RCC.AdmissionLinearizer.RealizationTests

open Residua.RCC
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality

inductive Epoch
  | current
  deriving DecidableEq

inductive Config
  | primary
  deriving DecidableEq

inductive Head
  | canonical
  | stale
  deriving DecidableEq

inductive OperationClass
  | deploy
  deriving DecidableEq

inductive Scope
  | production
  deriving DecidableEq

inductive Sequence
  | first
  deriving DecidableEq

inductive PolicyRule
  | strict
  deriving DecidableEq

abbrev Slot :=
  DecisionSlot Epoch Config Head OperationClass Scope Sequence PolicyRule

inductive Judgment
  | activate
  | rollback
  deriving DecidableEq

inductive Generation
  | current
  deriving DecidableEq

def judgmentEq : JudgmentEquivalence Judgment where
  Equivalent := Eq
  refl := by intro judgment; rfl
  symm := by intro _ _ equal; exact equal.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide
    | .activate, .activate => isTrue rfl
    | .rollback, .rollback => isTrue rfl
    | .activate, .rollback => isFalse (by intro conflict; cases conflict)
    | .rollback, .activate => isFalse (by intro conflict; cases conflict)

def deploySlot : Slot where
  epoch := .current
  config := .primary
  parentHead := .canonical
  operationClass := .deploy
  scope := .production
  sequence := .first
  policy := .strict

def writerSpec : FencedWriterSpec Slot Head where
  slotParent := DecisionSlot.parentHead

def emptyState : FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun _ => none

def activatedState : FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun slot =>
    if slot = deploySlot then some .activate else none

def activateProposal : Proposal Slot Head Judgment :=
  ⟨deploySlot, .canonical, .activate⟩

def rollbackProposal : Proposal Slot Head Judgment :=
  ⟨deploySlot, .canonical, .rollback⟩

def staleProposal : Proposal Slot Head Judgment :=
  ⟨{ deploySlot with parentHead := .stale }, .stale, .activate⟩

/-- Proposal-indexed authority evidence used by the executable writer tests. -/
inductive AuthorityEvidence : Proposal Slot Head Judgment → Type
  | activateQuorum : AuthorityEvidence activateProposal
  | rollbackQuorum : AuthorityEvidence rollbackProposal
  | staleQuorum : AuthorityEvidence staleProposal

def activateAuthorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨activateProposal, .activateQuorum⟩

def rollbackAuthorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨rollbackProposal, .rollbackQuorum⟩

def staleAuthorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨staleProposal, .staleQuorum⟩

def activateRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨activateAuthorization, .current⟩

def activateFinalizeOutput :
    FencedFinalizeOutput writerSpec judgmentEq activatedState activateRequest where
  finality := {
    authorization := activateAuthorization
    linearizationEvidence := {
      generation := .current
      slot := deploySlot
      parentHead := .canonical
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .activate, rfl, rfl⟩

def activateFinalizeSuccess :
    SuccessfulFinalize
      writerSpec judgmentEq activatedState activateRequest where
  output := activateFinalizeOutput
  accepted := by
    rfl

/-- An uncommitted slot is a wake condition, never a locally fabricated finality. -/
theorem empty_writer_waits :
    fencedFinalize writerSpec judgmentEq emptyState
        activateRequest =
      .Await .decisionCommitPending := by
  rfl

/-- A canonical committed cell can issue a finality certificate. -/
theorem committed_writer_finalizes :
    ∃ output,
      fencedFinalize writerSpec judgmentEq activatedState
          activateRequest =
        .Ok output := by
  exact ⟨activateFinalizeOutput, activateFinalizeSuccess.accepted⟩

/-- Once one judgment occupies the slot, an inequivalent judgment is refused. -/
theorem conflicting_judgment_is_refused :
    fencedFinalize writerSpec judgmentEq activatedState
        ⟨rollbackAuthorization, .current⟩ =
      .Refuse .conflictingJudgment := by
  simp [fencedFinalize, writerSpec, activatedState, rollbackAuthorization,
    rollbackProposal, deploySlot, judgmentEq]

/-- CAS/head binding refuses a proposal derived from a stale canonical parent. -/
theorem stale_parent_is_refused :
    fencedFinalize writerSpec judgmentEq activatedState
        ⟨staleAuthorization, .current⟩ =
      .Refuse .staleParent := by
  simp [fencedFinalize, writerSpec, activatedState, staleAuthorization,
    staleProposal, deploySlot]

/-- A writer fenced out by a newer generation cannot finalize old work. -/
inductive RequestedGeneration
  | stale
  | current
  deriving DecidableEq

def currentGenerationState :
    FencedWriterState Slot Head Judgment RequestedGeneration where
  generation := .current
  canonicalHead := .canonical
  decisions := activatedState.decisions

theorem stale_generation_is_refused :
    fencedFinalize writerSpec judgmentEq currentGenerationState
        ⟨activateAuthorization, .stale⟩ =
      .Refuse .staleGeneration := by
  simp [fencedFinalize, currentGenerationState, writerSpec,
    activateAuthorization, activateProposal, deploySlot]

theorem actual_success_is_single_valued :
    judgmentEq.Equivalent activateProposal.judgment activateProposal.judgment :=
  successful_finalizes_same_slot_equivalent
    writerSpec judgmentEq activatedState
      activateFinalizeSuccess activateFinalizeSuccess rfl

/--
The second half of the cross-snapshot countermodel: an independent receiver
with the same slot, active generation, and canonical parent can locally commit
the conflicting judgment.
-/
def rollbackState : FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun slot =>
    if slot = deploySlot then some .rollback else none

def rollbackRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨rollbackAuthorization, .current⟩

def rollbackFinalizeOutput :
    FencedFinalizeOutput writerSpec judgmentEq rollbackState rollbackRequest where
  finality := {
    authorization := rollbackAuthorization
    linearizationEvidence := {
      generation := .current
      slot := deploySlot
      parentHead := .canonical
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .rollback, rfl, rfl⟩

def rollbackFinalizeSuccess :
    SuccessfulFinalize
      writerSpec judgmentEq rollbackState rollbackRequest where
  output := rollbackFinalizeOutput
  accepted := by
    rfl

/--
CM-RCC42-GLOBAL-01 (control): the old local-only API admits both conflicting
independent snapshots.  Each snapshot is internally single-valued, so local
proofs alone do not establish a global linearization.
-/
theorem conflicting_independent_snapshots_both_finalize_locally :
    fencedFinalize writerSpec judgmentEq activatedState activateRequest =
        .Ok activateFinalizeOutput ∧
      fencedFinalize writerSpec judgmentEq rollbackState rollbackRequest =
        .Ok rollbackFinalizeOutput := by
  exact ⟨activateFinalizeSuccess.accepted, rollbackFinalizeSuccess.accepted⟩

/-- A concrete non-vacuous canonical CAS evolution used by the positive tests. -/
def globalLinearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Nat writerSpec judgmentEq where
  Precedes := fun first second => first ≤ second
  precedesRefl := Nat.le_refl
  precedesTrans := by
    intro first second third firstBeforeSecond secondBeforeThird
    exact Nat.le_trans firstBeforeSecond secondBeforeThird
  comparable := Nat.le_total
  activeGeneration := fun _ _ => .current
  canonicalDecision := fun _ _ => activatedState.decisions
  decisionPreserved := by
    intro first second head slot judgment _ committed
    exact committed

def activatedCanonicalSnapshot (version : Nat) :
    CanonicalWriterSnapshot globalLinearizer version activatedState where
  generationBound := rfl
  decisionBound := by
    intro slot
    rfl

def globallyActivated (version : Nat) :
    GloballySuccessfulFinalize
      globalLinearizer version activatedState activateRequest where
  snapshot := activatedCanonicalSnapshot version
  localSuccess := activateFinalizeSuccess

/-- The proof-carrying global interface remains executable and non-vacuous. -/
theorem global_interface_finalizes :
    globalLinearizer.finalize
        0 activatedState (activatedCanonicalSnapshot 0) activateRequest =
      .Ok (globallyActivated 0) := by
  rfl

/--
Two distinct canonical versions of the same CAS history preserve the finalized
judgment.  This is the cross-snapshot theorem absent from the old local API.
-/
theorem distinct_canonical_snapshots_are_single_valued :
    judgmentEq.Equivalent
      activateProposal.judgment activateProposal.judgment :=
  global_finalizes_same_slot_parent_equivalent
    globalLinearizer (globallyActivated 0) (globallyActivated 1) rfl rfl

/-- The public RCC-42 law exposes slot, generation, and parent explicitly. -/
theorem admission_linearizer_at_most_one_finalized :
    judgmentEq.Equivalent
      activateProposal.judgment activateProposal.judgment :=
  globalLinearizer.atMostOneFinalized
    (globallyActivated 0) (globallyActivated 1) rfl rfl rfl

/--
CM-RCC42-GLOBAL-01 (mutant refusal): although the two independent snapshots
both return local `Ok`, no single canonical CAS evolution can certify both,
even at distinct comparable versions.  In particular, a generation handoff
cannot reset the decision at the same slot/parent.
-/
theorem conflicting_local_successes_cannot_both_be_globally_certified
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Nat writerSpec judgmentEq)
    (firstVersion secondVersion : Nat)
    (activateCanonical :
      CanonicalWriterSnapshot linearizer firstVersion activatedState)
    (rollbackCanonical :
      CanonicalWriterSnapshot linearizer secondVersion rollbackState) :
    False := by
  let activateGlobal :
      GloballySuccessfulFinalize
        linearizer firstVersion activatedState activateRequest := {
    snapshot := activateCanonical
    localSuccess := activateFinalizeSuccess
  }
  let rollbackGlobal :
      GloballySuccessfulFinalize
        linearizer secondVersion rollbackState rollbackRequest := {
    snapshot := rollbackCanonical
    localSuccess := rollbackFinalizeSuccess
  }
  have conflict :
      judgmentEq.Equivalent
        activateProposal.judgment rollbackProposal.judgment :=
    global_finalizes_same_slot_parent_equivalent
      linearizer activateGlobal rollbackGlobal rfl rfl
  exact Judgment.noConfusion conflict

/-- Same-version canonical snapshots cannot claim overlapping generations. -/
theorem canonical_snapshot_generation_is_single_valued :
    activatedState.generation = activatedState.generation :=
  canonical_snapshots_no_generation_overlap
    (activatedCanonicalSnapshot 0) (activatedCanonicalSnapshot 0) rfl

#print axioms empty_writer_waits
#print axioms committed_writer_finalizes
#print axioms conflicting_judgment_is_refused
#print axioms stale_parent_is_refused
#print axioms stale_generation_is_refused
#print axioms finalized_in_state_equivalent
#print axioms successful_finalizes_same_slot_equivalent
#print axioms actual_success_is_single_valued
#print axioms conflicting_independent_snapshots_both_finalize_locally
#print axioms global_interface_finalizes
#print axioms distinct_canonical_snapshots_are_single_valued
#print axioms admission_linearizer_at_most_one_finalized
#print axioms conflicting_local_successes_cannot_both_be_globally_certified
#print axioms canonical_snapshot_generation_is_single_valued

end Residua.RCC.AdmissionLinearizer.RealizationTests

namespace Residua.RCC.AdmissionLinearizer.SettlementBridgeTests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.EffectSettlement
open Residua.RCC.AdmissionLinearizer.RealizationTests

inductive EffectSlot
  | store
  deriving DecidableEq

inductive Occurrence
  | deployment
  deriving DecidableEq

inductive FailureName
  | receiverRejected
  deriving DecidableEq

inductive EventQ
  | activationRecorded
  deriving DecidableEq

abbrev activatedState :=
  RealizationTests.activatedState

def deploymentEffect : ExternalEffect Occurrence Head EffectSlot where
  occurrence := .deployment
  expectedParent := .canonical
  effectSlot := .store

def deploymentReceipt :
    EffectReceipt
      Epoch Head EffectSlot Generation Occurrence FailureName where
  occurrence := .deployment
  fence := {
    epoch := .current
    head := .canonical
    effectSlot := .store
    generation := .current
  }
  phase := .recorded

def settledObservation :
    EffectObservation
      Epoch Head EffectSlot Generation Occurrence FailureName where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some deploymentReceipt

def appliedUnrecordedObservation :
    EffectObservation
      Epoch Head EffectSlot Generation Occurrence FailureName where
  worldApplied := true
  historyRecorded := false
  compensationApplied := false
  receipt := some deploymentReceipt

def effectSnapshot :
    EffectSnapshot
      Epoch Head EffectSlot Generation Occurrence FailureName where
  epoch := .current
  head := .canonical
  currentGeneration := fun _ => .current
  policyTerminalFailure := fun _ => False
  externalEffects := [deploymentEffect]
  observe := fun _ => some settledObservation

def splitEffectSnapshot :
    EffectSnapshot
      Epoch Head EffectSlot Generation Occurrence FailureName where
  epoch := .current
  head := .canonical
  currentGeneration := fun _ => .current
  policyTerminalFailure := fun _ => False
  externalEffects := [deploymentEffect]
  observe := fun _ => some appliedUnrecordedObservation

def historyView :
    HistoryEventView EventQ Slot Head Judgment Occurrence where
  preHead := fun _ => .canonical
  slot := fun _ => deploySlot
  judgment := fun _ => .activate
  occurrence := fun _ => .deployment

def recordedHistory : CanonicalHistorySnapshot EventQ Head where
  canonicalHead := .canonical
  contains := fun _ => true
  durableContains := fun _ => True
  containsSound := by intro _ _; trivial

def unrecordedHistory : CanonicalHistorySnapshot EventQ Head where
  canonicalHead := .canonical
  contains := fun _ => false
  durableContains := fun _ => False
  containsSound := by intro _ impossible; contradiction

def admissionEnvironment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ where
  writerSpec := writerSpec
  equivalence := judgmentEq
  writerState := activatedState
  effectSnapshot := effectSnapshot
  historyView := historyView
  historySnapshot := recordedHistory
  occurrenceOf := fun _ => .deployment
  effectSlotOf := fun _ => .store
  effectHeadBound := rfl
  historyHeadBound := rfl
  generationCoherent := by intro _; rfl

def authorizedOnlyEnvironment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ :=
  { admissionEnvironment with writerState := emptyState }

def unsettledEnvironment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ :=
  { admissionEnvironment with effectSnapshot := splitEffectSnapshot }

def unrecordedEnvironment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ :=
  { admissionEnvironment with historySnapshot := unrecordedHistory }

/-- Positive inhabitant: the complete RCC-42/RCC-31/history product is real. -/
def completeAdmission : SettledAdmission admissionEnvironment activateProposal where
  finalizeRequest := activateRequest
  proposalBound := rfl
  finalizeSuccess := activateFinalizeSuccess
  effect := deploymentEffect
  effectDeclared := by simp [admissionEnvironment, effectSnapshot]
  effectOccurrenceBound := rfl
  effectParentBound := rfl
  effectSlotBound := rfl
  effectObservation := settledObservation
  effectReceipt := deploymentReceipt
  settled := by
    refine {
      observed := rfl
      receiptPresent := rfl
      epochBound := rfl
      expectedParentBound := rfl
      canonicalHeadBound := rfl
      slotBound := rfl
      generationBound := rfl
      occurrenceBound := rfl
      coherent := ?_
    }
    simp [SettlementCoherent, settledObservation, deploymentReceipt]
  history := {
    event := .activationRecorded
    recorded := rfl
    durablyRecorded := True.intro
    canonicalHeadBound := rfl
    preHeadBound := rfl
    slotBound := rfl
    judgmentBound := rfl
    occurrenceBound := rfl
  }

theorem complete_admission_has_at_most_one_judgment :
    admissionEnvironment.equivalence.Equivalent
      activateProposal.judgment activateProposal.judgment :=
  settled_admissions_same_slot_equivalent
    completeAdmission completeAdmission rfl

/-- CM-RCC43-01: authorization without actual finalization cannot admit. -/
theorem authorized_only_cannot_admit :
    ¬ Nonempty
      (SettledAdmission authorizedOnlyEnvironment activateProposal) := by
  intro alleged
  obtain ⟨admission⟩ := alleged
  rcases admission.finalizeSuccess.output.finalized with
    ⟨_, _, stored, storedAt, _⟩
  simp [authorizedOnlyEnvironment, emptyState] at storedAt

/-- CM-RCC43-02: finalized but applied-unrecorded effect cannot admit. -/
theorem finalized_unsettled_cannot_admit :
    ¬ Nonempty
      (SettledAdmission unsettledEnvironment activateProposal) := by
  intro alleged
  obtain ⟨admission⟩ := alleged
  have observed := admission.settled.observed
  change
    some appliedUnrecordedObservation =
      some admission.effectObservation at observed
  have observationEq :
      appliedUnrecordedObservation = admission.effectObservation :=
    Option.some.inj observed
  have present := admission.settled.receiptPresent
  rw [← observationEq] at present
  change some deploymentReceipt = some admission.effectReceipt at present
  have receiptEq : deploymentReceipt = admission.effectReceipt :=
    Option.some.inj present
  have coherent := admission.settled.coherent
  rw [← observationEq, ← receiptEq] at coherent
  simp [SettlementCoherent, deploymentReceipt, appliedUnrecordedObservation]
    at coherent

/-- CM-RCC43-03: settled effect without canonical event inclusion cannot admit. -/
theorem settled_unrecorded_cannot_admit :
    ¬ Nonempty
      (SettledAdmission unrecordedEnvironment activateProposal) := by
  intro alleged
  obtain ⟨admission⟩ := alleged
  have durable := admission.history.durablyRecorded
  exact durable

/--
RCC-43 must expose both the RCC-31 terminal effect proof and the durable
canonical-history inclusion proof.  A finality-only witness cannot inhabit
this theorem's premise.
-/
theorem settled_admission_is_terminal_and_recorded
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type}
    {AuthorityEvidence :
      AuthorizationFinality.Proposal Slot Head Judgment → Type}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {proposal : AuthorizationFinality.Proposal Slot Head Judgment}
    (admission : SettledAdmission environment proposal) :
    EffectPhase.IsTerminal
        environment.effectSnapshot.policyTerminalFailure
        admission.effectReceipt.phase ∧
      environment.historySnapshot.contains admission.history.event = true := by
  exact ⟨settlement_coherent_is_terminal
    admission.effectObservation admission.effectReceipt
      admission.settled.coherent,
    admission.history.recorded⟩

#print axioms settled_admission_is_terminal_and_recorded
#print axioms settled_admissions_same_slot_equivalent
#print axioms settled_admission_effect_terminal
#print axioms settled_admission_implies_authorized
#print axioms settled_admission_history_durable
#print axioms complete_admission_has_at_most_one_judgment
#print axioms authorized_only_cannot_admit
#print axioms finalized_unsettled_cannot_admit
#print axioms settled_unrecorded_cannot_admit

end Residua.RCC.AdmissionLinearizer.SettlementBridgeTests

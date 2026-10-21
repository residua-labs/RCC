import RCC.EffectSettlement

/-!
# RCC-31 Fenced Effect Settlement Witnesses

These tests pin the phase surface, the typed fence coordinates, the positive
closure theorem, and load-bearing countermodels:

* the world changed but history did not record it;
* history says `Recorded` although the world was not changed;
* policy did not admit a named failure as terminal;
* `Recorded` is stale after compensation has also happened;
* each receiver fence coordinate is independently stale;
* the receipt names another logical occurrence;
* the observation or receipt is absent;
* compensation is still pending.

They deliberately do not claim global ACID, delivery liveness, or successful
compensation.
-/

namespace Residua.RCC.EffectSettlement.Tests

open Residua.RCC.EffectSettlement

inductive DemoEpoch
  | current
  | stale
  deriving DecidableEq

inductive DemoHead
  | current
  | stale
  deriving DecidableEq

inductive DemoSlot
  | charge
  | refund
  deriving DecidableEq

inductive DemoOccurrence
  | payment
  | other
  deriving DecidableEq

inductive DemoFailure
  | declined
  | transient
  deriving DecidableEq

abbrev DemoFence :=
  FencingToken DemoEpoch DemoHead DemoSlot Nat

abbrev DemoReceipt :=
  EffectReceipt DemoEpoch DemoHead DemoSlot Nat DemoOccurrence DemoFailure

abbrev DemoObservation :=
  EffectObservation DemoEpoch DemoHead DemoSlot Nat DemoOccurrence DemoFailure

abbrev DemoEffect :=
  ExternalEffect DemoOccurrence DemoHead DemoSlot

abbrev DemoSnapshot :=
  EffectSnapshot DemoEpoch DemoHead DemoSlot Nat DemoOccurrence DemoFailure

def terminalFailurePolicy : DemoFailure → Prop
  | .declined => True
  | .transient => False

def paymentEffect : DemoEffect where
  occurrence := .payment
  expectedParent := .current
  effectSlot := .charge

def currentFence : DemoFence where
  epoch := .current
  head := .current
  effectSlot := .charge
  generation := 7

def recordedReceipt : DemoReceipt where
  occurrence := .payment
  fence := currentFence
  phase := .recorded

def recordedObservation : DemoObservation where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some recordedReceipt

def closedSnapshot : DemoSnapshot where
  epoch := .current
  head := .current
  currentGeneration := fun _ => 7
  policyTerminalFailure := terminalFailurePolicy
  externalEffects := [paymentEffect]
  observe := fun
    | .payment => some recordedObservation
    | .other => none

theorem closedSnapshotProof : EpochEffectClosed closedSnapshot := by
  intro effect member
  simp only [closedSnapshot, List.mem_cons, List.mem_nil_iff, or_false] at member
  subst effect
  exact
    ⟨recordedObservation, recordedReceipt,
      { observed := rfl
      , receiptPresent := rfl
      , epochBound := rfl
      , expectedParentBound := rfl
      , canonicalHeadBound := rfl
      , slotBound := rfl
      , generationBound := rfl
      , occurrenceBound := rfl
      , coherent := by
          simp [SettlementCoherent, recordedObservation, recordedReceipt] }⟩

theorem closure_has_fenced_settled_receipt :
    ∀ effect, effect ∈ closedSnapshot.externalEffects →
      ∃ observation receipt,
        FencedSettledReceipt closedSnapshot effect observation receipt :=
  epoch_effect_closed_every_external_effect_settled closedSnapshot
    closedSnapshotProof

theorem closure_has_no_world_history_split :
    ∀ effect, effect ∈ closedSnapshot.externalEffects →
      ∃ observation receipt,
        closedSnapshot.observe effect.occurrence = some observation ∧
        observation.receipt = some receipt ∧
        ¬ EffectAppliedUnrecorded observation ∧
        ¬ EffectRecordedNotApplied observation receipt ∧
        ¬ CompensationStillPending receipt :=
  epoch_effect_closed_excludes_unsettled_phases closedSnapshot
    closedSnapshotProof

/-! The phase algebra is exactly the seven ADR §7.18 constructors. -/

theorem effect_phase_exactly_seven (phase : EffectPhase DemoFailure) :
    phase = .none ∨
      phase = .prepared ∨
      phase = .applied ∨
      phase = .recorded ∨
      phase = .compensationPending ∨
      phase = .compensated ∨
      ∃ failure, phase = .failedNamed failure := by
  cases phase with
  | none => simp
  | prepared => simp
  | applied => simp
  | recorded => simp
  | compensationPending => simp
  | compensated => simp
  | failedNamed failure =>
      right
      right
      right
      right
      right
      right
      exact ⟨failure, rfl⟩

example :
    EffectPhase.IsTerminal terminalFailurePolicy
      (EffectPhase.recorded : EffectPhase DemoFailure) := by
  simp [EffectPhase.IsTerminal]

example :
    EffectPhase.IsTerminal terminalFailurePolicy
      (EffectPhase.compensated : EffectPhase DemoFailure) := by
  simp [EffectPhase.IsTerminal]

example :
    EffectPhase.IsTerminal terminalFailurePolicy
      (EffectPhase.failedNamed DemoFailure.declined : EffectPhase DemoFailure) := by
  simp [EffectPhase.IsTerminal, terminalFailurePolicy]

def approvedFailureReceipt : DemoReceipt where
  occurrence := .payment
  fence := currentFence
  phase := .failedNamed .declined

def approvedFailureObservation : DemoObservation where
  worldApplied := false
  historyRecorded := true
  compensationApplied := false
  receipt := some approvedFailureReceipt

theorem approved_named_failure_can_settle :
    SettlementCoherent terminalFailurePolicy
      approvedFailureObservation approvedFailureReceipt := by
  simp [SettlementCoherent, terminalFailurePolicy, approvedFailureObservation,
    approvedFailureReceipt]

def unapprovedFailureReceipt : DemoReceipt where
  occurrence := .payment
  fence := currentFence
  phase := .failedNamed .transient

def unapprovedFailureObservation : DemoObservation where
  worldApplied := false
  historyRecorded := true
  compensationApplied := false
  receipt := some unapprovedFailureReceipt

/-!
CM-EFFECT-00A: a raw named failure is not terminal authority.  The pre-state
policy must admit that exact failure.
-/
theorem unapproved_named_failure_cannot_settle :
    ¬ SettlementCoherent terminalFailurePolicy
      unapprovedFailureObservation unapprovedFailureReceipt := by
  simp [SettlementCoherent, terminalFailurePolicy, unapprovedFailureReceipt]

def recordedAfterCompensationObservation : DemoObservation where
  worldApplied := true
  historyRecorded := true
  compensationApplied := true
  receipt := some recordedReceipt

/-!
CM-EFFECT-00B: a journal still marked `Recorded` after compensation happened
is a stale phase, not a settled enactment.
-/
theorem recorded_after_compensation_cannot_settle :
    ¬ SettlementCoherent terminalFailurePolicy
      recordedAfterCompensationObservation recordedReceipt := by
  simp [SettlementCoherent, recordedAfterCompensationObservation,
    recordedReceipt]

/-! CM-EFFECT-01: the world changed but no durable history record exists. -/

def appliedUnrecordedReceipt : DemoReceipt where
  occurrence := .payment
  fence := currentFence
  phase := .applied

def appliedUnrecordedObservation : DemoObservation where
  worldApplied := true
  historyRecorded := false
  compensationApplied := false
  receipt := some appliedUnrecordedReceipt

theorem applied_unrecorded_is_named_split :
    EffectAppliedUnrecorded appliedUnrecordedObservation := by
  simp [EffectAppliedUnrecorded, appliedUnrecordedObservation]

theorem applied_unrecorded_cannot_settle :
    ¬ SettlementCoherent terminalFailurePolicy
      appliedUnrecordedObservation appliedUnrecordedReceipt := by
  simp [SettlementCoherent, appliedUnrecordedReceipt]

/-! CM-EFFECT-02: history says Recorded although the world was not changed. -/

def recordedNotAppliedObservation : DemoObservation where
  worldApplied := false
  historyRecorded := true
  compensationApplied := false
  receipt := some recordedReceipt

theorem recorded_not_applied_is_named_split :
    EffectRecordedNotApplied recordedNotAppliedObservation recordedReceipt := by
  simp [EffectRecordedNotApplied, recordedNotAppliedObservation, recordedReceipt]

theorem recorded_not_applied_cannot_settle :
    ¬ SettlementCoherent terminalFailurePolicy
      recordedNotAppliedObservation recordedReceipt := by
  simp [SettlementCoherent, recordedNotAppliedObservation, recordedReceipt]

def snapshotWith (observation : DemoObservation) : DemoSnapshot where
  epoch := .current
  head := .current
  currentGeneration := fun _ => 7
  policyTerminalFailure := terminalFailurePolicy
  externalEffects := [paymentEffect]
  observe := fun
    | .payment => some observation
    | .other => none

/-! CM-EFFECT-03A: stale epoch is independently rejected. -/

def staleEpochReceipt : DemoReceipt where
  occurrence := .payment
  fence := { currentFence with epoch := .stale }
  phase := .recorded

def staleEpochObservation : DemoObservation :=
  { recordedObservation with receipt := some staleEpochReceipt }

theorem stale_epoch_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith staleEpochObservation) paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [staleEpochObservation] at receiptPresent
  subst receipt
  have : DemoEpoch.stale = .current := settled.epochBound
  cases this

/-! CM-EFFECT-03B: stale expected-parent fence is independently rejected. -/

def staleHeadReceipt : DemoReceipt where
  occurrence := .payment
  fence := { currentFence with head := .stale }
  phase := .recorded

def staleHeadObservation : DemoObservation :=
  { recordedObservation with receipt := some staleHeadReceipt }

theorem stale_parent_fence_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith staleHeadObservation) paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [staleHeadObservation] at receiptPresent
  subst receipt
  have : DemoHead.stale = .current := settled.expectedParentBound
  cases this

/-! CM-EFFECT-03C: a noncanonical declared effect parent is rejected. -/

def noncanonicalParentEffect : DemoEffect where
  occurrence := .payment
  expectedParent := .stale
  effectSlot := .charge

def noncanonicalParentSnapshot : DemoSnapshot where
  epoch := .current
  head := .current
  currentGeneration := fun _ => 7
  policyTerminalFailure := terminalFailurePolicy
  externalEffects := [noncanonicalParentEffect]
  observe := fun
    | .payment => some staleHeadObservation
    | .other => none

theorem noncanonical_effect_parent_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt noncanonicalParentSnapshot noncanonicalParentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have : DemoHead.stale = .current := settled.canonicalHeadBound
  cases this

/-! CM-EFFECT-03D: wrong effect slot is independently rejected. -/

def wrongSlotReceipt : DemoReceipt where
  occurrence := .payment
  fence := { currentFence with effectSlot := .refund }
  phase := .recorded

def wrongSlotObservation : DemoObservation :=
  { recordedObservation with receipt := some wrongSlotReceipt }

theorem wrong_slot_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith wrongSlotObservation) paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [wrongSlotObservation] at receiptPresent
  subst receipt
  have : DemoSlot.refund = .charge := settled.slotBound
  cases this

/-! CM-EFFECT-03E: stale receiver generation is independently rejected. -/

def staleGenerationReceipt : DemoReceipt where
  occurrence := .payment
  fence := { currentFence with generation := 6 }
  phase := .recorded

def staleGenerationObservation : DemoObservation :=
  { recordedObservation with receipt := some staleGenerationReceipt }

theorem stale_generation_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith staleGenerationObservation)
        paymentEffect observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [staleGenerationObservation] at receiptPresent
  subst receipt
  have : (6 : Nat) = 7 := settled.generationBound
  cases this

/-! CM-EFFECT-04: a receipt for another occurrence cannot settle this effect. -/

def wrongOccurrenceReceipt : DemoReceipt where
  occurrence := .other
  fence := currentFence
  phase := .recorded

def wrongOccurrenceObservation : DemoObservation where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some wrongOccurrenceReceipt

theorem missing_occurrence_binding_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith wrongOccurrenceObservation) paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [wrongOccurrenceObservation] at receiptPresent
  subst receipt
  have : DemoOccurrence.other = .payment := settled.occurrenceBound
  cases this

/-! CM-EFFECT-04B: an absent observation cannot be treated as settlement. -/

def missingObservationSnapshot : DemoSnapshot where
  epoch := .current
  head := .current
  currentGeneration := fun _ => 7
  policyTerminalFailure := terminalFailurePolicy
  externalEffects := [paymentEffect]
  observe := fun _ => none

theorem missing_observation_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt missingObservationSnapshot paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [missingObservationSnapshot, paymentEffect] at observed

/-! CM-EFFECT-04C: an observation without its durable receipt cannot settle. -/

def missingReceiptObservation : DemoObservation where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := none

theorem missing_receipt_cannot_close_effect :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith missingReceiptObservation) paymentEffect
        observation receipt := by
  rintro ⟨observation, receipt, settled⟩
  have observed := settled.observed
  simp [snapshotWith, paymentEffect] at observed
  subst observation
  have receiptPresent := settled.receiptPresent
  simp [missingReceiptObservation] at receiptPresent

/-! CM-EFFECT-05: compensation-in-flight is Runtime, never closed. -/

def pendingCompensationReceipt : DemoReceipt where
  occurrence := .payment
  fence := currentFence
  phase := .compensationPending

def pendingCompensationObservation : DemoObservation where
  worldApplied := true
  historyRecorded := false
  compensationApplied := false
  receipt := some pendingCompensationReceipt

theorem pending_compensation_is_not_terminal :
    CompensationStillPending pendingCompensationReceipt ∧
      ¬ EffectPhase.IsTerminal terminalFailurePolicy
        pendingCompensationReceipt.phase := by
  constructor <;>
    simp [CompensationStillPending, EffectPhase.IsTerminal,
      pendingCompensationReceipt]

theorem pending_compensation_cannot_settle :
    ¬ SettlementCoherent terminalFailurePolicy
      pendingCompensationObservation pendingCompensationReceipt := by
  simp [SettlementCoherent, pendingCompensationReceipt]

#print axioms epoch_effect_closed_every_external_effect_settled
#print axioms epoch_effect_closed_excludes_unsettled_phases
#print axioms settlement_coherent_failed_named_policy_terminal
#print axioms settlement_coherent_recorded_not_compensated
#print axioms closure_has_fenced_settled_receipt
#print axioms closure_has_no_world_history_split
#print axioms effect_phase_exactly_seven
#print axioms approved_named_failure_can_settle
#print axioms unapproved_named_failure_cannot_settle
#print axioms recorded_after_compensation_cannot_settle
#print axioms applied_unrecorded_cannot_settle
#print axioms recorded_not_applied_cannot_settle
#print axioms stale_epoch_cannot_close_effect
#print axioms stale_parent_fence_cannot_close_effect
#print axioms noncanonical_effect_parent_cannot_close_effect
#print axioms wrong_slot_cannot_close_effect
#print axioms stale_generation_cannot_close_effect
#print axioms missing_occurrence_binding_cannot_close_effect
#print axioms missing_observation_cannot_close_effect
#print axioms missing_receipt_cannot_close_effect
#print axioms pending_compensation_cannot_settle

end Residua.RCC.EffectSettlement.Tests


import RCC.EffectSettlement
import RCCTests.EffectSettlement

/-!
# RCC-31 target package

This candidate packages fenced effect settlement.  Every declared external
effect must have an observed, durable receipt bound to the current epoch,
canonical parent, effect slot, generation, and logical occurrence, with a
coherent terminal phase.  The official registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC31Target

open Residua.RCC.EffectSettlement
open Residua.RCC.EffectSettlement.Tests

universe u v w x y z

theorem generic_effect_closed_settles_every_external
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (closed : EpochEffectClosed snapshot) :
    ∀ effect, effect ∈ snapshot.externalEffects →
      ∃ observation receipt,
        FencedSettledReceipt snapshot effect observation receipt :=
  epoch_effect_closed_every_external_effect_settled snapshot closed

theorem generic_settlement_is_terminal
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent : SettlementCoherent policyTerminalFailure observation receipt) :
    EffectPhase.IsTerminal policyTerminalFailure receipt.phase :=
  settlement_coherent_is_terminal observation receipt coherent

structure ConcreteWitness : Prop where
  settledSnapshotProof :
    EpochEffectClosed Residua.RCC.EffectSettlement.Tests.closedSnapshot
  fencedReceiptExists :
    ∀ effect,
      effect ∈ Residua.RCC.EffectSettlement.Tests.closedSnapshot.externalEffects →
      ∃ observation receipt,
        FencedSettledReceipt
          Residua.RCC.EffectSettlement.Tests.closedSnapshot effect
            observation receipt
  unsettledExcluded :
    ∀ effect,
      effect ∈ Residua.RCC.EffectSettlement.Tests.closedSnapshot.externalEffects →
      ∃ observation receipt,
        Residua.RCC.EffectSettlement.Tests.closedSnapshot.observe
            effect.occurrence = some observation ∧
        observation.receipt = some receipt ∧
        ¬ EffectAppliedUnrecorded observation ∧
        ¬ EffectRecordedNotApplied observation receipt ∧
        ¬ CompensationStillPending receipt
  phaseSurface :
    ∀ phase : EffectPhase DemoFailure,
      phase = .none ∨ phase = .prepared ∨ phase = .applied ∨
        phase = .recorded ∨ phase = .compensationPending ∨
        phase = .compensated ∨ ∃ failure, phase = .failedNamed failure

structure MutantRefusal : Prop where
  unapprovedFailureRefused :
    ¬ SettlementCoherent terminalFailurePolicy
      unapprovedFailureObservation unapprovedFailureReceipt
  recordedAfterCompensationRefused :
    ¬ SettlementCoherent terminalFailurePolicy
      recordedAfterCompensationObservation recordedReceipt
  appliedUnrecordedRefused :
    EffectAppliedUnrecorded appliedUnrecordedObservation ∧
      ¬ SettlementCoherent terminalFailurePolicy
        appliedUnrecordedObservation appliedUnrecordedReceipt
  recordedNotAppliedRefused :
    EffectRecordedNotApplied recordedNotAppliedObservation recordedReceipt ∧
      ¬ SettlementCoherent terminalFailurePolicy
        recordedNotAppliedObservation recordedReceipt
  staleEpochRefused :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith staleEpochObservation) paymentEffect
        observation receipt
  staleHeadRefused :
    ¬ ∃ observation receipt,
      FencedSettledReceipt (snapshotWith staleHeadObservation) paymentEffect
        observation receipt
  missingObservationRefused :
    ¬ ∃ observation receipt,
      FencedSettledReceipt missingObservationSnapshot paymentEffect
        observation receipt
  pendingCompensationRefused :
    ¬ SettlementCoherent terminalFailurePolicy
      recordedObservation
      { recordedReceipt with phase := .compensationPending }

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { settledSnapshotProof := closedSnapshotProof
      fencedReceiptExists := closure_has_fenced_settled_receipt
      unsettledExcluded := closure_has_no_world_history_split
      phaseSurface := effect_phase_exactly_seven }
  mutants :=
    { unapprovedFailureRefused := unapproved_named_failure_cannot_settle
      recordedAfterCompensationRefused := recorded_after_compensation_cannot_settle
      appliedUnrecordedRefused :=
        ⟨applied_unrecorded_is_named_split, applied_unrecorded_cannot_settle⟩
      recordedNotAppliedRefused :=
        ⟨recorded_not_applied_is_named_split, recorded_not_applied_cannot_settle⟩
      staleEpochRefused := stale_epoch_cannot_close_effect
      staleHeadRefused := stale_parent_fence_cannot_close_effect
      missingObservationRefused := missing_observation_cannot_close_effect
      pendingCompensationRefused := pending_compensation_cannot_settle }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC31Target


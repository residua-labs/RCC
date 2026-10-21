/-!
# RCC-31 Fenced Effect Settlement

An epoch may close only when every declared external effect has a durable
settlement receipt.  The receipt is bound to the logical occurrence, expected
history parent, current epoch, effect slot, and receiver generation.  Its phase
must also agree with the observed physical world and durable history.

This is a finite safety kernel.  It does not claim global ACID, delivery
liveness, successful compensation, or authenticity of the supplied
observations.  Those remain implementation-binding and temporal obligations.

Prelude-only Lean 4.14; no Mathlib and no custom axioms.  The exported theorem
surface may report Lean's standard `propext`.
-/

namespace Residua.RCC.EffectSettlement

universe u v w x y z

/-- The seven effect-journal phases frozen by ADR §7.18. -/
inductive EffectPhase (FailureName : Type u) where
  | none
  | prepared
  | applied
  | recorded
  | compensationPending
  | compensated
  | failedNamed (failure : FailureName)
  deriving DecidableEq, Repr

namespace EffectPhase

/--
Only a recorded enactment, a recorded compensation, or a policy-terminal
named failure is a settlement phase.
-/
def IsTerminal {FailureName : Type u}
    (policyTerminal : FailureName → Prop) : EffectPhase FailureName → Prop
  | .recorded => True
  | .compensated => True
  | .failedNamed failure => policyTerminal failure
  | _ => False

end EffectPhase

/--
The receiver fence is typed by all four coordinates.  The effect receipt below
must carry the current token; a history CAS alone is not an effect fence.
-/
structure FencingToken
    (Epoch : Type u) (Head : Type v)
    (EffectSlot : Type w) (Generation : Type x) where
  epoch : Epoch
  head : Head
  effectSlot : EffectSlot
  generation : Generation
  deriving DecidableEq, Repr

/-- One external effect declared by the current epoch. -/
structure ExternalEffect
    (Occurrence : Type u) (Head : Type v) (EffectSlot : Type w) where
  occurrence : Occurrence
  expectedParent : Head
  effectSlot : EffectSlot
  deriving DecidableEq, Repr

/-- Durable receiver/history receipt for one effect occurrence. -/
structure EffectReceipt
    (Epoch : Type u) (Head : Type v)
    (EffectSlot : Type w) (Generation : Type x)
    (Occurrence : Type y) (FailureName : Type z) where
  occurrence : Occurrence
  fence : FencingToken Epoch Head EffectSlot Generation
  phase : EffectPhase FailureName
  deriving DecidableEq, Repr

/--
Evidence observed at the effect/history boundary.

`worldApplied` records that the external effect happened.
`historyRecorded` records that canonical history durably describes the
terminal outcome. `compensationApplied` records a completed compensating
effect.  The booleans are evidence inputs; RCC-31 proves only the safety of
closure relative to their implementation binding.
-/
structure EffectObservation
    (Epoch : Type u) (Head : Type v)
    (EffectSlot : Type w) (Generation : Type x)
    (Occurrence : Type y) (FailureName : Type z) where
  worldApplied : Bool
  historyRecorded : Bool
  compensationApplied : Bool
  receipt : Option
    (EffectReceipt Epoch Head EffectSlot Generation Occurrence FailureName)
  deriving DecidableEq, Repr

/-- Sealed epoch snapshot used by the settlement checker. -/
structure EffectSnapshot
    (Epoch : Type u) (Head : Type v)
    (EffectSlot : Type w) (Generation : Type x)
    (Occurrence : Type y) (FailureName : Type z) where
  epoch : Epoch
  head : Head
  currentGeneration : EffectSlot → Generation
  /-- Pre-state policy decides which exact named failures are terminal. -/
  policyTerminalFailure : FailureName → Prop
  externalEffects : List (ExternalEffect Occurrence Head EffectSlot)
  observe : Occurrence →
    Option
      (EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)

/-- Physical effect happened without a durable history record. -/
def EffectAppliedUnrecorded
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName) : Prop :=
  observation.worldApplied = true ∧ observation.historyRecorded = false

/-- History claims a recorded enactment although the world was not changed. -/
def EffectRecordedNotApplied
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName) : Prop :=
  receipt.phase = .recorded ∧
    observation.historyRecorded = true ∧
    observation.worldApplied = false

/-- Compensation has not reached a terminal receipt. -/
def CompensationStillPending
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName) : Prop :=
  receipt.phase = .compensationPending

/--
The journal phase must agree with both the observed external world and durable
history.

* `Recorded`: enactment happened, history recorded it, and no compensation was
  also applied.
* `Compensated`: enactment, compensation, and history record all exist.
* `FailedNamed`: pre-state policy admits the exact failure as terminal, history
  records it, and either enactment never happened or a compensation completed.

Every nonterminal phase is incoherent with epoch closure.
-/
def SettlementCoherent
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (policyTerminalFailure : FailureName → Prop)
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName) : Prop :=
  match receipt.phase with
  | .recorded =>
      observation.worldApplied = true ∧
        observation.historyRecorded = true ∧
        observation.compensationApplied = false
  | .compensated =>
      observation.worldApplied = true ∧
        observation.historyRecorded = true ∧
        observation.compensationApplied = true
  | .failedNamed failure =>
      policyTerminalFailure failure ∧
        observation.historyRecorded = true ∧
        (observation.worldApplied = false ∨
          observation.compensationApplied = true)
  | _ => False

/--
Proof-carrying settlement of one external effect at one sealed snapshot.
Every identity coordinate is explicit; none is inferred from a content hash.
-/
structure FencedSettledReceipt
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (effect : ExternalEffect Occurrence Head EffectSlot)
    (observation :
      EffectObservation Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt Epoch Head EffectSlot Generation Occurrence FailureName) :
    Prop where
  observed : snapshot.observe effect.occurrence = some observation
  receiptPresent : observation.receipt = some receipt
  epochBound : receipt.fence.epoch = snapshot.epoch
  expectedParentBound : receipt.fence.head = effect.expectedParent
  canonicalHeadBound : effect.expectedParent = snapshot.head
  slotBound : receipt.fence.effectSlot = effect.effectSlot
  generationBound :
    receipt.fence.generation =
      snapshot.currentGeneration effect.effectSlot
  occurrenceBound : receipt.occurrence = effect.occurrence
  coherent :
    SettlementCoherent snapshot.policyTerminalFailure observation receipt

/--
Effect closure quantifies over the sealed list of external effects.  Pure
history-only transitions are outside this carrier.
-/
def EpochEffectClosed
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName) :
    Prop :=
  ∀ effect, effect ∈ snapshot.externalEffects →
    ∃ observation receipt,
      FencedSettledReceipt snapshot effect observation receipt

/-- RCC-31: every external effect at closure has a fenced settled receipt. -/
theorem epoch_effect_closed_every_external_effect_settled
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (closed : EpochEffectClosed snapshot) :
    ∀ effect, effect ∈ snapshot.externalEffects →
      ∃ observation receipt,
        FencedSettledReceipt snapshot effect observation receipt := by
  exact closed

theorem settlement_coherent_is_terminal
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt) :
    EffectPhase.IsTerminal policyTerminalFailure receipt.phase := by
  cases phase : receipt.phase <;>
    simp [SettlementCoherent, phase, EffectPhase.IsTerminal] at coherent ⊢
  exact coherent.1

theorem settlement_coherent_failed_named_policy_terminal
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (failure : FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt)
    (phase : receipt.phase = .failedNamed failure) :
    policyTerminalFailure failure := by
  simp [SettlementCoherent, phase] at coherent
  exact coherent.1

theorem settlement_coherent_recorded_not_compensated
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt)
    (phase : receipt.phase = .recorded) :
    observation.compensationApplied = false := by
  simp [SettlementCoherent, phase] at coherent
  exact coherent.2.2

theorem settlement_coherent_not_applied_unrecorded
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt) :
    ¬ EffectAppliedUnrecorded observation := by
  intro split
  cases phase : receipt.phase <;>
    simp [SettlementCoherent, phase] at coherent
  all_goals
    simp [EffectAppliedUnrecorded] at split
    simp_all

theorem settlement_coherent_not_recorded_without_apply
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt) :
    ¬ EffectRecordedNotApplied observation receipt := by
  intro split
  simp [EffectRecordedNotApplied] at split
  rcases split with ⟨recorded, _, worldAbsent⟩
  simp [SettlementCoherent, recorded] at coherent
  simp_all

theorem settlement_coherent_not_compensation_pending
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    {policyTerminalFailure : FailureName → Prop}
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (coherent :
      SettlementCoherent policyTerminalFailure observation receipt) :
    ¬ CompensationStillPending receipt := by
  intro pending
  simp [CompensationStillPending] at pending
  simp [SettlementCoherent, pending] at coherent

/--
Closure excludes both effect/history split directions and a pending
compensation for every external effect.
-/
theorem epoch_effect_closed_excludes_unsettled_phases
    {Epoch : Type u} {Head : Type v}
    {EffectSlot : Type w} {Generation : Type x}
    {Occurrence : Type y} {FailureName : Type z}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (closed : EpochEffectClosed snapshot) :
    ∀ effect, effect ∈ snapshot.externalEffects →
      ∃ observation receipt,
        snapshot.observe effect.occurrence = some observation ∧
        observation.receipt = some receipt ∧
        ¬ EffectAppliedUnrecorded observation ∧
        ¬ EffectRecordedNotApplied observation receipt ∧
        ¬ CompensationStillPending receipt := by
  intro effect member
  obtain ⟨observation, receipt, settled⟩ := closed effect member
  exact
    ⟨observation, receipt,
      settled.observed, settled.receiptPresent,
      settlement_coherent_not_applied_unrecorded
        observation receipt settled.coherent,
      settlement_coherent_not_recorded_without_apply
        observation receipt settled.coherent,
      settlement_coherent_not_compensation_pending
        observation receipt settled.coherent⟩

end Residua.RCC.EffectSettlement

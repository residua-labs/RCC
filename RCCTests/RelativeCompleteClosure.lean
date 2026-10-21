import RCC.RelativeCompleteClosure

/-!
# RCC RC-1 proof-carrying capstone tests

Theorems below pin the strong packet and branch adapters.  Caller labels,
arbitrary jumps, hidden higher-priority branches, string-only migrations,
active workflow, pending migration, unsettled effects, detached Goal/replay
claims, and underdeclared primitive occurrences cannot manufacture closure.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RelativeCompleteClosure.Tests

open Residua.RCC
open Residua.RCC.FacetCoherence
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectSettlement
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.IntentSnapshotBinding
open Residua.RCC.MetaFailureExhaustion
open Residua.RCC.PrimitiveInvocationCoverage
open Residua.RCC.ProofCarryingOutcome

universe u

inductive Phase
  | initial
  | closed
  deriving DecidableEq, Repr

abbrev phaseWakeSystem : WakeSystem where
  State := Phase
  Goal := Unit
  Observation := Unit
  Source := Unit
  InvalidationRule := Unit
  Evidence := Unit
  History := Unit
  GoalView := Unit
  Receipt := Unit
  ReceiptLog := Unit
  Deadline := Unit
  Recheck := Unit
  currentGoal := fun _ => none
  goalOpen := fun _ _ => False
  goalObstructed := fun _ _ => False
  sameEpochAdvance := fun state next =>
    state = .initial ∧ next = .closed
  observed := fun _ _ => False
  sourceOf := fun _ => ()
  goalDependsOn := fun _ _ _ => False
  ruleApplies := fun _ _ _ => False
  admitObservation := fun state _ => state
  goalEvidence := fun _ _ => none
  measure
    | .initial => 1
    | .closed => 0
  history := fun _ => ()
  goalView := fun _ _ => ()
  receiptLog := fun _ => ()
  expired := fun _ _ => False

/-! ## Proof-carrying execution mutants -/

/-- A strong closed packet is a fixed point of the proof-carrying normalizer. -/
theorem closed_packet_is_core_fixed
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (state : Phase)
    (packet : GlobalEpochClosedPacket C state) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state :=
  (core_fixed_iff_packet execution state).2 ⟨packet⟩

/-- An Advance packet exposes the exact formal reduction, not a target label. -/
theorem admitted_advance_is_formal_reduction
    {C : ClosureContext Phase}
    {before after : Phase}
    (packet : RC1AdvancePacket C before after) :
    (C.adapter.index.world before).reduces
      (C.formalStateAt before before)
      (C.formalStateAt before after) :=
  packet.reduces

/-- A non-reduction cannot be packaged as an RC-1 internal advance. -/
theorem arbitrary_jump_mutant_refused
    {C : ClosureContext Phase}
    {before after : Phase}
    (notReduction :
      ¬ (C.adapter.index.world before).reduces
          (C.formalStateAt before before)
          (C.formalStateAt before after)) :
    ¬ Nonempty (RC1AdvancePacket C before after) := by
  rintro ⟨packet⟩
  exact notReduction packet.reduces

/-- Reepoch payloads always expose an RCC-23 certificate. -/
theorem migration_string_cannot_replace_certificate
    {C : ClosureContext Phase}
    {state : Phase}
    (migration : RC1MigrationPacket C state) :
    Nonempty
      (ReepochCert C.reepochSystem
        (C.snapshotAt state).coordinates.epoch migration.successor) :=
  ⟨migration.certificate⟩

/-- Exact readers prevent an Await result from hiding a legal advance. -/
theorem omitted_advance_reader_mutant_refused
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (state : Phase)
    (wake : RC1WakePacket phaseWakeSystem state)
    (selected : deriveOpen K.toBranchSystem state = .await wake) :
    ¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state) :=
  rc1_await_excludes_hidden_advance execution state wake selected

/-- Exact readers make Halt the true typed remainder. -/
theorem omitted_continuation_reader_mutant_refused
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (state : Phase)
    (fatal : RC1FatalCause C state)
    (selected : deriveOpen K.toBranchSystem state = .halt fatal) :
    (¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state)) ∧
      (¬ Nonempty (K.toBranchSystem.WakePacket state)) ∧
      ¬ Nonempty (K.toBranchSystem.MigrationPacket state) :=
  rc1_halt_excludes_hidden_continuation
    execution state fatal selected

/--
The failure-Halt branch cannot consume detached facts: its refusal is found in
the exact current failure window and is in that window's sealed scope.
-/
theorem detached_failure_facts_cannot_halt
    {C : ClosureContext Phase}
    {state : Phase}
    (refusal : CurrentFailureRefusalAt C state) :
    (C.failureSemantics.coverage.modelAt
        (C.failureTerminalSystem.contextAt
          (C.closureStateAt state))).inScope refusal.failure ∧
      C.failureSemantics.AdmittedAt
        (C.failureTerminalSystem.contextAt
          (C.closureStateAt state)) refusal.failure ∧
      (C.failureWindowAt state).factsAt refusal.failure =
        some refusal.facts ∧
      deriveFailureClass refusal.facts = .refuse refusal.residue :=
  ⟨refusal.inScope, refusal.admitted, refusal.found, refusal.refused⟩

/-- A current-window failure refusal is a constructive anti-closure witness. -/
theorem refused_current_failure_window_cannot_close
    {C : ClosureContext Phase}
    {state : Phase}
    (refusal : CurrentFailureRefusalAt C state) :
    ¬ GlobalEpochClosed C state :=
  refusal.excludesClosed

/-! ## Strong closed-packet mutants -/

/-- A packet cannot hide a live nonterminal goal. -/
theorem active_goal_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    {goal : C.closureSystem.Goal}
    (active :
      goal ∈
        deriveActiveGoals C.closureSystem (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state :=
  active_goal_excludes_closed active

/-- A packet cannot hide a pending reepoch migration. -/
theorem pending_migration_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    {migration : C.closureSystem.Migration}
    (pending :
      migration ∈
        derivePendingMigrations C.closureSystem
          (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state :=
  pending_migration_excludes_closed pending

/-- Support and replay are bound to the exact selected mandatory Goal. -/
theorem detached_goal_replay_support_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state)
    (goal :
      (C.intentRegistry.profile
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state))).Goal)
    (mandatory :
      goal ∈
        (C.intentRegistry.profile
          (currentIntentSpec C.intentRegistry
            (C.snapshotAt state))).mandatoryGoals) :
    ((C.intentRegistry.profile
      (currentIntentSpec C.intentRegistry
        (C.snapshotAt state))).contract goal).claim
      (C.intentObservation.observe
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state)) goal (C.carrierAt state).value) :=
  packet_support_replay_closes_mandatory_goal packet goal mandatory

/-- Replay executes the same accepted certificate as the Goal verifier. -/
theorem detached_replay_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state)
    (goal :
      (C.intentRegistry.profile
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state))).Goal)
    (mandatory :
      goal ∈
        (C.intentRegistry.profile
          (currentIntentSpec C.intentRegistry
            (C.snapshotAt state))).mandatoryGoals) :
    (C.replaySystemAt state).verifyReplay
        ((C.intentGoalMapAt state).judgmentFor goal)
        ((C.replaySystemAt state).receiptFor
          ((C.intentGoalMapAt state).judgmentFor goal)) = true :=
  packet_mandatory_replay_accepted packet goal mandatory

/-- Every in-scope primitive occurrence has an exact refinement packet. -/
theorem underdeclared_primitive_universe_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state)
    (invocation : C.PrimitiveInvocation)
    (inScope : C.primitiveInScopeAt state invocation) :
    ∃ refinement :
        ActualInvocationRefinementAt
          (C.primitiveSystem.familyAt state),
      refinement.invocation =
          C.primitiveSystem.actualAt state invocation ∧
        InvocationReturned refinement.invocation ∧
        (C.primitiveSystem.worldAt state).runtimeStep
            (C.primitiveSystem.runtimeBeforeAt state invocation)
            (C.primitiveSystem.runtimeAfterAt state invocation) ∧
        Nonempty
          (FormalOrMeasuredAt C.primitiveSystem state invocation) :=
  packet_actual_primitive_refines_family packet invocation inScope

/-- Every in-scope effect has a fenced settled receipt. -/
theorem unsettled_effect_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state)
    (effect :
      ExternalEffect C.Occurrence C.HistoryHead C.EffectSlot)
    (inScope : C.EffectInScopeAt state effect) :
    ∃ observation receipt,
      (C.effectSnapshotAt state).observe effect.occurrence =
          some observation ∧
        observation.receipt = some receipt ∧
        ¬ EffectAppliedUnrecorded observation ∧
        ¬ EffectRecordedNotApplied observation receipt ∧
        ¬ CompensationStillPending receipt :=
  packet_excludes_unsettled_effects packet effect inScope

/-- Finality and settlement consume exactly one effect snapshot. -/
theorem effect_snapshot_split_mutant_refused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state) :
    packet.finalizedSourceHead.environment.effectSnapshot =
      C.effectSnapshotAt state :=
  packet_effect_snapshot_exact packet

/-- Closed and fatal derivation cannot inspect different failure windows. -/
theorem closed_packet_uses_current_failure_window
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state) :
    packet.closureExhaustion.failureWindow.admitted =
      C.failureWindowAt state :=
  packet.failureWindowExact

end Residua.RCC.RelativeCompleteClosure.Tests

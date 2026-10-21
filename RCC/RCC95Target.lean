import RCCTests.RelativeCompleteClosure

/-! RCC-95 candidate: relative-complete-closure capstone and CoreObject bridge.

The load-bearing theorems already live in `RelativeCompleteClosure.Tests`.
This Target only packages them. Do not pin `RC1AdvancePacket.{0}`: the packet
is `Type u` indexed by `ClosureContext` (itself `Type u`), and forcing `u = 0`
is the universe-inference failure that made the module unbuildable.
-/

universe u

namespace Residua.RCC.RCC95Target

open Residua.RCC.RelativeCompleteClosure.Tests
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC
open Residua.RCC.FacetCoherence
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectSettlement
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.IntentSnapshotBinding
open Residua.RCC.MetaFailureExhaustion
open Residua.RCC.PrimitiveInvocationCoverage
open Residua.RCC.ProofCarryingOutcome

theorem closedPacketIsCoreFixed
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (state : Phase)
    (packet : GlobalEpochClosedPacket C state) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state :=
  closed_packet_is_core_fixed execution state packet

theorem admittedAdvanceIsFormalReduction
    {C : ClosureContext Phase}
    {before after : Phase}
    (packet : RC1AdvancePacket C before after) :
    (C.adapter.index.world before).reduces
      (C.formalStateAt before before)
      (C.formalStateAt before after) :=
  admitted_advance_is_formal_reduction packet

theorem arbitraryJumpRefused
    {C : ClosureContext Phase}
    {before after : Phase}
    (notReduction :
      ¬ (C.adapter.index.world before).reduces
          (C.formalStateAt before before)
          (C.formalStateAt before after)) :
    ¬ Nonempty (RC1AdvancePacket C before after) :=
  arbitrary_jump_mutant_refused notReduction

theorem migrationStringRefused
    {C : ClosureContext Phase}
    {state : Phase}
    (migration : RC1MigrationPacket C state) :
    Nonempty
      (ReepochCert C.reepochSystem
        (C.snapshotAt state).coordinates.epoch migration.successor) :=
  ⟨migration.certificate⟩
theorem omittedAdvanceReaderRefused
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (state : Phase)
    (wake : RC1WakePacket phaseWakeSystem state)
    (selected : deriveOpen K.toBranchSystem state = .await wake) :
    ¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state) :=
  omitted_advance_reader_mutant_refused execution state wake selected

theorem omittedContinuationReaderRefused
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
  omitted_continuation_reader_mutant_refused
    execution state fatal selected

theorem detachedFailureFactsRefused
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
  detached_failure_facts_cannot_halt refusal

theorem refusedFailureWindowCannotClose
    {C : ClosureContext Phase}
    {state : Phase}
    (refusal : CurrentFailureRefusalAt C state) :
    ¬ GlobalEpochClosed C state :=
  refused_current_failure_window_cannot_close refusal

theorem activeGoalRefused
    {C : ClosureContext Phase}
    {state : Phase}
    {goal : C.closureSystem.Goal}
    (active :
      goal ∈
        deriveActiveGoals C.closureSystem (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state :=
  active_goal_mutant_refused active

theorem pendingMigrationRefused
    {C : ClosureContext Phase}
    {state : Phase}
    {migration : C.closureSystem.Migration}
    (pending :
      migration ∈
        derivePendingMigrations C.closureSystem
          (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state :=
  pending_migration_mutant_refused pending

theorem detachedGoalReplayRefused
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
  detached_goal_replay_support_mutant_refused packet goal mandatory

theorem detachedReplayRefused
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
  detached_replay_mutant_refused packet goal mandatory

theorem underdeclaredPrimitiveRefused
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
  underdeclared_primitive_universe_mutant_refused packet invocation inScope

theorem unsettledEffectRefused
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
  unsettled_effect_mutant_refused packet effect inScope

theorem effectSnapshotSplitRefused
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state) :
    packet.finalizedSourceHead.environment.effectSnapshot =
      C.effectSnapshotAt state :=
  effect_snapshot_split_mutant_refused packet

theorem currentFailureWindowBound
    {C : ClosureContext Phase}
    {state : Phase}
    (packet : GlobalEpochClosedPacket C state) :
    packet.closureExhaustion.failureWindow.admitted =
      C.failureWindowAt state :=
  closed_packet_uses_current_failure_window packet

/-- Pack the capstone theorems as values. Do not restate their binders as
`abbrev _ : Prop := ∀ {C : ClosureContext Phase}, …` — that form cannot
generalize the residual universes on `ClosureContext` / `RC1BranchKernel`.
Defaults bind the Tests theorems (not the field names) so the RHS cannot
shadow. -/
structure Certificate where
  closedPacketIsCoreFixed := @closed_packet_is_core_fixed
  admittedAdvanceIsFormalReduction := @admitted_advance_is_formal_reduction
  arbitraryJumpRefused := @arbitrary_jump_mutant_refused
  migrationStringRefused := @migration_string_cannot_replace_certificate
  omittedAdvanceReaderRefused := @omitted_advance_reader_mutant_refused
  omittedContinuationReaderRefused := @omitted_continuation_reader_mutant_refused
  detachedFailureFactsRefused := @detached_failure_facts_cannot_halt
  refusedFailureWindowCannotClose := @refused_current_failure_window_cannot_close
  activeGoalRefused := @active_goal_mutant_refused
  pendingMigrationRefused := @pending_migration_mutant_refused
  detachedGoalReplayRefused := @detached_goal_replay_support_mutant_refused
  detachedReplayRefused := @detached_replay_mutant_refused
  underdeclaredPrimitiveRefused := @underdeclared_primitive_universe_mutant_refused
  unsettledEffectRefused := @unsettled_effect_mutant_refused
  effectSnapshotSplitRefused := @effect_snapshot_split_mutant_refused
  currentFailureWindowBound := @closed_packet_uses_current_failure_window

def certificate : Certificate where
  closedPacketIsCoreFixed := @closed_packet_is_core_fixed
  admittedAdvanceIsFormalReduction := @admitted_advance_is_formal_reduction
  arbitraryJumpRefused := @arbitrary_jump_mutant_refused
  migrationStringRefused := @migration_string_cannot_replace_certificate
  omittedAdvanceReaderRefused := @omitted_advance_reader_mutant_refused
  omittedContinuationReaderRefused := @omitted_continuation_reader_mutant_refused
  detachedFailureFactsRefused := @detached_failure_facts_cannot_halt
  refusedFailureWindowCannotClose := @refused_current_failure_window_cannot_close
  activeGoalRefused := @active_goal_mutant_refused
  pendingMigrationRefused := @pending_migration_mutant_refused
  detachedGoalReplayRefused := @detached_goal_replay_support_mutant_refused
  detachedReplayRefused := @detached_replay_mutant_refused
  underdeclaredPrimitiveRefused := @underdeclared_primitive_universe_mutant_refused
  unsettledEffectRefused := @unsettled_effect_mutant_refused
  effectSnapshotSplitRefused := @effect_snapshot_split_mutant_refused
  currentFailureWindowBound := @closed_packet_uses_current_failure_window

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC95Target


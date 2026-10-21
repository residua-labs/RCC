import RCCTests.RC1TraceClosure

/-! RCC-72 candidate: semantic terminal trace and closure bridge. -/

namespace Residua.RCC.RCC72Target

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingOutcome.Tests
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.RC1TraceClosure.Tests
open Residua.RCC.RC1TraceClosure
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectSettlement
open Residua.RCC.IntentSnapshotBinding

theorem closedResultExposesTraceAndIntent
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (packet : GlobalEpochClosedPacket C finish)
    (normalized :
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet) :
    Nonempty (AdmittedTrace K.toBranchSystem start finish) ∧
      DerivedIntentSatisfied
        C.intentRegistry C.intentObservation
        (C.snapshotAt finish) (C.carrierAt finish) :=
  rc1_closed_result_exposes_trace_and_intent packet normalized

theorem closedTraceCommutes
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (start finish : Phase)
    (packet : GlobalEpochClosedPacket C finish)
    (closedFound : K.closedAt finish = some packet) :
    ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet ↔
      Nonempty (AdmittedTrace K.toBranchSystem start finish) :=
  rc1_closed_trace_commutes start finish packet closedFound

theorem coreTransitionCommutes
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (start finish : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty (AdmittedTrace K.toBranchSystem start finish) ∧
        GlobalEpochClosed C finish) :=
  rc1_core_transition_commutes execution start finish

theorem coreFixedCommutesWithGlobalClosed
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    {state : Phase} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      GlobalEpochClosed C state :=
  Residua.RCC.RC1TraceClosure.Tests.rc1_core_fixed_iff_global_closed execution

theorem closedResultExposesSettlementAndQuiescence
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (packet : GlobalEpochClosedPacket C finish)
    (normalized :
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet) :
    EpochEffectClosed (C.effectSnapshotAt finish) ∧
      deriveActiveGoals C.closureSystem (C.closureStateAt finish) = [] ∧
      derivePendingMigrations C.closureSystem
          (C.closureStateAt finish) = [] :=
  rc1_closed_result_exposes_settlement_and_quiescence packet normalized

theorem weakUnitTerminalRefused
    {C : ClosureContext Unit}
    (notClosed : ¬ GlobalEpochClosed C ()) :
    ProofCarryingOutcome.normalize unitPacketSystem () = .closed () () ∧
      ¬ Nonempty (TerminalPacketAdapter C (fun _ : Unit => Unit)) :=
  weak_unit_terminal_cannot_realize_rc1 notClosed

structure Certificate where
  closedResultExposesTraceAndIntent :
    ∀ {C : ClosureContext Phase} {K : RC1BranchKernel phaseWakeSystem C}
      {start finish : Phase} (packet : GlobalEpochClosedPacket C finish),
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet →
      Nonempty (AdmittedTrace K.toBranchSystem start finish) ∧
        DerivedIntentSatisfied C.intentRegistry C.intentObservation
          (C.snapshotAt finish) (C.carrierAt finish)
  closedTraceCommutes :
    ∀ {C : ClosureContext Phase} {K : RC1BranchKernel phaseWakeSystem C}
      (start finish : Phase) (packet : GlobalEpochClosedPacket C finish)
      (closedFound : K.closedAt finish = some packet),
      ProofCarryingOutcome.normalize K.toBranchSystem start =
          .closed finish packet ↔
        Nonempty (AdmittedTrace K.toBranchSystem start finish)
  coreTransitionCommutes :
    ∀ {C : ClosureContext Phase} {K : RC1BranchKernel phaseWakeSystem C}
      (execution : RC1Execution K) (start finish : Phase),
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
        (Nonempty (AdmittedTrace K.toBranchSystem start finish) ∧
          GlobalEpochClosed C finish)
  coreFixedCommutesWithGlobalClosed :
    ∀ {C : ClosureContext Phase} {K : RC1BranchKernel phaseWakeSystem C}
      (execution : RC1Execution K) {state : Phase},
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
        GlobalEpochClosed C state
  closedResultExposesSettlementAndQuiescence :
    ∀ {C : ClosureContext Phase} {K : RC1BranchKernel phaseWakeSystem C}
      {start finish : Phase} (packet : GlobalEpochClosedPacket C finish),
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet →
      EpochEffectClosed (C.effectSnapshotAt finish) ∧
        deriveActiveGoals C.closureSystem (C.closureStateAt finish) = [] ∧
        derivePendingMigrations C.closureSystem (C.closureStateAt finish) = []
  weakUnitTerminalRefused :
    ∀ {C : ClosureContext Unit}, ¬ GlobalEpochClosed C () →
      ProofCarryingOutcome.normalize unitPacketSystem () = .closed () () ∧
        ¬ Nonempty (TerminalPacketAdapter C (fun _ : Unit => Unit))

def certificate : Certificate where
  closedResultExposesTraceAndIntent := by
    intro C K start finish packet normalized
    exact closedResultExposesTraceAndIntent packet normalized
  closedTraceCommutes := by
    intro C K start finish packet closedFound
    exact closedTraceCommutes start finish packet closedFound
  coreTransitionCommutes := by
    intro C K execution start finish
    exact coreTransitionCommutes execution start finish
  coreFixedCommutesWithGlobalClosed := by
    intro C K execution state
    exact coreFixedCommutesWithGlobalClosed execution
  closedResultExposesSettlementAndQuiescence := by
    intro C K start finish packet normalized
    exact closedResultExposesSettlementAndQuiescence packet normalized
  weakUnitTerminalRefused := by
    intro C notClosed
    exact weakUnitTerminalRefused notClosed

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC72Target

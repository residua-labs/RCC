import RCC.RC1TraceClosure
import RCCTests.RelativeCompleteClosure
import RCCTests.ProofCarryingOutcome

/-! Adversarial witnesses for the RC-1 semantic terminal / trace bridge. -/

namespace Residua.RCC.RC1TraceClosure.Tests

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingOutcome.Tests
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests
open Residua.RCC.RC1TraceClosure
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectSettlement
open Residua.RCC.IntentSnapshotBinding

/-- A real RC-1 closed result yields both its selected trace and intent semantics. -/
theorem rc1_closed_result_exposes_trace_and_intent
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (packet : GlobalEpochClosedPacket C finish)
    (normalized :
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet) :
    Nonempty
        (Residua.RCC.ProofCarryingTrace.AdmittedTrace
          K.toBranchSystem start finish) ∧
      DerivedIntentSatisfied
        C.intentRegistry C.intentObservation
        (C.snapshotAt finish) (C.carrierAt finish) := by
  let witness :=
    rc1_normalize_closed_has_semantic_trace
      K start finish packet normalized
  exact ⟨witness.trace, witness.intentSatisfied⟩

/-- The arbitrary-endpoint bridge commutes in both directions once the strong reader is pinned. -/
theorem rc1_closed_trace_commutes
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (start finish : Phase)
    (packet : GlobalEpochClosedPacket C finish)
    (closedFound : K.closedAt finish = some packet) :
    ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet ↔
      Nonempty
        (Residua.RCC.ProofCarryingTrace.AdmittedTrace
          K.toBranchSystem start finish) :=
  rc1_closed_iff_finite_selected_trace
    K start finish packet closedFound

/-- The CoreObject transition also commutes with semantic RC-1 closure. -/
theorem rc1_core_transition_commutes
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (start finish : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty
          (Residua.RCC.ProofCarryingTrace.AdmittedTrace
            K.toBranchSystem start finish) ∧
        GlobalEpochClosed C finish) := by
  exact rc1_core_transition_iff_trace_and_closed execution

/-- The demo fixed-point carrier is exactly its strong global closure packet. -/
theorem rc1_core_fixed_iff_global_closed
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    {state : Phase} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      GlobalEpochClosed C state := by
  exact RC1TraceClosure.rc1_core_fixed_iff_global_closed execution

/-- A real RC-1 terminal also entails settled effects and exact quiescence. -/
theorem rc1_closed_result_exposes_settlement_and_quiescence
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
          (C.closureStateAt finish) = [] := by
  let witness :=
    rc1_normalize_closed_has_semantic_trace
      K start finish packet normalized
  exact
    ⟨witness.effectsSettled,
      witness.quiescent.1,
      witness.quiescent.2.2⟩

/--
Countermodel: the generic `Unit` terminal can close its toy normalizer, but it
cannot realize an RC-1 terminal at a state where strong global closure is
constructively refuted.
-/
theorem weak_unit_terminal_cannot_realize_rc1
    {C : ClosureContext Unit}
    (notClosed : ¬ GlobalEpochClosed C ()) :
    ProofCarryingOutcome.normalize unitPacketSystem () = .closed () () ∧
      ¬ Nonempty (TerminalPacketAdapter C (fun _ : Unit => Unit)) := by
  constructor
  · exact generic_core_still_needs_semantic_packet_adapter
  · rintro ⟨adapter⟩
    exact notClosed ⟨adapter.lift () ()⟩

end Residua.RCC.RC1TraceClosure.Tests

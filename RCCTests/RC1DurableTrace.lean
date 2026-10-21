import RCC.RC1DurableTrace
import RCCTests.RC1StepMSTBinding
import RCC.RC1StepVerdictAdapter
import RCCTests.RelativeCompleteClosure

/-! Positive and adversarial witnesses for the M1-E durable-trace lift. -/

namespace Residua.RCC.RC1DurableTrace.Tests

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RC1StepMSTBinding.Tests
open Residua.RCC.RC1DurableTrace
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests

/-- The demo M1-A realization constructively covers every selected edge. -/
def demoCoverage
    {C : ClosureContext Phase}
    (K : RC1BranchKernel phaseWakeSystem C) :
    SelectedAdvanceRealizationCoverage K (demoSurface C) where
  cover := fun edge => ⟨demoBinding edge.advance.certificate⟩

/-- Every finite selected RC-1 trace lifts edge-for-edge to durable history. -/
theorem demo_selected_trace_realizes_durably
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (trace : AdmittedTrace K.toBranchSystem start finish) :
    Nonempty (DurableTrace K (demoSurface C) start finish) :=
  ⟨DurableTrace.realize (demoCoverage K) trace⟩

/-- The realized trace has a history edge for every selected transition. -/
theorem demo_durable_trace_projects_to_history
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (trace : DurableTrace K (demoSurface C) start finish) :
    Nonempty
        (HistoryTrace (W := phaseWakeSystem) (C := C)
          (demoSurface C) start finish) :=
  ⟨DurableTrace.toHistoryTrace trace⟩

/-- A closed RC-1 result can be consumed by a typed-verdict client without
re-running or weakening the canonical normalization proof. -/
theorem normalized_closed_result_lifts_to_typed_trace
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {surface : StepSurface C}
    {adapter : RC1StepVerdictAdapter.Adapter C surface}
    {start finish : Phase}
    (coverage : SelectedAdvanceRealizationCoverage K surface)
    (packet : GlobalEpochClosedPacket C finish)
    (normalized :
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet) :
    ∃ (trace : DurableTrace K surface start finish)
      (verdicts : List surface.SettledEvent),
      DurableTrace.AcceptedVerdictTrace
        (W := phaseWakeSystem) (C := C) (K := K) (surface := surface)
        adapter trace verdicts :=
  DurableTrace.normalize_closed_has_durable_accepted_trace
    coverage packet normalized

/-- CoreObject closure commutes with the concrete demo durable realization. -/
theorem demo_core_transition_commutes_with_durable_trace
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (start finish : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty (DurableTrace K (demoSurface C) start finish) ∧
        GlobalEpochClosed C finish) := by
  exact
    rc1_core_transition_iff_durable_trace_and_closed
      execution (demoSurface C) (demoCoverage K)

/-- The same commuting bridge retains a typed accepted-verdict witness list. -/
theorem demo_core_transition_commutes_with_accepted_verdict_trace
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    {adapter : RC1StepVerdictAdapter.Adapter C (demoSurface C)}
    {start finish : Phase} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      ∃ (trace : DurableTrace K (demoSurface C) start finish)
        (verdicts : List (demoSurface C).SettledEvent),
        Nonempty
            (DurableTrace.AcceptedVerdictTrace
              (W := phaseWakeSystem) (C := C) (K := K)
              (surface := demoSurface C)
              adapter trace verdicts) ∧
          GlobalEpochClosed C finish := by
  exact
    rc1_core_transition_iff_durable_accepted_trace_and_closed
      execution (demoSurface C) (demoCoverage K)

/-- Fixed-point form of the durable accepted-verdict bridge. -/
theorem demo_core_fixed_iff_durable_accepted_verdict_trace
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    {adapter : RC1StepVerdictAdapter.Adapter C (demoSurface C)}
    {state : Phase} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      ∃ (trace : DurableTrace K (demoSurface C) state state)
        (verdicts : List (demoSurface C).SettledEvent),
        Nonempty
            (DurableTrace.AcceptedVerdictTrace
              (W := phaseWakeSystem) (C := C) (K := K)
              (surface := demoSurface C) adapter trace verdicts) ∧
          GlobalEpochClosed C state := by
  exact
    rc1_core_fixed_iff_durable_accepted_trace_and_closed
      execution (demoSurface C) (demoCoverage K)

/-- Empty settled events make coverage impossible for any actual selected edge. -/
theorem empty_event_mutant_cannot_cover_trace_edge
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {before after : Phase}
    (edge : SelectedAdvance K.toBranchSystem before after) :
    ¬ SelectedAdvanceRealizationCoverage K (emptyEventSurface C) := by
  exact
    empty_settled_event_cannot_cover_selected_edge
      (surface := emptyEventSurface C)
      (by
        intro event
        change EmptySettledEvent at event
        cases event)
      edge

end Residua.RCC.RC1DurableTrace.Tests

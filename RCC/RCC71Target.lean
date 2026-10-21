import RCCTests.RC1DurableTrace

/-! RCC-71 candidate: durable M1-E traces and CoreObject bridge. -/

namespace Residua.RCC.RCC71Target

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.RC1DurableTrace
open Residua.RCC.RC1DurableTrace.Tests
open Residua.RCC.RC1StepMSTBinding.Tests
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests

theorem selectedTraceRealizesDurably
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (trace : AdmittedTrace K.toBranchSystem start finish) :
    Nonempty (DurableTrace K (demoSurface C) start finish) :=
  demo_selected_trace_realizes_durably trace

theorem durableTraceProjectsToHistory
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {start finish : Phase}
    (trace : DurableTrace K (demoSurface C) start finish) :
    Nonempty
        (HistoryTrace (W := phaseWakeSystem) (C := C)
          (demoSurface C) start finish) :=
  demo_durable_trace_projects_to_history trace

theorem closedResultLiftsToAcceptedTrace
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
  normalized_closed_result_lifts_to_typed_trace
    coverage packet normalized

theorem coreTransitionCommutesWithDurableTrace
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (start finish : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty (DurableTrace K (demoSurface C) start finish) ∧
        GlobalEpochClosed C finish) :=
  demo_core_transition_commutes_with_durable_trace execution start finish

theorem coreFixedCommutesWithAcceptedTrace
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
              (surface := demoSurface C)
              adapter trace verdicts) ∧
          GlobalEpochClosed C state :=
  demo_core_fixed_iff_durable_accepted_verdict_trace execution

theorem emptyEventCoverageRefused
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    {before after : Phase}
    (edge : SelectedAdvance K.toBranchSystem before after) :
    ¬ SelectedAdvanceRealizationCoverage K (emptyEventSurface C) :=
  empty_event_mutant_cannot_cover_trace_edge edge

structure Certificate where
  selectedTraceRealizesDurably :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      {start finish : Phase},
      AdmittedTrace K.toBranchSystem start finish →
        Nonempty (DurableTrace K (demoSurface C) start finish)
  durableTraceProjectsToHistory :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      {start finish : Phase},
      DurableTrace K (demoSurface C) start finish →
        Nonempty (HistoryTrace (W := phaseWakeSystem) (C := C)
          (demoSurface C) start finish)
  closedResultLiftsToAcceptedTrace :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      {surface : StepSurface C}
      {adapter : RC1StepVerdictAdapter.Adapter C surface}
      {start finish : Phase},
      SelectedAdvanceRealizationCoverage K surface →
      (packet : GlobalEpochClosedPacket C finish) →
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet →
      ∃ (trace : DurableTrace K surface start finish)
        (verdicts : List surface.SettledEvent),
        DurableTrace.AcceptedVerdictTrace
          (W := phaseWakeSystem) (C := C) (K := K) (surface := surface)
          adapter trace verdicts
  coreTransitionCommutesWithDurableTrace :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      (execution : RC1Execution K) (start finish : Phase),
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
        (Nonempty (DurableTrace K (demoSurface C) start finish) ∧
          GlobalEpochClosed C finish)
  coreFixedCommutesWithAcceptedTrace :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      (execution : RC1Execution K)
      {adapter : RC1StepVerdictAdapter.Adapter C (demoSurface C)}
      {state : Phase},
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
        ∃ (trace : DurableTrace K (demoSurface C) state state)
          (verdicts : List (demoSurface C).SettledEvent),
          Nonempty
              (DurableTrace.AcceptedVerdictTrace
                (W := phaseWakeSystem) (C := C) (K := K)
                (surface := demoSurface C)
                adapter trace verdicts) ∧
            GlobalEpochClosed C state
  emptyEventCoverageRefused :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      {before after : Phase},
      SelectedAdvance K.toBranchSystem before after →
        ¬ SelectedAdvanceRealizationCoverage K (emptyEventSurface C)

def certificate : Certificate where
  selectedTraceRealizesDurably := by
    intro C K start finish trace
    exact selectedTraceRealizesDurably trace
  durableTraceProjectsToHistory := by
    intro C K start finish trace
    exact durableTraceProjectsToHistory trace
  closedResultLiftsToAcceptedTrace := by
    intro C K surface adapter start finish coverage packet normalized
    exact closedResultLiftsToAcceptedTrace coverage packet normalized
  coreTransitionCommutesWithDurableTrace := by
    intro C K execution start finish
    exact coreTransitionCommutesWithDurableTrace execution start finish
  coreFixedCommutesWithAcceptedTrace := by
    intro C K execution adapter state
    exact coreFixedCommutesWithAcceptedTrace execution
  emptyEventCoverageRefused := by
    intro C K before after edge
    exact emptyEventCoverageRefused edge

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC71Target

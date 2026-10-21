import RCCTests.ProofCarryingTrace

/-! RCC-87 candidate: finite proof-carrying trace provenance. -/

namespace Residua.RCC.RCC87Target

open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.ProofCarryingTrace.Tests
open Residua.RCC.ProofCarryingOutcome.Tests

@[reducible] def closedEmptyTrace := closed_state_has_empty_trace
def emptyTraceAccepted := empty_trace_closed_state_is_accepted
@[reducible] def oneStepTraceExists := one_step_closed_result_decomposes
def coreTransitionExposesTrace := generic_core_transition_exposes_trace_and_closed
def coreFixedIffClosed := generic_core_fixed_iff_closed_packet
def omittedAdvanceHalts := nonclosed_no_advance_normalizes_to_named_halt
def omittedAdvanceNoTrace := nonclosed_no_advance_has_no_admitted_trace

structure Certificate where
  closedEmptyTrace :
    Nonempty (AdmittedTrace demoSystem DemoState.done DemoState.done)
  emptyTraceAccepted :
    ProofCarryingOutcome.normalize demoSystem DemoState.done =
      .closed DemoState.done DemoClosed.done
  oneStepTraceExists :
    Nonempty (AdmittedTrace demoSystem DemoState.pending DemoState.done)
  coreTransitionExposesTrace :
    (ProofCarryingOutcome.coreObject demoSystem).D
        DemoState.pending DemoState.done ↔
      (Nonempty (AdmittedTrace demoSystem DemoState.pending DemoState.done) ∧
        Nonempty (demoSystem.ClosedPacket DemoState.done))
  coreFixedIffClosed :
    (ProofCarryingOutcome.coreObject demoSystem).D
        DemoState.done DemoState.done ↔
      Nonempty (demoSystem.ClosedPacket DemoState.done)
  omittedAdvanceHalts :
    ProofCarryingOutcome.normalize omittedAdvanceSystem DemoState.pending =
      .halt DemoState.pending .namedOpenFailure
  omittedAdvanceNoTrace :
    ¬ Nonempty
        (AdmittedTrace omittedAdvanceSystem DemoState.pending DemoState.done)

def certificate : Certificate where
  closedEmptyTrace := closed_state_has_empty_trace
  emptyTraceAccepted := empty_trace_closed_state_is_accepted
  oneStepTraceExists := one_step_closed_result_decomposes
  coreTransitionExposesTrace := generic_core_transition_exposes_trace_and_closed
  coreFixedIffClosed := generic_core_fixed_iff_closed_packet
  omittedAdvanceHalts := nonclosed_no_advance_normalizes_to_named_halt
  omittedAdvanceNoTrace := nonclosed_no_advance_has_no_admitted_trace

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
-- Bound to the CERTIFICATE PROJECTIONS, not the sibling defs of the same name.
theorem certificate_omitted_advance_halts (c : Certificate) :
    ProofCarryingOutcome.normalize omittedAdvanceSystem DemoState.pending =
      .halt DemoState.pending .namedOpenFailure :=
  c.omittedAdvanceHalts

theorem certificate_omitted_advance_no_trace (c : Certificate) :
    ¬ Nonempty
        (AdmittedTrace omittedAdvanceSystem DemoState.pending DemoState.done) :=
  c.omittedAdvanceNoTrace

end Residua.RCC.RCC87Target

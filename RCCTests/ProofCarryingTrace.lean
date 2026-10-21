import RCC.ProofCarryingTrace
import RCCTests.ProofCarryingOutcome

/-!
# Adversarial witnesses for finite proof-carrying traces

The positive witnesses cover both zero-step closure and the existing one-step
demo normalization.  The mutant removes the only selected advance: although
the transition packet type still has an inhabitant, no admitted trace can use
it and the open state cannot masquerade as a closed result.
-/

namespace Residua.RCC.ProofCarryingTrace.Tests

open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingOutcome.Tests
open Residua.RCC.ProofCarryingTrace

/-- An already closed state has the canonical empty admitted trace. -/
theorem closed_state_has_empty_trace :
    Nonempty (AdmittedTrace demoSystem DemoState.done DemoState.done) :=
  ⟨AdmittedTrace.nil (K := demoSystem) DemoState.done⟩

/-- The empty trace plus the exact closed-reader packet is accepted unchanged. -/
theorem empty_trace_closed_state_is_accepted :
    ProofCarryingOutcome.normalize demoSystem DemoState.done =
      .closed DemoState.done DemoClosed.done := by
  exact
    normalize_of_trace_and_closed_selection
      demoSystem (AdmittedTrace.nil (K := demoSystem) DemoState.done)
        DemoClosed.done rfl

/-- The existing one-step normalization has a finite selected admitted trace. -/
theorem one_step_closed_result_decomposes :
    Nonempty (AdmittedTrace demoSystem DemoState.pending DemoState.done) :=
  normalize_closed_has_trace
    demoSystem DemoState.pending DemoState.done .done one_admitted_step_closes

/-- The generic CoreObject bridge exposes both the selected trace and packet. -/
theorem generic_core_transition_exposes_trace_and_closed :
    (ProofCarryingOutcome.coreObject demoSystem).D
        DemoState.pending DemoState.done ↔
      (Nonempty (AdmittedTrace demoSystem DemoState.pending DemoState.done) ∧
        Nonempty (demoSystem.ClosedPacket DemoState.done)) := by
  exact
    core_transition_iff_trace_and_closed
      demoSystem demoReadersComplete

/-- Generic fixed points are exactly states with a closed packet. -/
theorem generic_core_fixed_iff_closed_packet :
    (ProofCarryingOutcome.coreObject demoSystem).D
        DemoState.done DemoState.done ↔
      Nonempty (demoSystem.ClosedPacket DemoState.done) := by
  exact core_fixed_iff_closed demoSystem demoReadersComplete

/-- Removing `advanceAt` makes the open state halt rather than silently close. -/
theorem nonclosed_no_advance_normalizes_to_named_halt :
    ProofCarryingOutcome.normalize omittedAdvanceSystem DemoState.pending =
      .halt DemoState.pending .namedOpenFailure := by
  simp [ProofCarryingOutcome.normalize, deriveOpen, omittedAdvanceSystem, demoSystem]

/--
Countermodel: the packet type alone cannot forge a trace when the canonical
reader selected no advance.
-/
theorem nonclosed_no_advance_has_no_admitted_trace :
    ¬ Nonempty
        (AdmittedTrace omittedAdvanceSystem DemoState.pending DemoState.done) := by
  rintro ⟨trace⟩
  cases trace.nil_or_first with
  | inl same =>
      cases same
  | inr first =>
      obtain ⟨next, ⟨edge⟩⟩ := first
      have selected := edge.selected
      simp [deriveOpen, omittedAdvanceSystem, demoSystem] at selected

end Residua.RCC.ProofCarryingTrace.Tests

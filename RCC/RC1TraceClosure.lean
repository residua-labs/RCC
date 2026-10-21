import RCC.ProofCarryingTrace
import RCC.RelativeCompleteClosure

/-!
# RC-1 semantic terminal / finite-trace bridge

M1-C decomposes a generic proof-carrying normalization into selected certified
advances.  This module closes the terminal side for RC-1: the final packet is
not a caller label or `Unit`, but the existing `GlobalEpochClosedPacket` whose
headline entails intent satisfaction, effect settlement, and lifecycle
quiescence.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RC1TraceClosure

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectSettlement
open Residua.RCC.IntentSnapshotBinding

universe u v

/--
An explicit adapter obligation for any generic terminal-packet family that
claims to realize RC-1 closure.  Merely inhabiting the generic packet is not
enough; it must construct the strong global packet at the same state.
-/
structure TerminalPacketAdapter
    {State : Type u}
    (C : ClosureContext State)
    (ClosedPacket : State → Type v) where
  lift : ∀ state, ClosedPacket state → GlobalEpochClosedPacket C state

/-- RC-1's branch kernel already uses the strong packet, so its adapter is exact. -/
def rc1TerminalPacketAdapter
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C) :
    TerminalPacketAdapter C K.toBranchSystem.ClosedPacket where
  lift := fun _ packet => packet

/--
The complete semantic witness behind one RC-1 closed normalization.

The trace is generic M1-C evidence for selected certified branch advances; it
is not, by itself, a durable history/event trace.  `terminal` is the existing
strong RC-1 packet.  Its semantic consequences are derived below through the
existing packet headline theorems rather than by repeating the normalize
equality.
-/
structure RC1ClosedTraceWitness
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C)
    (start finish : W.State) where
  terminal : GlobalEpochClosedPacket C finish
  trace : Nonempty (AdmittedTrace K.toBranchSystem start finish)

/-- Every RC-1 closed result has a finite admitted trace and strong semantic terminal. -/
def rc1_normalize_closed_has_semantic_trace
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C)
    (start finish : W.State)
    (packet : GlobalEpochClosedPacket C finish)
    (normalized :
      ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet) :
    RC1ClosedTraceWitness K start finish where
  terminal := packet
  trace :=
    normalize_closed_has_trace
      K.toBranchSystem start finish packet normalized

/-- The terminal of an RC-1 closed trace entails the current intent contract. -/
theorem RC1ClosedTraceWitness.intentSatisfied
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    {start finish : W.State}
    (witness : RC1ClosedTraceWitness K start finish) :
    DerivedIntentSatisfied
      C.intentRegistry C.intentObservation
      (C.snapshotAt finish) (C.carrierAt finish) := by
  exact packet_intent_satisfied witness.terminal

/-- The same terminal entails settled effects, not merely a closed branch tag. -/
theorem RC1ClosedTraceWitness.effectsSettled
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    {start finish : W.State}
    (witness : RC1ClosedTraceWitness K start finish) :
    EpochEffectClosed (C.effectSnapshotAt finish) := by
  exact packet_effects_settled witness.terminal

/-- The same terminal entails the three exact quiescence projections. -/
theorem RC1ClosedTraceWitness.quiescent
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    {start finish : W.State}
    (witness : RC1ClosedTraceWitness K start finish) :
    deriveActiveGoals C.closureSystem (C.closureStateAt finish) = [] ∧
      deriveActiveFailures C.failureTerminalSystem
          (C.closureStateAt finish)
          witness.terminal.closureExhaustion.failureWindow = [] ∧
      derivePendingMigrations C.closureSystem
          (C.closureStateAt finish) = [] := by
  exact packet_meta_quiescent witness.terminal

/-- A finite RC-1 selected trace ending at the exact strong-reader packet is accepted. -/
theorem rc1_trace_to_closed_is_accepted
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C)
    {start finish : W.State}
    (trace : AdmittedTrace K.toBranchSystem start finish)
    (packet : GlobalEpochClosedPacket C finish)
    (closedFound : K.closedAt finish = some packet) :
    ProofCarryingOutcome.normalize K.toBranchSystem start =
      .closed finish packet :=
  normalize_of_trace_and_closed_selection
    K.toBranchSystem trace packet closedFound

/--
For arbitrary endpoints, once the strong terminal reader is pinned, RC-1
closed normalization is equivalent to existence of the finite selected trace.
-/
theorem rc1_closed_iff_finite_selected_trace
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C)
    (start finish : W.State)
    (packet : GlobalEpochClosedPacket C finish)
    (closedFound : K.closedAt finish = some packet) :
    ProofCarryingOutcome.normalize K.toBranchSystem start =
        .closed finish packet ↔
      Nonempty (AdmittedTrace K.toBranchSystem start finish) := by
  constructor
  · exact normalize_closed_has_trace K.toBranchSystem start finish packet
  · rintro ⟨trace⟩
    exact rc1_trace_to_closed_is_accepted K trace packet closedFound

/-!
The stronger commuting statement exposes the generic CoreObject transition
without putting the normalizer equation or a `closedAt` lookup on the right
hand side.  The reverse direction genuinely uses the complete closed reader
to recover the executable terminal packet from semantic RC-1 closure.
-/
theorem rc1_core_transition_iff_trace_and_closed
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    {start finish : W.State} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty (AdmittedTrace K.toBranchSystem start finish) ∧
        GlobalEpochClosed C finish) := by
  constructor
  · intro transition
    change (ProofCarryingOutcome.normalize K.toBranchSystem start).closedState? =
      some finish at transition
    cases normalized : ProofCarryingOutcome.normalize K.toBranchSystem start with
    | closed target packet =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized] at transition
        cases transition
        have trace :=
          normalize_closed_has_trace
            K.toBranchSystem start finish packet normalized
        exact ⟨trace, ⟨packet⟩⟩
    | await target wake =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized] at transition
    | reepoch target migration =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized] at transition
    | halt target failure =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized] at transition
  · rintro ⟨trace, closed⟩
    obtain ⟨packet, found⟩ := execution.readers.closed.complete finish closed
    obtain ⟨trace⟩ := trace
    have normalized :=
      normalize_of_trace_and_closed_selection
        K.toBranchSystem trace packet found
    change (ProofCarryingOutcome.normalize K.toBranchSystem start).closedState? =
      some finish
    rw [normalized]
    rfl

/-- The concrete RC-1 fixed points are exactly the strong global closures. -/
theorem rc1_core_fixed_iff_global_closed
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    {state : W.State} :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      GlobalEpochClosed C state := by
  constructor
  · intro fixed
    exact (rc1_core_transition_iff_trace_and_closed execution).mp fixed |>.2
  · intro closed
    exact (rc1_core_transition_iff_trace_and_closed execution).mpr
      ⟨⟨AdmittedTrace.nil (K := K.toBranchSystem) state⟩, closed⟩

end Residua.RCC.RC1TraceClosure

import RCC.ProofCarryingOutcome

/-!
# Finite canonical traces for proof-carrying normalization

`ProofCarryingOutcome.normalize` hides its certified internal advances behind
the final four-way outcome.  This module exposes the exact finite trace behind
a closed result.  Every edge is selected by the common branch derivation,
carries the indexed `CertifiedAdvance`, and therefore carries its strict
measure decrease.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.ProofCarryingTrace

open Residua.RCC.ProofCarryingOutcome

universe u a c w m h

/-- One internal advance exactly as selected by `normalize`. -/
structure SelectedAdvance
    (K : BranchSystem.{u, a, c, w, m, h})
    (before after : K.State) : Type (max u a) where
  openAt : K.closedAt before = none
  advance : CertifiedAdvance K.State K.measure K.AdvancePacket before
  targetExact : advance.next = after
  selected :
    deriveOpen K before =
      .advanced advance.next advance.certificate advance.decreases

/-- The strict decrease carried by every selected trace edge. -/
theorem SelectedAdvance.decreases
    {K : BranchSystem.{u, a, c, w, m, h}}
    {before after : K.State}
    (edge : SelectedAdvance K before after) :
    K.measure after < K.measure before := by
  rw [← edge.targetExact]
  exact edge.advance.decreases

/-- A type-safe finite path of selected proof-carrying advances. -/
inductive AdmittedTrace
    (K : BranchSystem.{u, a, c, w, m, h}) :
    K.State → K.State → Type (max u a) where
  | nil (state : K.State) : AdmittedTrace K state state
  | cons
      {before next finish : K.State}
      (edge : SelectedAdvance K before next)
      (tail : AdmittedTrace K next finish) :
      AdmittedTrace K before finish

namespace AdmittedTrace

/-- The number of admitted internal transitions in a finite trace. -/
def length
    {K : BranchSystem.{u, a, c, w, m, h}}
    {start finish : K.State} :
    AdmittedTrace K start finish → Nat
  | .nil _ => 0
  | .cons _ tail => tail.length + 1

/-- A finite trace is empty or exposes its first selected advance. -/
theorem nil_or_first
    {K : BranchSystem.{u, a, c, w, m, h}}
    {start finish : K.State}
    (trace : AdmittedTrace K start finish) :
    start = finish ∨
      ∃ next, Nonempty (SelectedAdvance K start next) := by
  cases trace with
  | nil state => exact Or.inl rfl
  | cons edge tail => exact Or.inr ⟨_, ⟨edge⟩⟩

end AdmittedTrace

/-- A closed normalization result decomposes into its finite selected trace. -/
theorem normalize_closed_has_trace
    (K : BranchSystem.{u, a, c, w, m, h})
    (start finish : K.State)
    (packet : K.ClosedPacket finish)
    (normalized : ProofCarryingOutcome.normalize K start = .closed finish packet) :
    Nonempty (AdmittedTrace K start finish) := by
  generalize measureExact : K.measure start = measureValue
  induction measureValue using Nat.strongRecOn generalizing start finish packet with
  | ind measureValue ih =>
      cases closedFound : K.closedAt start with
      | some closed =>
          have same : (.closed start closed : NormalizeOutcome K) = .closed finish packet := by
            rw [ProofCarryingOutcome.normalize] at normalized
            rw [closedFound] at normalized
            exact normalized
          cases same
          exact ⟨AdmittedTrace.nil start⟩
      | none =>
          cases selected : deriveOpen K start with
          | advanced next certificate decreases =>
              have tailNormalized :
                  ProofCarryingOutcome.normalize K next = .closed finish packet := by
                rw [ProofCarryingOutcome.normalize] at normalized
                rw [closedFound, selected] at normalized
                exact normalized
              have nextMeasure : K.measure next < measureValue := by
                simpa [← measureExact] using decreases
              have recursive := ih (K.measure next) nextMeasure
              obtain ⟨tail⟩ := recursive next finish packet tailNormalized rfl
              let advance :
                  CertifiedAdvance K.State K.measure K.AdvancePacket start :=
                { next := next
                  certificate := certificate
                  decreases := decreases }
              have edge : SelectedAdvance K start next :=
                { openAt := closedFound
                  advance := advance
                  targetExact := rfl
                  selected := selected }
              exact ⟨AdmittedTrace.cons edge tail⟩
          | await wake =>
              simp [ProofCarryingOutcome.normalize, closedFound, selected] at normalized
          | reepoch migration =>
              simp [ProofCarryingOutcome.normalize, closedFound, selected] at normalized
          | halt failure =>
              simp [ProofCarryingOutcome.normalize, closedFound, selected] at normalized

/--
Conversely, an exact selected trace whose terminal packet is returned by the
closed reader is exactly the trace accepted by `normalize`.
-/
theorem normalize_of_trace_and_closed_selection
    (K : BranchSystem.{u, a, c, w, m, h})
    {start finish : K.State}
    (trace : AdmittedTrace K start finish)
    (packet : K.ClosedPacket finish)
    (closedFound : K.closedAt finish = some packet) :
    ProofCarryingOutcome.normalize K start = .closed finish packet := by
  induction trace with
  | nil state =>
      rw [ProofCarryingOutcome.normalize]
      rw [closedFound]
  | cons edge tail ih =>
      rw [ProofCarryingOutcome.normalize]
      simp only [edge.openAt, edge.selected]
      rw [edge.targetExact]
      exact ih packet closedFound

/-- A complete closed reader turns any finite selected trace to a closed state into acceptance. -/
theorem trace_to_closed_is_accepted
    (K : BranchSystem.{u, a, c, w, m, h})
    (reader : ClosedReaderComplete K)
    {start finish : K.State}
    (trace : AdmittedTrace K start finish)
    (closed : Nonempty (K.ClosedPacket finish)) :
    ∃ packet,
      ProofCarryingOutcome.normalize K start = .closed finish packet := by
  obtain ⟨packet, found⟩ := reader.complete finish closed
  exact ⟨packet, normalize_of_trace_and_closed_selection K trace packet found⟩

/-!
The generic CoreObject transition is exactly the existence of the finite
selected trace together with a packet that the closed reader can expose at
the endpoint.  The right hand side deliberately mentions neither the
normalizer equation nor a caller-provided branch tag; the reverse direction
uses only the reader-completeness certificate and the trace theorem above.
-/
theorem core_transition_iff_trace_and_closed
    (K : BranchSystem)
    (readers : BranchReadersComplete K)
    {start finish : K.State} :
    (ProofCarryingOutcome.coreObject K).D start finish ↔
      (Nonempty (AdmittedTrace K start finish) ∧
        Nonempty (K.ClosedPacket finish)) := by
  constructor
  · intro transition
    change (ProofCarryingOutcome.normalize K start).closedState? =
      some finish at transition
    cases normalized : ProofCarryingOutcome.normalize K start with
    | closed target packet =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized]
          at transition
        cases transition
        have trace :=
          normalize_closed_has_trace K start finish packet normalized
        exact ⟨trace, ⟨packet⟩⟩
    | await target wake =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized]
          at transition
    | reepoch target migration =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized]
          at transition
    | halt target failure =>
        simp [ProofCarryingOutcome.NormalizeOutcome.closedState?, normalized]
          at transition
  · rintro ⟨trace, closed⟩
    obtain ⟨trace⟩ := trace
    obtain ⟨packet, normalized⟩ :=
      trace_to_closed_is_accepted K readers.closed trace closed
    change (ProofCarryingOutcome.normalize K start).closedState? =
      some finish
    rw [normalized]
    rfl

theorem core_fixed_iff_closed
    (K : BranchSystem)
    (readers : BranchReadersComplete K)
    {state : K.State} :
    (ProofCarryingOutcome.coreObject K).D state state ↔
      Nonempty (K.ClosedPacket state) := by
  constructor
  · intro fixed
    exact (core_transition_iff_trace_and_closed K readers).mp fixed |>.2
  · intro closed
    exact (core_transition_iff_trace_and_closed K readers).mpr
      ⟨⟨AdmittedTrace.nil (K := K) state⟩, closed⟩

end Residua.RCC.ProofCarryingTrace

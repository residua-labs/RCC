import RCC.RelativeCompleteClosure

/-!
# RC-1 Step-MST / history binding

`RC1AdvancePacket` proves that one same-epoch transition is both a formal
reduction and admitted by the FC-2 world.  It does not by itself prove that the
transition has a settled representative which can be appended to durable
history.  This module adds that missing, deliberately small M1-A bridge.

The instance supplies the step-class and settled-event realization.  A bound
advance must then expose the active/admitted class, `sigma = some event`, the
exact pre-head, settlement, and the append edge.  `HistoryEdge` is derived only
from such a bound `RC1AdvancePacket`; a residue or empty representative type
cannot mutate history.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RC1StepMSTBinding

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure

universe u

/-- Pin RC-1's proof-only packet universe to the carrier universe for this executable bridge. -/
abbrev AdvancePacket
    {State : Type u}
    (C : ClosureContext State)
    (before after : State) : Type u :=
  RC1AdvancePacket.{u, u} C before after

/--
The realization surface for one RC-1 step class.

`admitted` is only the Step-MST admissibility bit.  The stronger institutional
admission proof remains in `RC1AdvancePacket`; `sigma` must additionally expose
the settled durable representative used by `append`.
-/
structure StepSurface
    {State : Type u}
    (C : ClosureContext State) where
  StepClass : Type u
  SettledEvent : Type u
  classOf :
    {before after : State} →
      AdvancePacket C before after → StepClass
  active : StepClass → Bool
  admitted : StepClass → Bool
  sigma : StepClass → Option SettledEvent
  preHead : SettledEvent → C.HistoryHead
  settled : SettledEvent → Prop
  append : State → SettledEvent → State → Prop

/--
One RC-1 advance resolved all the way to a durable history representative.

The class is derived from the existing proof-carrying advance; callers cannot
substitute a detached class or event after admission.
-/
structure BoundAdvance
    {State : Type u}
    {C : ClosureContext State}
    (surface : StepSurface C)
    {before after : State}
    (packet : AdvancePacket C before after) : Type u where
  event : surface.SettledEvent
  activeClass : surface.active (surface.classOf packet) = true
  admittedClass : surface.admitted (surface.classOf packet) = true
  representative : surface.sigma (surface.classOf packet) = some event
  preHeadBound :
    surface.preHead event =
      (C.snapshotAt before).coordinates.historyHead
  eventSettled : surface.settled event
  appended : surface.append before event after

/--
A durable history edge exists only when an RC-1 advance has a settled
representative and an append witness.
-/
def HistoryEdge
    {State : Type u}
    {C : ClosureContext State}
    (surface : StepSurface C)
    (before after : State) : Prop :=
  ∃ packet : AdvancePacket C before after,
    Nonempty (BoundAdvance surface packet)

/-- A non-admitted Step-MST class cannot acquire a durable representative. -/
theorem nonadmitted_cannot_bind_history
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    {before after : State}
    {packet : AdvancePacket C before after}
    (notAdmitted : surface.admitted (surface.classOf packet) = false) :
    ¬ Nonempty (BoundAdvance surface packet) := by
  rintro ⟨binding⟩
  have contradiction := binding.admittedClass
  rw [notAdmitted] at contradiction
  cases contradiction

/-- Every fully bound RC-1 advance derives one durable history edge. -/
theorem BoundAdvance.historyEdge
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    {before after : State}
    {packet : AdvancePacket C before after}
    (binding : BoundAdvance surface packet) :
    HistoryEdge surface before after :=
  ⟨packet, ⟨binding⟩⟩

/--
Every derived history edge exposes the Step-MST representative provenance,
the pre-head binding, settlement, and append relation.
-/
theorem historyEdge_has_settled_sigma_provenance
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    {before after : State}
    (edge : HistoryEdge surface before after) :
    ∃ (packet : AdvancePacket C before after)
        (event : surface.SettledEvent),
      surface.active (surface.classOf packet) = true ∧
      surface.admitted (surface.classOf packet) = true ∧
      surface.sigma (surface.classOf packet) = some event ∧
      surface.preHead event =
        (C.snapshotAt before).coordinates.historyHead ∧
      surface.settled event ∧
      surface.append before event after := by
  rcases edge with ⟨packet, ⟨binding⟩⟩
  exact
    ⟨packet, binding.event,
      binding.activeClass,
      binding.admittedClass,
      binding.representative,
      binding.preHeadBound,
      binding.eventSettled,
      binding.appended⟩

/--
Load-bearing empty-event countermodel: an existing admitted/reducing RC-1
advance cannot be resolved when the realization has no settled-event carrier.
-/
theorem empty_settled_event_cannot_bind_advance
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (empty : surface.SettledEvent → False)
    {before after : State}
    (packet : AdvancePacket C before after) :
    ¬ Nonempty (BoundAdvance surface packet) := by
  rintro ⟨binding⟩
  exact empty binding.event

/-- Consequently an empty settled-event carrier cannot derive a history edge. -/
theorem empty_settled_event_has_no_history_edge
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (empty : surface.SettledEvent → False)
    {before after : State} :
    ¬ HistoryEdge surface before after := by
  rintro ⟨packet, binding⟩
  exact empty_settled_event_cannot_bind_advance empty packet binding

end Residua.RCC.RC1StepMSTBinding

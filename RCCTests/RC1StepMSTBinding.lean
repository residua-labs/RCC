import RCC.RC1StepMSTBinding

/-!
# RC-1 Step-MST / history binding witnesses

The positive surface retains the exact before/after states and snapshot head
in its canonical event.  The mutant has no settled-event inhabitant at all;
even an already existing `RC1AdvancePacket` therefore cannot become a history
edge.
-/

namespace Residua.RCC.RC1StepMSTBinding.Tests

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RC1StepMSTBinding

/-- Minimal semantic class used by the non-vacuous generic witness. -/
structure DemoStepClass (State : Type) where
  before : State
  after : State

/-- The settled event retains both transition endpoints and the exact pre-head. -/
structure DemoSettledEvent
    {State : Type}
    (C : ClosureContext State) where
  before : State
  after : State
  head : C.HistoryHead

/--
A canonical one-event realization for an existing RC-1 advance.  This fixture
does not strengthen the packet's admission theorem; it only demonstrates that
all M1-A provenance coordinates can be bound without caller status labels.
-/
def demoSurface
    {State : Type}
    (C : ClosureContext State) : StepSurface C where
  StepClass := DemoStepClass State
  SettledEvent := DemoSettledEvent C
  classOf := fun {before after} _ => ⟨before, after⟩
  active := fun _ => true
  admitted := fun _ => true
  sigma := fun stepClass =>
    some
      { before := stepClass.before
        after := stepClass.after
        head :=
          (C.snapshotAt stepClass.before).coordinates.historyHead }
  preHead := fun event => event.head
  settled := fun _ => True
  append := fun before event after =>
    event.before = before ∧ event.after = after

/-- Every existing RC-1 packet has a concrete settled representative here. -/
def demoBinding
    {State : Type}
    {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    BoundAdvance (demoSurface C) packet where
  event :=
    { before := before
      after := after
      head := (C.snapshotAt before).coordinates.historyHead }
  activeClass := rfl
  admittedClass := rfl
  representative := rfl
  preHeadBound := rfl
  eventSettled := trivial
  appended := ⟨rfl, rfl⟩

/-- Positive M1-A witness: an RC-1 packet resolves to a durable history edge. -/
theorem existing_advance_resolves_to_history_edge
    {State : Type}
    {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    HistoryEdge (demoSurface C) before after :=
  (demoBinding packet).historyEdge

/-- The derived edge exposes every requested Step-MST/history coordinate. -/
theorem existing_advance_retains_settled_sigma_provenance
    {State : Type}
    {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    ∃ (source : AdvancePacket C before after)
        (event : (demoSurface C).SettledEvent),
      (demoSurface C).active ((demoSurface C).classOf source) = true ∧
      (demoSurface C).admitted ((demoSurface C).classOf source) = true ∧
      (demoSurface C).sigma ((demoSurface C).classOf source) = some event ∧
      (demoSurface C).preHead event =
        (C.snapshotAt before).coordinates.historyHead ∧
      (demoSurface C).settled event ∧
      (demoSurface C).append before event after :=
  historyEdge_has_settled_sigma_provenance
    (existing_advance_resolves_to_history_edge packet)

/-! ## Non-admission cannot mutate durable history -/

theorem nonadmitted_advance_cannot_resolve_to_history
    {State : Type}
    {C : ClosureContext State}
    {surface : StepSurface C}
    {before after : State}
    {packet : AdvancePacket C before after}
    (notAdmitted : surface.admitted (surface.classOf packet) = false) :
    ¬ Nonempty (BoundAdvance surface packet) :=
  nonadmitted_cannot_bind_history notAdmitted

/-- Universe-polymorphic empty carrier used by the negative realization. -/
inductive EmptySettledEvent : Type

/-- A mutant realization which has no possible settled representative. -/
def emptyEventSurface
    {State : Type}
    (C : ClosureContext State) : StepSurface C where
  StepClass := DemoStepClass State
  SettledEvent := EmptySettledEvent
  classOf := fun {before after} _ => ⟨before, after⟩
  active := fun _ => true
  admitted := fun _ => true
  sigma := fun _ => none
  preHead := fun event => nomatch event
  settled := fun event => nomatch event
  append := fun _ event _ => nomatch event

/--
Load-bearing mutant: removing the settled-event carrier makes an existing
admitted/reducing RC-1 advance impossible to bind.
-/
theorem empty_event_mutant_cannot_resolve_existing_advance
    {State : Type}
    {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    ¬ Nonempty (BoundAdvance (emptyEventSurface C) packet) :=
  empty_settled_event_cannot_bind_advance
    (by
      intro event
      change EmptySettledEvent at event
      cases event)
    packet

/-- The same mutant cannot manufacture a durable append edge. -/
theorem empty_event_mutant_cannot_append_history
    {State : Type}
    {C : ClosureContext State}
    {before after : State} :
    ¬ HistoryEdge (emptyEventSurface C) before after :=
  empty_settled_event_has_no_history_edge
    (by
      intro event
      change EmptySettledEvent at event
      cases event)

end Residua.RCC.RC1StepMSTBinding.Tests

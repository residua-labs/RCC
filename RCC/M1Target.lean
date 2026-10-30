import RCCTests.RC1DurableTrace

/-!
# M1 candidate: Step ExecModel, slot coherence, admitted traces, CoreObject.Exact

M1's obligation is that the Step ExecModel and slot coherence together yield
admitted traces and CoreObject exactness.  This file replaces the historical
aliasing stub with a real certificate containing three genuinely new layers
plus the existing generic wiring:

* a generic `SlotSurface` wrapper adding the NEW head-evolution law `postHead`
  (no prior encoding existed for it), with the per-edge theorem and a
  trace-level chaining theorem by induction over `DurableTrace`;
* a non-vacuous fixture surface whose settled events carry a real Nat slot
  chain (`pre + 1 = post` settlement, discriminating admission, typed
  out-of-epoch residue) — unlike `demoSurface` (settled := True, always
  admitted);
* NEW refusal sites: an incoherent-head mutant surface whose append demands
  `post = pre` while settlement demands `pre + 1 = post` can bind no advance,
  and a broken-slot event cannot be any binding's representative — plus the
  two existing Step-MST refusals re-cited at this surface.

Scope honesty (RCC-40 lesson): the discriminating admission surface is a
fixture-level law over the two-phase `Phase` carrier.  It proves that the
generic slot-coherence layer is non-vacuous; it does not turn a finite fixture
into a production quorum extractor.  The `SlotSurface`, `HeadChain`, edge, and
chaining theorems are fully parametric over any state, context, kernel, and
surface.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.M1Target

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingTrace
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RC1StepMSTBinding.Tests
open Residua.RCC.RC1DurableTrace
open Residua.RCC.RC1DurableTrace.Tests
open Residua.RCC.RC1StepVerdictAdapter
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests
open Residua.RCC.StepExecModel
open Residua.RCC.StepVerdictModel

universe u v w x y z

/-! ## The NEW slot-coherence layer (generic) -/

/--
One step surface plus the head-evolution law it previously lacked: appending a
settled event to `before` producing `after` moves the snapshot head to exactly
the event's `postHead`.  `preHead` (already in `StepSurface`) and `postHead`
are the two teeth of a slot; the edge and chaining theorems below make the
pairing explicit.
-/
structure SlotSurface
    {State : Type u}
    (C : ClosureContext State) where
  surface : StepSurface C
  postHead : surface.SettledEvent → C.HistoryHead
  coherent :
    ∀ {before after : State}
      (event : surface.SettledEvent),
      surface.settled event →
      surface.append before event after →
        postHead event = (C.snapshotAt after).coordinates.historyHead

/-- NEW per-edge head evolution: every bound advance's settled event posts
exactly the snapshot head of the state it produces. -/
theorem slot_coherence_edge
    {State : Type u}
    {C : ClosureContext State}
    (slot : SlotSurface C)
    {before after : State}
    {packet : AdvancePacket C before after}
    (binding : BoundAdvance slot.surface packet) :
    slot.postHead binding.event =
      (C.snapshotAt after).coordinates.historyHead :=
  slot.coherent binding.event binding.eventSettled binding.appended

/--
NEW trace-level chaining witness: a concrete `BoundAdvance` representative for
every edge of a durable trace.  `DurableTrace` itself only carries
`Nonempty (BoundAdvance ...)`, so the head chain selects one witness per edge
and is therefore where consecutive heads are comparable.
-/
inductive HeadChain
    {W : WakeSystem.{u, v, w, x, y, z}}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (slot : SlotSurface C) :
    {start finish : W.State} →
    DurableTrace K slot.surface start finish → Prop where
  | nil (state : W.State) : HeadChain slot (DurableTrace.nil state)
  | cons
      {before next finish : W.State}
      {edge : SelectedAdvance K.toBranchSystem before next}
      {binding : Nonempty (BoundAdvance slot.surface edge.advance.certificate)}
      {tail : DurableTrace K slot.surface next finish}
      (bound : BoundAdvance slot.surface edge.advance.certificate)
      (rest : HeadChain slot tail) :
      HeadChain slot (DurableTrace.cons edge binding tail)

/-- NEW: every durable trace over a coherent slot surface carries a head chain. -/
theorem durable_trace_has_head_chain
    {W : WakeSystem.{u, v, w, x, y, z}}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    {slot : SlotSurface C}
    {start finish : W.State}
    (trace : DurableTrace K slot.surface start finish) :
    HeadChain slot trace := by
  induction trace with
  | nil state => exact HeadChain.nil state
  | @cons before next finish edge binding tail ih =>
      obtain ⟨bound⟩ := binding
      exact HeadChain.cons bound ih

/-- NEW chaining theorem: on consecutive edges of one trace, the first edge's
posted head is exactly the second edge's bound pre-head. -/
theorem consecutive_bound_events_link_heads
    {W : WakeSystem.{u, v, w, x, y, z}}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    {slot : SlotSurface C}
    {before next middle finish : W.State}
    {edge₁ : SelectedAdvance K.toBranchSystem before next}
    {binding₁ : Nonempty (BoundAdvance slot.surface edge₁.advance.certificate)}
    {edge₂ : SelectedAdvance K.toBranchSystem next middle}
    {binding₂ : Nonempty (BoundAdvance slot.surface edge₂.advance.certificate)}
    {tail : DurableTrace K slot.surface middle finish}
    (chain :
      HeadChain slot
        (DurableTrace.cons edge₁ binding₁
          (DurableTrace.cons edge₂ binding₂ tail))) :
    ∃ (bound₁ : BoundAdvance slot.surface edge₁.advance.certificate)
      (bound₂ : BoundAdvance slot.surface edge₂.advance.certificate),
      slot.postHead bound₁.event = slot.surface.preHead bound₂.event := by
  cases chain with
  | cons bound₁ rest₁ =>
    cases rest₁ with
    | cons bound₂ _ =>
      have headEvolution := slot_coherence_edge slot bound₁
      have headShift :
          (C.snapshotAt edge₁.advance.next).coordinates.historyHead =
            (C.snapshotAt next).coordinates.historyHead :=
        congrArg
          (fun state => (C.snapshotAt state).coordinates.historyHead)
          edge₁.targetExact
      exact
        ⟨bound₁, bound₂,
          headEvolution.trans (headShift.trans bound₂.preHeadBound.symm)⟩

/-! ## A non-vacuous fixture surface with real head state -/

/-- The step class retains both transition endpoints (Phase fixture). -/
structure SlotStepClass where
  before : Phase
  after : Phase

/--
REAL head state: the settled event carries its own pre/post slot numbers and
both transition endpoints.  Settlement below demands a strict one-slot step,
so unlike `DemoSettledEvent` the carrier is not inert.
-/
structure SlotSettledEvent
    (C : ClosureContext Phase) where
  before : Phase
  after : Phase
  pre : Nat
  post : Nat

/-- Discriminating admission: only the initial→closed epoch step admits. -/
def slotAdmitted : SlotStepClass → Bool
  | { before := .initial, after := .closed } => true
  | _ => false

/-- Typed non-admission residue: the refusal names the refused class. -/
inductive SlotResidue where
  | outOfEpoch : SlotStepClass → SlotResidue

/-- The canonical settled representative of the one admitted class. -/
def slotSigma
    (C : ClosureContext Phase) :
    SlotStepClass → Option (SlotSettledEvent C)
  | { before := .initial, after := .closed } =>
      some { before := .initial, after := .closed, pre := 0, post := 1 }
  | _ => none

/-- The typed residue reader: non-admitted classes carry their class. -/
def slotRho : SlotStepClass → Option SlotResidue
  | { before := .initial, after := .closed } => none
  | cls => some (.outOfEpoch cls)

/--
The fixture Step-MST surface.  `settled` is a real law (`pre + 1 = post`), the
append relation re-asserts the slot step alongside the endpoint binding, and
`admitted` discriminates.  This is the guardedSurface template with real
settlement content.
-/
def slotSurface
    (C : ClosureContext Phase) : StepSurface C where
  StepClass := SlotStepClass
  SettledEvent := SlotSettledEvent C
  classOf := fun {before after} _ => ⟨before, after⟩
  active := fun _ => true
  admitted := slotAdmitted
  sigma := slotSigma C
  preHead := fun event => (C.snapshotAt event.before).coordinates.historyHead
  settled := fun event => event.pre + 1 = event.post
  append := fun before event after =>
    event.before = before ∧ event.after = after ∧ event.post = event.pre + 1

/--
Every admitted-class packet binds durably: the canonical event settles
(`0 + 1 = 1` by computation), posts the exact snapshot heads, and appends.
-/
def slotBinding
    {C : ClosureContext Phase}
    {before after : Phase}
    (admitted : slotAdmitted ⟨before, after⟩ = true)
    (packet : AdvancePacket C before after) :
    BoundAdvance (slotSurface C) packet where
  event := { before := before, after := after, pre := 0, post := 1 }
  activeClass := rfl
  admittedClass := admitted
  representative := by
    cases before <;> cases after <;>
      simp_all [slotSurface, slotAdmitted, slotSigma]
  preHeadBound := rfl
  eventSettled := rfl
  appended := ⟨rfl, rfl, rfl⟩

/-- Wrapping the fixture surface with its post-head reader satisfies the
generic head-evolution law. -/
def slotCoherentSurface
    (C : ClosureContext Phase) : SlotSurface C where
  surface := slotSurface C
  postHead := fun event => (C.snapshotAt event.after).coordinates.historyHead
  coherent := by
    intro before after event _eventSettled appended
    obtain ⟨-, eventAfter, -⟩ := appended
    show (C.snapshotAt event.after).coordinates.historyHead = (C.snapshotAt after).coordinates.historyHead
    rw [eventAfter]

/-- The fixture surface really satisfies the NEW per-edge law: every bound
advance's event posts exactly the snapshot head of the state it produces. -/
theorem slot_fixture_edge_coherence
    {C : ClosureContext Phase}
    {before after : Phase}
    {packet : AdvancePacket C before after}
    (binding : BoundAdvance (slotSurface C) packet) :
    (slotCoherentSurface C).postHead binding.event =
      (C.snapshotAt after).coordinates.historyHead :=
  slot_coherence_edge (slotCoherentSurface C) binding

/-- The instance obligation that the kernel only selects admitted-class
packets; under it every selected edge has a durable slot representative. -/
def slotCoverage
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (admittedPackets :
      ∀ {before after : Phase}
        (_ : AdvancePacket C before after),
        slotAdmitted ⟨before, after⟩ = true) :
    SelectedAdvanceRealizationCoverage K (slotSurface C) where
  cover edge :=
    ⟨slotBinding (admittedPackets edge.advance.certificate)
      edge.advance.certificate⟩

/-! ## Step ExecModel / typed verdict wiring over the real surface -/

structure SlotRaw where
  before : Phase
  after : Phase

/--
The typed verdict reader: the one admitted class is accepted with its canonical
representative; every other class is rejected with its out-of-epoch residue.
-/
def slotVerdict
    (C : ClosureContext Phase) :
    SlotStepClass → StepVerdictModel.Outcome (SlotSettledEvent C) SlotResidue
  | { before := .initial, after := .closed } =>
      .accepted { before := .initial, after := .closed, pre := 0, post := 1 }
  | cls => .reject (.outOfEpoch cls)

/-- The concrete typed-verdict adapter over the discriminating slot surface. -/
def slotVerdictAdapter
    (C : ClosureContext Phase) :
    RC1StepVerdictAdapter.Adapter C (slotSurface C) where
  Raw := SlotRaw
  Residue := SlotResidue
  q := fun raw => { before := raw.before, after := raw.after }
  evalRaw := fun raw =>
    slotVerdict C { before := raw.before, after := raw.after }
  evalClass := slotVerdict C
  rho := slotRho
  quotient_factorization := by intro raw; rfl
  admitted_iff_accepted := by
    intro cls
    cases cls with
    | mk b a =>
      cases b <;> cases a
      · simp only [slotSurface, slotAdmitted, slotVerdict]
        exact iff_of_false (by simp) (by simp)
      · simp only [slotSurface, slotAdmitted, slotVerdict]
        exact ⟨fun _ => ⟨_, rfl⟩, fun _ => trivial⟩
      · simp only [slotSurface, slotAdmitted, slotVerdict]
        exact iff_of_false (by simp) (by simp)
      · simp only [slotSurface, slotAdmitted, slotVerdict]
        exact iff_of_false (by simp) (by simp)
  representative_iff_accepted := by
    intro cls rep
    cases cls with
    | mk b a =>
      cases b <;> cases a
      · simp only [slotSurface, slotSigma, slotVerdict]
        exact iff_of_false (by simp) (by simp)
      · simp only [slotSurface, slotSigma, slotVerdict]
        constructor
        · intro h
          injection h with hEvent
          rw [hEvent]
        · intro h
          injection h with hEvent
          rw [hEvent]
      · simp only [slotSurface, slotSigma, slotVerdict]
        exact iff_of_false (by simp) (by simp)
      · simp only [slotSurface, slotSigma, slotVerdict]
        exact iff_of_false (by simp) (by simp)
  residue_totality := by
    intro cls _active notAdmitted
    cases cls with
    | mk b a =>
      cases b <;> cases a
      · exact ⟨.outOfEpoch ⟨.initial, .initial⟩, by
          simp [slotSurface, slotRho, slotVerdict]⟩
      · simp [slotSurface, slotAdmitted] at notAdmitted
      · exact ⟨.outOfEpoch ⟨.closed, .initial⟩, by
          simp [slotSurface, slotRho, slotVerdict]⟩
      · exact ⟨.outOfEpoch ⟨.closed, .closed⟩, by
          simp [slotSurface, slotRho, slotVerdict]⟩

theorem slot_verdict_profile
    {C : ClosureContext Phase} :
    StepVerdictModel.Profile
      (RC1StepVerdictAdapter.model (slotVerdictAdapter C)) :=
  RC1StepVerdictAdapter.adapter_has_profile (slotVerdictAdapter C)

/-- The four Step ExecModel laws hold over the real surface via the typed
verdict refinement (no separate abstract-outcome adapter is needed). -/
theorem slot_step_profile
    {C : ClosureContext Phase} :
    StepExecModel.Profile
      (StepVerdictModel.toStepExecModel
        (RC1StepVerdictAdapter.model (slotVerdictAdapter C))) :=
  StepVerdictModel.profile_to_step_exec_profile slot_verdict_profile

/-! ## CoreObject.Exact wiring -/

/-- Wiring: under the admitted-packets obligation, every admitted selected
trace realizes durably through the generic `DurableTrace.realize`. -/
theorem slot_admitted_trace_realizes
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (admittedPackets :
      ∀ {before after : Phase}
        (_ : AdvancePacket C before after),
        slotAdmitted ⟨before, after⟩ = true)
    {start finish : Phase}
    (trace : AdmittedTrace K.toBranchSystem start finish) :
    Nonempty (DurableTrace K (slotSurface C) start finish) :=
  ⟨DurableTrace.realize (slotCoverage admittedPackets) trace⟩

/-- Wiring: CoreObject transitions are exactly durable slot traces plus
global epoch closure, via the existing generic commuting bridge. -/
theorem slot_core_transition_iff
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (admittedPackets :
      ∀ {before after : Phase}
        (_ : AdvancePacket C before after),
        slotAdmitted ⟨before, after⟩ = true)
    (start finish : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
      (Nonempty (DurableTrace K (slotSurface C) start finish) ∧
        GlobalEpochClosed C finish) :=
  rc1_core_transition_iff_durable_trace_and_closed
    execution (slotSurface C) (slotCoverage admittedPackets)

/-- Wiring (fixed-point, typed-verdict form): CoreObject fixed points are
exactly durable accepted-verdict traces over the slot surface plus global
epoch closure. -/
theorem slot_core_fixed_iff
    {C : ClosureContext Phase}
    {K : RC1BranchKernel phaseWakeSystem C}
    (execution : RC1Execution K)
    (admittedPackets :
      ∀ {before after : Phase}
        (_ : AdvancePacket C before after),
        slotAdmitted ⟨before, after⟩ = true)
    (state : Phase) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      ∃ (trace : DurableTrace K (slotSurface C) state state)
        (verdicts : List (SlotSettledEvent C)),
        Nonempty
            (DurableTrace.AcceptedVerdictTrace
              (slotVerdictAdapter C) trace verdicts) ∧
          GlobalEpochClosed C state :=
  rc1_core_fixed_iff_durable_accepted_trace_and_closed
    execution (slotSurface C) (slotCoverage admittedPackets)

/-! ## Refusal sites -/

/--
NEW incoherent-head mutant: this surface keeps the real settlement law
(`pre + 1 = post`) but its append relation demands the head NOT advance
(`post = pre`).  The two laws are jointly unsatisfiable, so no advance — not
even an existing admitted/reducing packet — can bind: the slot step in the
append relation is load-bearing.
-/
def slotMismatchSurface
    (C : ClosureContext Phase) : StepSurface C where
  StepClass := SlotStepClass
  SettledEvent := SlotSettledEvent C
  classOf := fun {before after} _ => ⟨before, after⟩
  active := fun _ => true
  admitted := slotAdmitted
  sigma := slotSigma C
  preHead := fun event => (C.snapshotAt event.before).coordinates.historyHead
  settled := fun event => event.pre + 1 = event.post
  append := fun before event after =>
    event.before = before ∧ event.after = after ∧ event.post = event.pre

theorem incoherent_head_mutant_cannot_bind
    {C : ClosureContext Phase}
    {before after : Phase}
    (packet : AdvancePacket C before after) :
    ¬ Nonempty (BoundAdvance (slotMismatchSurface C) packet) := by
  rintro ⟨binding⟩
  obtain ⟨-, -, postEq⟩ := binding.appended
  exact
    absurd (binding.eventSettled.trans postEq)
      (Nat.succ_ne_self binding.event.pre)

/-- NEW event-level refusal: an event whose slot chain is broken (`post ≠
pre + 1`) cannot be the settled representative of any bound advance on the
real surface. -/
theorem broken_slot_event_cannot_be_bound
    {C : ClosureContext Phase}
    {before after : Phase}
    {packet : AdvancePacket C before after}
    (binding : BoundAdvance (slotSurface C) packet)
    {event : SlotSettledEvent C}
    (broken : event.post ≠ event.pre + 1) :
    binding.event ≠ event := by
  intro same
  subst same
  exact broken binding.eventSettled.symm

/-- Existing refusal re-cited at the slot surface: a non-admitted class cannot
acquire a durable representative. -/
theorem slot_nonadmitted_cannot_bind
    {C : ClosureContext Phase}
    {before after : Phase}
    {packet : AdvancePacket C before after}
    (notAdmitted : slotAdmitted ⟨before, after⟩ = false) :
    ¬ Nonempty (BoundAdvance (slotSurface C) packet) :=
  nonadmitted_cannot_bind_history notAdmitted

/-- Existing refusal re-cited: an empty settled-event carrier cannot bind an
already existing advance. -/
theorem slot_empty_event_cannot_bind
    {C : ClosureContext Phase}
    {before after : Phase}
    (packet : AdvancePacket C before after) :
    ¬ Nonempty (BoundAdvance (emptyEventSurface C) packet) :=
  empty_event_mutant_cannot_resolve_existing_advance packet

/-! ## Non-vacuity pins -/

/-- Admission discriminates: the out-of-epoch class is not admitted. -/
theorem slot_admitted_discriminates :
    slotAdmitted ⟨.closed, .initial⟩ = false :=
  rfl

/-- Settlement has content: a head-skipping event (5 → 7) does not settle. -/
theorem slot_settlement_has_content
    {C : ClosureContext Phase} :
    ¬ (slotSurface C).settled
        { before := .initial, after := .closed, pre := 5, post := 7 } := by
  intro h
  simp [slotSurface] at h

/-- Settlement is satisfiable: the canonical one-slot event settles. -/
theorem slot_settlement_nonempty
    {C : ClosureContext Phase} :
    (slotSurface C).settled
        { before := .initial, after := .closed, pre := 0, post := 1 } :=
  rfl

/-- The out-of-epoch class carries its typed residue. -/
theorem slot_nonadmitted_class_has_typed_residue
    {C : ClosureContext Phase} :
    (slotVerdictAdapter C).rho ⟨.closed, .initial⟩ =
      some (.outOfEpoch ⟨.closed, .initial⟩) :=
  rfl

/-! ## The certificate -/

structure Certificate where
  stepProfile :
    ∀ {C : ClosureContext Phase},
      StepExecModel.Profile
        (StepVerdictModel.toStepExecModel
          (RC1StepVerdictAdapter.model (slotVerdictAdapter C)))
  verdictProfile :
    ∀ {C : ClosureContext Phase},
      StepVerdictModel.Profile
        (RC1StepVerdictAdapter.model (slotVerdictAdapter C))
  slotCoherenceEdge :
    ∀ {State : Type} {C : ClosureContext State}
      (slot : SlotSurface C)
      {before after : State}
      {packet : AdvancePacket C before after}
      (binding : BoundAdvance slot.surface packet),
      slot.postHead binding.event =
        (C.snapshotAt after).coordinates.historyHead
  slotCoherenceTrace :
    ∀ {W : WakeSystem.{0, 0, 0, 0, 0, 0}} {C : ClosureContext W.State}
      {K : RC1BranchKernel W C} {slot : SlotSurface C}
      {start finish : W.State}
      (trace : DurableTrace K slot.surface start finish),
      HeadChain slot trace
  consecutiveHeadsLink :
    ∀ {W : WakeSystem.{0, 0, 0, 0, 0, 0}} {C : ClosureContext W.State}
      {K : RC1BranchKernel W C} {slot : SlotSurface C}
      {before next middle finish : W.State}
      {edge₁ : SelectedAdvance K.toBranchSystem before next}
      {binding₁ : Nonempty (BoundAdvance slot.surface edge₁.advance.certificate)}
      {edge₂ : SelectedAdvance K.toBranchSystem next middle}
      {binding₂ : Nonempty (BoundAdvance slot.surface edge₂.advance.certificate)}
      {tail : DurableTrace K slot.surface middle finish}
      (_chain :
        HeadChain slot
          (DurableTrace.cons edge₁ binding₁
            (DurableTrace.cons edge₂ binding₂ tail))),
      ∃ (bound₁ : BoundAdvance slot.surface edge₁.advance.certificate)
        (bound₂ : BoundAdvance slot.surface edge₂.advance.certificate),
        slot.postHead bound₁.event = slot.surface.preHead bound₂.event
  admittedTraceRealizes :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      (_admittedPackets :
        ∀ {before after : Phase}
          (_ : AdvancePacket C before after),
          slotAdmitted ⟨before, after⟩ = true)
      {start finish : Phase}
      (_trace : AdmittedTrace K.toBranchSystem start finish),
      Nonempty (DurableTrace K (slotSurface C) start finish)
  coreTransitionExact :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      (_execution : RC1Execution K)
      (_admittedPackets :
        ∀ {before after : Phase}
          (_ : AdvancePacket C before after),
          slotAdmitted ⟨before, after⟩ = true)
      (start finish : Phase),
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D start finish ↔
        (Nonempty (DurableTrace K (slotSurface C) start finish) ∧
          GlobalEpochClosed C finish)
  coreFixedExact :
    ∀ {C : ClosureContext Phase}
      {K : RC1BranchKernel phaseWakeSystem C}
      (_execution : RC1Execution K)
      (_admittedPackets :
        ∀ {before after : Phase}
          (_ : AdvancePacket C before after),
          slotAdmitted ⟨before, after⟩ = true)
      (state : Phase),
      (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
        ∃ (trace : DurableTrace K (slotSurface C) state state)
          (verdicts : List (SlotSettledEvent C)),
          Nonempty
              (DurableTrace.AcceptedVerdictTrace
                (slotVerdictAdapter C) trace verdicts) ∧
            GlobalEpochClosed C state
  incoherentHeadRefused :
    ∀ {C : ClosureContext Phase} {before after : Phase}
      (packet : AdvancePacket C before after),
      ¬ Nonempty (BoundAdvance (slotMismatchSurface C) packet)
  incoherentEventRefused :
    ∀ {C : ClosureContext Phase} {before after : Phase}
      {packet : AdvancePacket C before after}
      (binding : BoundAdvance (slotSurface C) packet)
      {event : SlotSettledEvent C}
      (_broken : event.post ≠ event.pre + 1),
      binding.event ≠ event
  nonadmittedCannotBind :
    ∀ {C : ClosureContext Phase} {before after : Phase}
      {packet : AdvancePacket C before after},
      slotAdmitted ⟨before, after⟩ = false →
      ¬ Nonempty (BoundAdvance (slotSurface C) packet)
  emptyEventCannotCover :
    ∀ {C : ClosureContext Phase} {before after : Phase}
      (packet : AdvancePacket C before after),
      ¬ Nonempty (BoundAdvance (emptyEventSurface C) packet)
  admittedDiscriminates : slotAdmitted ⟨.closed, .initial⟩ = false
  settlementHasContent :
    ∀ {C : ClosureContext Phase},
      ¬ (slotSurface C).settled
          { before := .initial, after := .closed, pre := 5, post := 7 }
  settlementNonempty :
    ∀ {C : ClosureContext Phase},
      (slotSurface C).settled
          { before := .initial, after := .closed, pre := 0, post := 1 }
  nonadmittedClassHasTypedResidue :
    ∀ {C : ClosureContext Phase},
      (slotVerdictAdapter C).rho ⟨.closed, .initial⟩ =
        some (.outOfEpoch ⟨.closed, .initial⟩)

def certificate : Certificate where
  stepProfile := by intro C; exact slot_step_profile
  verdictProfile := by intro C; exact slot_verdict_profile
  slotCoherenceEdge := by
    intro State C slot before after packet binding
    exact slot_coherence_edge slot binding
  slotCoherenceTrace := by
    intro W C K slot start finish trace
    exact durable_trace_has_head_chain trace
  consecutiveHeadsLink := by
    intro W C K slot before next middle finish edge₁ binding₁ edge₂ binding₂
      tail chain
    exact consecutive_bound_events_link_heads chain
  admittedTraceRealizes := by
    intro C K admittedPackets start finish trace
    exact slot_admitted_trace_realizes admittedPackets trace
  coreTransitionExact := by
    intro C K execution admittedPackets start finish
    exact slot_core_transition_iff execution admittedPackets start finish
  coreFixedExact := by
    intro C K execution admittedPackets state
    exact slot_core_fixed_iff execution admittedPackets state
  incoherentHeadRefused := by
    intro C before after packet
    exact incoherent_head_mutant_cannot_bind packet
  incoherentEventRefused := by
    intro C before after packet binding event broken
    exact broken_slot_event_cannot_be_bound binding broken
  nonadmittedCannotBind := by
    intro C before after packet notAdmitted
    exact slot_nonadmitted_cannot_bind notAdmitted
  emptyEventCannotCover := by
    intro C before after packet
    exact slot_empty_event_cannot_bind packet
  admittedDiscriminates := slot_admitted_discriminates
  settlementHasContent := by
    intro C; exact slot_settlement_has_content
  settlementNonempty := by
    intro C; exact slot_settlement_nonempty
  nonadmittedClassHasTypedResidue := by
    intro C; exact slot_nonadmitted_class_has_typed_residue

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.M1Target

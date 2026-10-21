import RCC.ProofCarryingOutcome

/-!
# Adversarial witnesses for proof-carrying RCC outcomes

The positive model performs one admitted reduction and closes.  The negative
models show that an arbitrary decreasing jump, a migration without debt
conservation, and a halt without a named failure cannot be represented by the
certificate types used by the execution core.
-/

namespace Residua.RCC.ProofCarryingOutcome.Tests

open Residua.RCC
open Residua.RCC.ProofCarryingOutcome

inductive DemoState
  | pending
  | done
  | rogue
  deriving DecidableEq, Repr

def demoMeasure : DemoState → Nat
  | .pending => 1
  | .done => 0
  | .rogue => 0

inductive DemoClosed : DemoState → Type
  | done : DemoClosed .done

inductive DemoReduction : DemoState → DemoState → Prop
  | finish : DemoReduction .pending .done

inductive DemoAdmission : DemoState → DemoState → Prop
  | finish : DemoAdmission .pending .done

/-- The advance payload binds both formal reduction and pre-state admission. -/
structure DemoAdvance (before after : DemoState) : Type where
  reduces : DemoReduction before after
  admitted : DemoAdmission before after

inductive NoAdvance (_before _after : DemoState) : Type
inductive NoWake (_state : DemoState) : Type
inductive NoMigration (_state : DemoState) : Type

inductive DemoWake (state : DemoState)
  | external : DemoWake state

inductive DemoMigration (state : DemoState) : Type
  | conservative
      (oldDebtSettled : state = .done) :
      DemoMigration state

inductive DemoFailure : DemoState → Type
  | namedOpenFailure : DemoFailure .pending
  | namedDoneFailure : DemoFailure .done
  | namedRogueFailure : DemoFailure .rogue

def demoSystem : BranchSystem where
  State := DemoState
  measure := demoMeasure
  ClosedPacket := DemoClosed
  AdvancePacket := DemoAdvance
  WakePacket := NoWake
  MigrationPacket := NoMigration
  HaltPacket := DemoFailure
  closedAt
    | .pending => none
    | .done => some .done
    | .rogue => none
  advanceAt
    | .pending =>
        some
          { next := .done
            certificate :=
              { reduces := .finish
                admitted := .finish }
            decreases := by decide }
    | .done => none
    | .rogue => none
  wakeAt := fun _ => none
  migrationAt := fun _ => none
  haltAt
    | .pending => .namedOpenFailure
    | .done => .namedDoneFailure
    | .rogue => .namedRogueFailure

def demoClosedReaderComplete : ClosedReaderComplete demoSystem where
  complete := by
    intro state closed
    cases state with
    | pending =>
        rcases closed with ⟨certificate⟩
        cases certificate
    | done =>
        exact ⟨.done, rfl⟩
    | rogue =>
        rcases closed with ⟨certificate⟩
        cases certificate

def demoReadersComplete : BranchReadersComplete demoSystem where
  closed := demoClosedReaderComplete
  advance := by
    intro state hidden
    cases state with
    | pending =>
        exact
          ⟨{ next := .done
             certificate :=
               { reduces := .finish
                 admitted := .finish }
             decreases := by decide },
            rfl⟩
    | done =>
        rcases hidden with ⟨advance⟩
        cases advance.certificate.reduces
    | rogue =>
        rcases hidden with ⟨advance⟩
        cases advance.certificate.reduces
  wake := by
    intro state hidden
    rcases hidden with ⟨certificate⟩
    cases certificate
  migration := by
    intro state hidden
    rcases hidden with ⟨certificate⟩
    cases certificate

theorem one_admitted_step_closes :
    normalize demoSystem .pending =
      .closed .done .done := by
  simp [normalize, deriveOpen, demoSystem]

theorem demo_core_exact :
    (coreObject demoSystem).Exact :=
  core_exact demoSystem demoClosedReaderComplete

/--
Nat decrease alone cannot create the reverse jump: the domain transition
certificate has no such constructor.
-/
theorem arbitrary_decreasing_jump_without_event_refused :
    demoMeasure .rogue < demoMeasure .pending ∧
      ¬ Nonempty (DemoAdvance .pending .rogue) := by
  constructor
  · decide
  · rintro ⟨certificate⟩
    cases certificate.reduces

theorem selected_advance_is_admitted :
    ∀ certificate,
      deriveOpen demoSystem .pending =
        .advanced .done certificate (by decide) →
      DemoAdmission .pending .done := by
  intro certificate _selected
  exact certificate.admitted

/-! ## Every external branch carries a certificate -/

def awaitSystem : BranchSystem where
  State := DemoState
  measure := demoMeasure
  ClosedPacket := DemoClosed
  AdvancePacket := NoAdvance
  WakePacket := DemoWake
  MigrationPacket := NoMigration
  HaltPacket := DemoFailure
  closedAt := fun _ => none
  advanceAt := fun _ => none
  wakeAt := fun state => some (.external : DemoWake state)
  migrationAt := fun _ => none
  haltAt
    | .pending => .namedOpenFailure
    | .done => .namedDoneFailure
    | .rogue => .namedRogueFailure

theorem await_carries_wake :
    ∃ certificate,
      normalize awaitSystem .pending =
        .await .pending certificate := by
  refine ⟨.external, ?_⟩
  simp [normalize, deriveOpen, awaitSystem]

def reepochSystem : BranchSystem where
  State := DemoState
  measure := demoMeasure
  ClosedPacket := DemoClosed
  AdvancePacket := NoAdvance
  WakePacket := NoWake
  MigrationPacket := DemoMigration
  HaltPacket := DemoFailure
  closedAt := fun _ => none
  advanceAt := fun _ => none
  wakeAt := fun _ => none
  migrationAt
    | .pending => none
    | .done => some (.conservative rfl)
    | .rogue => none
  haltAt
    | .pending => .namedOpenFailure
    | .done => .namedDoneFailure
    | .rogue => .namedRogueFailure

theorem reepoch_carries_conservation :
    ∃ certificate : DemoMigration .done,
      normalize reepochSystem .done =
        .reepoch .done certificate := by
  refine ⟨.conservative rfl, ?_⟩
  simp [normalize, deriveOpen, reepochSystem]

/-- An open-state migration cannot forge the done-state conservation proof. -/
theorem reepoch_without_conservation_refused :
    ¬ Nonempty (DemoMigration .pending) := by
  rintro ⟨certificate⟩
  cases certificate with
  | conservative oldDebtSettled =>
      cases oldDebtSettled

def haltSystem : BranchSystem where
  State := DemoState
  measure := demoMeasure
  ClosedPacket := DemoClosed
  AdvancePacket := NoAdvance
  WakePacket := NoWake
  MigrationPacket := NoMigration
  HaltPacket := DemoFailure
  closedAt := fun _ => none
  advanceAt := fun _ => none
  wakeAt := fun _ => none
  migrationAt := fun _ => none
  haltAt
    | .pending => .namedOpenFailure
    | .done => .namedDoneFailure
    | .rogue => .namedRogueFailure

theorem halt_carries_named_failure :
    ∃ certificate : DemoFailure .pending,
      normalize haltSystem .pending =
        .halt .pending certificate := by
  refine ⟨.namedOpenFailure, ?_⟩
  simp [normalize, deriveOpen, haltSystem]

/-! ## Generic-boundary countermodels -/

/--
The optional readers require their own completeness certificate.  This system
has a real admitted/decreasing transition packet but deliberately omits it
from `advanceAt`.
-/
def omittedAdvanceSystem : BranchSystem :=
  { demoSystem with
    advanceAt := fun _ => none }

theorem omitted_advance_reader_is_not_complete :
    ¬ BranchReadersComplete omittedAdvanceSystem := by
  intro complete
  have hidden :
      Nonempty
        (CertifiedAdvance
          omittedAdvanceSystem.State
          omittedAdvanceSystem.measure
          omittedAdvanceSystem.AdvancePacket
          .pending) :=
    ⟨{ next := .done
       certificate :=
         { reduces := .finish
           admitted := .finish }
       decreases := by decide }⟩
  obtain ⟨certificate, found⟩ :=
    complete.advance .pending hidden
  simp [omittedAdvanceSystem] at found

/--
The generic kernel intentionally does not define RCC semantics: a `Unit`
closed packet can close a `Unit` carrier.  RC-1 must instantiate
`ClosedPacket` with its strong global certificate product before using
`core_exact`.
-/
def unitPacketSystem : BranchSystem where
  State := Unit
  measure := fun _ => 0
  ClosedPacket := fun _ => Unit
  AdvancePacket := fun _ _ => Unit
  WakePacket := fun _ => Unit
  MigrationPacket := fun _ => Unit
  HaltPacket := fun _ => Unit
  closedAt := fun _ => some ()
  advanceAt := fun _ => none
  wakeAt := fun _ => none
  migrationAt := fun _ => none
  haltAt := fun _ => ()

theorem generic_core_still_needs_semantic_packet_adapter :
    normalize unitPacketSystem () = .closed () () := by
  simp [normalize, unitPacketSystem]

end Residua.RCC.ProofCarryingOutcome.Tests

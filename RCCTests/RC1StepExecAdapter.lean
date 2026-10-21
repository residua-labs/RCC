import RCC.RC1StepExecAdapter
import RCCTests.RC1StepMSTBinding
import RCCTests.RelativeCompleteClosure

/-! A concrete adapter witness and its profile-gate mutant. -/

namespace Residua.RCC.RC1StepExecAdapter.Tests

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RC1StepMSTBinding.Tests
open Residua.RCC.RC1StepExecAdapter

def demoAdapter
    {C : ClosureContext Phase} :
    Adapter C (demoSurface C) where
  Raw := Unit
  Outcome := Unit
  Residue := Unit
  q := fun _ => { before := .initial, after := .closed }
  evalRaw := fun _ => ()
  evalClass := fun _ => ()
  rho := fun _ => some ()
  quotient_factorization := by intro raw; cases raw; rfl
  representative_implies_admissible := by
    intro cls rep representative
    rfl
  residue_totality := by
    intro cls active notAdmitted
    cases notAdmitted
  representative_precision := by
    intro cls active admitted
    exact
      ⟨{ before := cls.before
         after := cls.after
         head := (C.snapshotAt cls.before).coordinates.historyHead }, rfl⟩

theorem demo_adapter_has_profile
    {C : ClosureContext Phase} :
    StepExecModel.Profile (RC1StepExecAdapter.model (demoAdapter (C := C))) :=
  adapter_has_profile (demoAdapter (C := C))

/-! ## Non-vacuous raw/q/rho witness -/

structure ConcreteRaw where
  before : Phase
  after : Phase

def acceptedClass : DemoStepClass Phase → Bool
  | { before := .initial, after := .closed } => true
  | _ => false

def guardedSurface
    {C : ClosureContext Phase} : StepSurface C where
  StepClass := DemoStepClass Phase
  SettledEvent := DemoSettledEvent C
  classOf := fun {before after} _ => ⟨before, after⟩
  active := fun _ => true
  admitted := acceptedClass
  sigma := fun cls =>
    if acceptedClass cls then
      some
        { before := cls.before
          after := cls.after
          head := (C.snapshotAt cls.before).coordinates.historyHead }
    else
      none
  preHead := fun event => event.head
  settled := fun _ => True
  append := fun before event after =>
    event.before = before ∧ event.after = after

def concreteAdapter
    {C : ClosureContext Phase} :
    Adapter C (guardedSurface (C := C)) where
  Raw := ConcreteRaw
  Outcome := Bool
  Residue := Unit
  q := fun raw => { before := raw.before, after := raw.after }
  evalRaw := fun raw => acceptedClass { before := raw.before, after := raw.after }
  evalClass := acceptedClass
  rho := fun cls =>
    if acceptedClass cls then none else some ()
  quotient_factorization := by intro raw; rfl
  representative_implies_admissible := by
    intro cls rep representative
    exact (by
      simpa [guardedSurface] using representative :
        acceptedClass cls = true ∧ _).1
  residue_totality := by
    intro cls active notAdmitted
    cases cls with
    | mk before after =>
      cases before <;> cases after <;>
        simp_all [guardedSurface, acceptedClass]
  representative_precision := by
    intro cls active admitted
    cases cls with
    | mk before after =>
      cases before <;> cases after <;>
        simp_all [guardedSurface, acceptedClass]

theorem concrete_adapter_has_profile
    {C : ClosureContext Phase} :
    StepExecModel.Profile
      (RC1StepExecAdapter.model (concreteAdapter (C := C))) :=
  adapter_has_profile (concreteAdapter (C := C))

theorem concrete_nonadmitted_class_has_typed_residue
    {C : ClosureContext Phase} :
    (concreteAdapter (C := C)).rho
        ({ before := .closed, after := .initial } : DemoStepClass Phase) = some () := by
  rfl

theorem profile_rejects_missing_concrete_residue
    {C : ClosureContext Phase}
    (adapter : Adapter C (guardedSurface (C := C)))
    (missing : adapter.rho
        ({ before := .closed, after := .initial } : DemoStepClass Phase) = none) :
    False := by
  obtain ⟨residue, proof⟩ :=
    (adapter_has_profile adapter).residue_totality
      ({ before := .closed, after := .initial } : DemoStepClass Phase)
      rfl rfl
  change adapter.rho
      ({ before := .closed, after := .initial } : DemoStepClass Phase) = some residue at proof
  rw [missing] at proof
  cases proof

end Residua.RCC.RC1StepExecAdapter.Tests

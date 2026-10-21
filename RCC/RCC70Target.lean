import RCCTests.RC1StepExecAdapter

/-! RCC-70 candidate: concrete StepExec/Step-MST adapter and history safety. -/

namespace Residua.RCC.RCC70Target

open Residua.RCC.RC1StepExecAdapter.Tests
open Residua.RCC.RC1StepExecAdapter
open Residua.RCC.RC1StepMSTBinding.Tests
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.StepExecModel
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RelativeCompleteClosure.Tests

/- The concrete adapter has a proof-only universe parameter.  Pinning it to zero
   keeps the independent Lean 4.29 package from leaving that phantom level
   underconstrained while preserving the same adapter definition. -/
def concreteAdapter0
    {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase} :
    RC1StepExecAdapter.Adapter.{0, 0, 0, 0, 0} C
      (guardedSurface (C := C)) :=
  concreteAdapter

theorem concreteProfile
    {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase} :
    StepExecModel.Profile
      (RC1StepExecAdapter.model
        (concreteAdapter0 (C := C))) := by
  exact concrete_adapter_has_profile

theorem nonadmittedResidue
    {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase} :
    (concreteAdapter0 (C := C)).rho
        ({ before := .closed, after := .initial } :
          RC1StepMSTBinding.Tests.DemoStepClass RelativeCompleteClosure.Tests.Phase) = some () :=
  concrete_nonadmitted_class_has_typed_residue

theorem missingResidueRefused
    {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase}
    (adapter : RC1StepExecAdapter.Adapter.{0, 0, 0, 0, 0} C
      (guardedSurface (C := C)))
    (missing : adapter.rho
        ({ before := .closed, after := .initial } :
          RC1StepMSTBinding.Tests.DemoStepClass RelativeCompleteClosure.Tests.Phase) = none) :
    False :=
  profile_rejects_missing_concrete_residue adapter missing

theorem existingAdvanceHistoryEdge
    {State : Type} {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    HistoryEdge (demoSurface C) before after :=
  existing_advance_resolves_to_history_edge packet

theorem existingAdvanceProvenance
    {State : Type} {C : ClosureContext State}
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
  existing_advance_retains_settled_sigma_provenance packet

theorem nonadmittedHistoryRefused
    {State : Type} {C : ClosureContext State}
    {surface : StepSurface C}
    {before after : State}
    {packet : AdvancePacket C before after}
    (notAdmitted : surface.admitted (surface.classOf packet) = false) :
    ¬ Nonempty (BoundAdvance surface packet) :=
  nonadmitted_advance_cannot_resolve_to_history notAdmitted

theorem emptyEventAdvanceRefused
    {State : Type} {C : ClosureContext State}
    {before after : State}
    (packet : AdvancePacket C before after) :
    ¬ Nonempty (BoundAdvance (emptyEventSurface C) packet) :=
  empty_event_mutant_cannot_resolve_existing_advance packet

theorem emptyEventAppendRefused
    {State : Type} {C : ClosureContext State}
    {before after : State} :
    ¬ HistoryEdge (emptyEventSurface C) before after :=
  empty_event_mutant_cannot_append_history

structure Certificate where
  concreteProfile : ∀ {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase},
    StepExecModel.Profile (RC1StepExecAdapter.model (concreteAdapter0 (C := C)))
  nonadmittedResidue : ∀ {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase},
    (concreteAdapter0 (C := C)).rho ({ before := .closed, after := .initial } :
      RC1StepMSTBinding.Tests.DemoStepClass RelativeCompleteClosure.Tests.Phase) = some ()
  missingResidueRefused : ∀ {C : RelativeCompleteClosure.ClosureContext RelativeCompleteClosure.Tests.Phase}
    (adapter : RC1StepExecAdapter.Adapter.{0, 0, 0, 0, 0} C
      (guardedSurface (C := C)))
    (missing : adapter.rho ({ before := .closed, after := .initial } :
      RC1StepMSTBinding.Tests.DemoStepClass RelativeCompleteClosure.Tests.Phase) = none), False
  existingAdvanceHistoryEdge : ∀ {State : Type} {C : ClosureContext State}
    {before after : State}, AdvancePacket C before after → HistoryEdge (demoSurface C) before after
  existingAdvanceProvenance : ∀ {State : Type} {C : ClosureContext State}
    {before after : State}, AdvancePacket C before after →
      ∃ (source : AdvancePacket C before after) (event : (demoSurface C).SettledEvent),
      (demoSurface C).active ((demoSurface C).classOf source) = true ∧
      (demoSurface C).admitted ((demoSurface C).classOf source) = true ∧
      (demoSurface C).sigma ((demoSurface C).classOf source) = some event ∧
      (demoSurface C).preHead event = (C.snapshotAt before).coordinates.historyHead ∧
      (demoSurface C).settled event ∧ (demoSurface C).append before event after
  nonadmittedHistoryRefused : ∀ {State : Type} {C : ClosureContext State}
    {surface : StepSurface C} {before after : State} {packet : AdvancePacket C before after},
    surface.admitted (surface.classOf packet) = false → ¬ Nonempty (BoundAdvance surface packet)
  emptyEventAdvanceRefused : ∀ {State : Type} {C : ClosureContext State}
    {before after : State} (packet : AdvancePacket C before after),
    ¬ Nonempty (BoundAdvance (emptyEventSurface C) packet)
  emptyEventAppendRefused : ∀ {State : Type} {C : ClosureContext State}
    {before after : State}, ¬ HistoryEdge (emptyEventSurface C) before after

def certificate : Certificate where
  concreteProfile := by intro C; exact concreteProfile
  nonadmittedResidue := by intro C; exact nonadmittedResidue
  missingResidueRefused := by intro C adapter missing; exact missingResidueRefused adapter missing
  existingAdvanceHistoryEdge := by intro State C before after packet; exact existingAdvanceHistoryEdge packet
  existingAdvanceProvenance := by intro State C before after packet; exact existingAdvanceProvenance packet
  nonadmittedHistoryRefused := by intro State C surface before after packet notAdmitted; exact nonadmittedHistoryRefused notAdmitted
  emptyEventAdvanceRefused := by intro State C before after packet; exact emptyEventAdvanceRefused packet
  emptyEventAppendRefused := by intro State C before after; exact emptyEventAppendRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC70Target

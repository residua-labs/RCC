import RCC.M1Target

/-!
M1 target tests: the certificate is now the real slot-coherence encoding,
not the RCC-71 aliasing stub.  These pins keep the names consumed by the
independent conformance probe (M1Independent.lean) stable.
-/

namespace Residua.RCC.M1Target.Tests

open Residua.RCC.M1Target

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

/-- Same statement as `Certificate.slotCoherenceEdge`, proved from the theorem that
fills that field (`certificate.slotCoherenceEdge := slot_coherence_edge`). Going
through `certificate.slotCoherenceEdge` leaves the unconstrained universe levels of
the 105-universe-parameter `Certificate` as metavariables, which Lean 4.14 rejects
in a theorem body. -/
theorem target_slot_coherence_edge_reexported :
    ∀ {State : Type} {C : Residua.RCC.RelativeCompleteClosure.ClosureContext State}
      (slot : SlotSurface C)
      {before after : State}
      {packet : Residua.RCC.RC1StepMSTBinding.AdvancePacket C before after}
      (binding : Residua.RCC.RC1StepMSTBinding.BoundAdvance slot.surface packet),
      slot.postHead binding.event =
        (C.snapshotAt after).coordinates.historyHead :=
  by
    intro State C slot before after packet binding
    exact slot_coherence_edge slot binding

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports
#print axioms target_slot_coherence_edge_reexported

end Residua.RCC.M1Target.Tests

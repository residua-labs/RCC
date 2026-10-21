import RCC.RCC42Target

/-! Independent checks for the RCC-42 canonical admission-linearizer target. -/

namespace Residua.RCC.RCC42Target.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AdmissionLinearizer.RealizationTests
open Residua.RCC.RCC42Target

theorem target_has_global_interface_witness :
    globalLinearizer.finalize
        0 activatedState (activatedCanonicalSnapshot 0) activateRequest =
      .Ok (globallyActivated 0) :=
  certificate.globalInterface

theorem target_preserves_same_slot_single_valuedness :
    judgmentEq.Equivalent
      activateProposal.judgment activateProposal.judgment :=
  certificate.sameSlotUnique
    (first := globallyActivated 0)
    (second := globallyActivated 1)
    rfl rfl rfl

theorem target_rejects_conflicting_local_successes :
    ∀ (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Nat writerSpec judgmentEq)
      (firstVersion secondVersion : Nat)
      (activateCanonical :
        CanonicalWriterSnapshot linearizer firstVersion activatedState)
      (rollbackCanonical :
        CanonicalWriterSnapshot linearizer secondVersion rollbackState),
      False :=
  certificate.localConflictRejected

theorem target_certificate_is_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

#print axioms target_has_global_interface_witness
#print axioms target_preserves_same_slot_single_valuedness
#print axioms target_rejects_conflicting_local_successes
#print axioms target_certificate_is_nonempty

end Residua.RCC.RCC42Target.Tests

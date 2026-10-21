import RCC.RCC44Target

/-! Independent checks for the RCC-44 authority-reconfiguration target. -/

namespace Residua.RCC.RCC44Target.Tests

open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.AuthorityReconfiguration.Tests
open Residua.RCC.RCC44Target

theorem target_has_joint_and_finalized_authority :
    Nonempty (TestAuthorization transition) ∧
      Nonempty (TestAuthorization transition) :=
  ⟨certificate.jointAuthorized, certificate.finalizedAuthorized⟩

theorem target_coordinate_binding_is_unique :
    ∀ {candidate : AuthorityTransition Config Slot Head Authority Member},
      TestAuthorization candidate →
        candidate.activationSlot = transition.activationSlot →
        candidate.activationHead = transition.activationHead →
        candidate.roundBoundary = transition.roundBoundary →
        candidate = transition :=
  certificate.coordinateUnique

theorem target_disjoint_local_finalizations_are_refused :
    (match assessDisjointFinalization disjointAttempt with
      | .refuse .disjointFinalization => true
      | _ => false) = true :=
  certificate.disjointRefused

theorem target_certificate_is_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

#print axioms target_has_joint_and_finalized_authority
#print axioms target_coordinate_binding_is_unique
#print axioms target_disjoint_local_finalizations_are_refused
#print axioms target_certificate_is_nonempty

end Residua.RCC.RCC44Target.Tests

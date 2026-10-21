import RCCTests.AuthorityReconfiguration

/-!
# RCC-44 target package

This candidate packages authority reconfiguration as one coordinate-bound
transition: joint-quorum or actual-finalizer authority is accepted, while
disjoint local finalizations cannot manufacture shared authority.
-/

namespace Residua.RCC.RCC44Target

open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.AuthorityReconfiguration.Tests

structure Certificate : Prop where
  jointAuthorized : Nonempty (TestAuthorization transition)
  finalizedAuthorized : Nonempty (TestAuthorization transition)
  coordinateUnique :
    ∀ {candidate : AuthorityTransition Config Slot Head Authority Member},
      TestAuthorization candidate →
        candidate.activationSlot = transition.activationSlot →
        candidate.activationHead = transition.activationHead →
        candidate.roundBoundary = transition.roundBoundary →
        candidate = transition
  disjointRefused :
    (match assessDisjointFinalization disjointAttempt with
      | .refuse .disjointFinalization => true
      | _ => false) = true

def certificate : Certificate where
  jointAuthorized := joint_quorum_is_authorized
  finalizedAuthorized := actual_successful_finalize_handoff_is_authorized
  coordinateUnique := authorized_fixture_coordinate_is_unique
  disjointRefused := disjoint_local_finalizations_without_shared_domain_are_refused

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC44Target

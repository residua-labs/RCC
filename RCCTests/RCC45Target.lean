import RCC.RCC45Target

/-! Independent checks for RCC-45 finalized-head/window eligibility. -/

namespace Residua.RCC.RCC45Target.Tests

open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.RCC45Target

theorem target_accepts_complete_finalized_window :
    (match assessFull currentSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .eligible _ => true
      | .await _ => false) = true :=
  certificate.eligible

theorem target_local_fork_awaits :
    localA.localGreen = true ∧ localB.localGreen = true ∧
      localA.localHead ≠ localB.localHead ∧
      (match assessFull currentSnapshot none none none with
        | .await .sourceWindowNotFinalized => true
        | _ => false) = true :=
  certificate.localForkAwaits

theorem target_omitted_partition_awaits :
    (match assessFull omittedPartitionSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true :=
  certificate.omittedPartitionAwaits

theorem target_awaits_pending_transition :
    (match assessFinalizedClosure
        pendingTransitionSnapshot (some headEnvelope) (some fullSealEnvelope)
        (none : Option (StableConfigEvidence
          pendingTransitionSnapshot.transitionView
            pendingTransitionSnapshot.slot pendingTransitionSnapshot.head
            pendingTransitionSnapshot.config)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true :=
  certificate.pendingTransitionAwaits

theorem target_certificate_is_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

#print axioms target_accepts_complete_finalized_window
#print axioms target_local_fork_awaits
#print axioms target_omitted_partition_awaits
#print axioms target_awaits_pending_transition
#print axioms target_certificate_is_nonempty

end Residua.RCC.RCC45Target.Tests

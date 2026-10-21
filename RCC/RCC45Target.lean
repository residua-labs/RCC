import RCCTests.FinalizedHeadWindow

/-!
# RCC-45 target package

This candidate packages finalized-head/window eligibility.  Local GREEN views,
omitted partitions, stale heads/watermarks, and pending transitions remain
awaiting states rather than closure evidence.
-/

namespace Residua.RCC.RCC45Target

open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests

structure Certificate : Prop where
  eligible :
    (match assessFull currentSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .eligible _ => true
      | .await _ => false) = true
  localForkAwaits :
    localA.localGreen = true ∧ localB.localGreen = true ∧
      localA.localHead ≠ localB.localHead ∧
      (match assessFull currentSnapshot none none none with
        | .await .sourceWindowNotFinalized => true
        | _ => false) = true
  omittedPartitionAwaits :
    (match assessFull omittedPartitionSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true
  pendingTransitionAwaits :
    (match assessFinalizedClosure
        pendingTransitionSnapshot (some headEnvelope) (some fullSealEnvelope)
        (none : Option (StableConfigEvidence
          pendingTransitionSnapshot.transitionView
            pendingTransitionSnapshot.slot pendingTransitionSnapshot.head
            pendingTransitionSnapshot.config)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true

def certificate : Certificate where
  eligible := finalized_head_and_window_are_eligible
  localForkAwaits := two_local_greens_global_fork_awaits
  omittedPartitionAwaits := window_omitting_partition_awaits
  pendingTransitionAwaits := actual_pending_transition_cannot_be_hidden

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC45Target

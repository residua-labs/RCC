import RCCTests.FinalizedHeadWindow

/-! RCC-16 candidate: only a globally finalized head and complete window can close. -/

namespace Residua.RCC.RCC16Target

open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.FinalizedHeadWindow

structure Certificate where
  finalizedHeadConsumesAdmission :
    headCertificate.admission = admissionA
  finalizedHeadAndWindowEligible :
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
  staleHeadAwaits :
    (match assessFull staleHeadSnapshot (some headEnvelope)
        (some fullSealEnvelope)
        (some (stableConfigEvidenceAt .deploy .headB .v1)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true
  staleWatermarkAwaits :
    (match assessFull staleWatermarkSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true
  pendingTransitionExcludesStable :
    ¬ Nonempty
      (StableConfigEvidence pendingTransitionView .deploy .headA .v1)
  pendingTransitionCannotBeHidden :
    (match assessFinalizedClosure
        pendingTransitionSnapshot (some headEnvelope) (some fullSealEnvelope)
        (none : Option
          (StableConfigEvidence pendingTransitionSnapshot.transitionView
            pendingTransitionSnapshot.slot pendingTransitionSnapshot.head
            pendingTransitionSnapshot.config)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true

def certificate : Certificate where
  finalizedHeadConsumesAdmission := finalized_head_consumes_rcc42_history
  finalizedHeadAndWindowEligible := finalized_head_and_window_are_eligible
  localForkAwaits := two_local_greens_global_fork_awaits
  omittedPartitionAwaits := window_omitting_partition_awaits
  staleHeadAwaits := window_bound_to_stale_head_awaits
  staleWatermarkAwaits := stale_watermark_awaits
  pendingTransitionExcludesStable := actual_pending_transition_excludes_stable_evidence
  pendingTransitionCannotBeHidden := actual_pending_transition_cannot_be_hidden

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC16Target

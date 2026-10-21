import RCC.RCC46Target

/-! Thin admission checks for RCC-46 conditional finality liveness. -/

namespace Residua.RCC.RCC46Target.Tests

open Residua.RCC.FinalityLiveness.Tests
open Residua.RCC.FinalityLiveness
open Residua.RCC.AdmissionLinearizer

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_complete_packet_reaches_success :
    ∃ witness,
      runConditionalFinality
          world progressAdapter continuousEligibility completePacket =
        .Ok witness ∧
      fencedFinalize writerSpec judgmentEq
          (world.stateAt witness.step) request =
        .Ok witness.success.localSuccess.output :=
  complete_packet_runs_to_actual_success

theorem target_missing_quorum_awaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket =
      .Await .finalityQuorumUnavailable :=
  missing_quorum_awaits

theorem target_local_commit_cannot_bypass_missing_quorum :
    committedState.decisions .deploy = some .commit ∧
      (runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket).value? =
        none :=
  local_commit_does_not_bypass_missing_quorum

theorem target_all_true_environment_cannot_fabricate_progress :
    ¬ Nonempty (FinalityProgressAdapter allTrueUncommittedWorld) :=
  all_true_environment_cannot_fabricate_finality_progress

#print axioms target_certificate_nonempty
#print axioms target_complete_packet_reaches_success
#print axioms target_missing_quorum_awaits
#print axioms target_local_commit_cannot_bypass_missing_quorum
#print axioms target_all_true_environment_cannot_fabricate_progress

end Residua.RCC.RCC46Target.Tests

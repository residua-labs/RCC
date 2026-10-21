import RCCTests.FinalityLiveness

/-!
# RCC-46 target package

This candidate packages conditional finality liveness.  The complete premise
packet reaches the actual fenced finalizer within its declared horizon; every
missing environmental premise returns a named Await rather than fabricating
progress.
-/

namespace Residua.RCC.RCC46Target

open Residua.RCC.FinalityLiveness
open Residua.RCC.FinalityLiveness.Tests
open Residua.RCC.AdmissionLinearizer

structure Certificate : Prop where
  completePacketSucceeds :
    ∃ witness,
      runConditionalFinality
          world progressAdapter continuousEligibility completePacket =
        .Ok witness ∧
      fencedFinalize writerSpec judgmentEq
          (world.stateAt witness.step) request =
        .Ok witness.success.localSuccess.output
  boundedHorizon : boundedWitness.step ≤ world.horizon
  missingQuorumAwaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket =
      .Await .finalityQuorumUnavailable
  localCommitCannotBypass :
    committedState.decisions .deploy = some .commit ∧
      (runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket).value? =
        none

def certificate : Certificate where
  completePacketSucceeds := complete_packet_runs_to_actual_success
  boundedHorizon := bounded_witness_is_within_declared_horizon
  missingQuorumAwaits := missing_quorum_awaits
  localCommitCannotBypass := local_commit_does_not_bypass_missing_quorum

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC46Target

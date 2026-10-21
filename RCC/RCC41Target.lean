import RCCTests.DurableVoteLock

/-!
# RCC-41 target package

This certificate packages the durable full-vote binding, crash/split-brain and
key-rotation countermodels, together with the lawful higher-round unlock
positive control. Runtime storage durability and production crypto remain
explicit implementation obligations.
-/

namespace Residua.RCC.RCC41Target

open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests

structure Certificate : Prop where
  fullVoteBinding :
    SignatureBinding exactVoteSignatureScheme releaseP.envelope
  signedCoordinateCoverage :
    voteP.configQ = votePVerdictMutant.configQ ∧
      voteP.epochQ = votePVerdictMutant.epochQ ∧
      voteP.slotQ = votePVerdictMutant.slotQ ∧
      voteP.parentHeadQ = votePVerdictMutant.parentHeadQ ∧
      voteP.round = votePVerdictMutant.round ∧
      voteP.proposalClassQ = votePVerdictMutant.proposalClassQ ∧
      voteP.policyQ = votePVerdictMutant.policyQ ∧
      voteP.verdict ≠ votePVerdictMutant.verdict ∧
      voteP.signerQ = votePVerdictMutant.signerQ ∧
      voteP.priorVoteQ = votePVerdictMutant.priorVoteQ
  verdictMutantRefused :
    ¬ SignatureBinding exactVoteSignatureScheme verdictMutantEnvelope
  crashLostLockRefused :
    ¬ NonFaultySignerContinuity releaseP releaseQAfterCrash
  rotationLostLockRefused :
    ¬ NonFaultySignerContinuity releaseP releaseQAfterRotation
  lawfulUnlockPreserved :
    ¬ ConflictingJudgments releaseP releaseQUnlocked

def certificate : Certificate where
  fullVoteBinding := ⟨releaseP.validSignature.accepted⟩
  signedCoordinateCoverage := verdict_mutant_changes_only_the_signed_verdict
  verdictMutantRefused := unbound_verdict_mutant_has_no_signature_binding
  crashLostLockRefused := crash_lost_lock_is_not_nonfaulty
  rotationLostLockRefused := rotation_lost_lock_is_not_nonfaulty
  lawfulUnlockPreserved := lawful_higher_round_unlock_is_not_equivocation

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC41Target

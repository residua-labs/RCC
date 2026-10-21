import RCC.RCC41Target

/-! Independent target checks for the RCC-41 certificate package. -/

namespace Residua.RCC.RCC41Target.Tests

open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.RCC41Target

theorem certificate_carries_exact_vote_signature_binding :
    SignatureBinding exactVoteSignatureScheme releaseP.envelope :=
  certificate.fullVoteBinding

theorem verdict_mutant_is_rejected_without_invalidating_goal :
    ¬ SignatureBinding exactVoteSignatureScheme verdictMutantEnvelope :=
  certificate.verdictMutantRefused

theorem crash_and_rotation_are_distinct_nonfaulty_failures :
    (¬ NonFaultySignerContinuity releaseP releaseQAfterCrash) ∧
      (¬ NonFaultySignerContinuity releaseP releaseQAfterRotation) :=
  ⟨certificate.crashLostLockRefused, certificate.rotationLostLockRefused⟩

theorem lawful_higher_round_unlock_is_not_equivocation :
    ¬ ConflictingJudgments releaseP releaseQUnlocked :=
  certificate.lawfulUnlockPreserved

theorem target_certificate_is_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

#print axioms certificate_carries_exact_vote_signature_binding
#print axioms verdict_mutant_is_rejected_without_invalidating_goal
#print axioms crash_and_rotation_are_distinct_nonfaulty_failures
#print axioms lawful_higher_round_unlock_is_not_equivocation
#print axioms target_certificate_is_nonempty

end Residua.RCC.RCC41Target.Tests

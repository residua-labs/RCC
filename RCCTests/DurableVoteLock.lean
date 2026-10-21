import RCC.DurableVoteLock

/-!
# RCC-41 Durable Signer Non-Equivocation Countermodels

RED-first witnesses for ADR §23.3, §23.5, and §23.12.  Every released signature
is bound to a full vote and a durable lock committed before release.  The
countermodels fail only at the cross-process/crash/rotation continuity layer.
-/

open Residua.RCC.DurableVoteLock

namespace Residua.RCC.DurableVoteLock.Tests

inductive Token
  | configA | configB
  | epochA | epochB
  | slotA | slotB
  | headA | headB
  | policyA | policyB
  | proposalP | proposalQ
  | verdictAccept | verdictReject
  | signerA
  | keyOld | keyNew
  | processOne | processTwo
  | lockP | lockQ
  | signatureP | signatureQ
  | unlockCert
  deriving DecidableEq, Repr

def voteP : Vote Token where
  configQ := .configA
  epochQ := .epochA
  slotQ := .slotA
  parentHeadQ := .headA
  round := 0
  proposalClassQ := .proposalP
  policyQ := .policyA
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := none

def voteQFresh : Vote Token where
  configQ := .configA
  epochQ := .epochA
  slotQ := .slotA
  parentHeadQ := .headA
  round := 0
  proposalClassQ := .proposalQ
  policyQ := .policyA
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := none

/--
The verdict mutant changes one signed coordinate while retaining the original
proposal class and every other vote coordinate.
-/
def votePVerdictMutant : Vote Token where
  configQ := .configA
  epochQ := .epochA
  slotQ := .slotA
  parentHeadQ := .headA
  round := 0
  proposalClassQ := .proposalP
  policyQ := .policyA
  verdict := .verdictReject
  signerQ := .signerA
  priorVoteQ := none

def voteQUnlocked : Vote Token where
  configQ := .configA
  epochQ := .epochA
  slotQ := .slotA
  parentHeadQ := .headA
  round := 1
  proposalClassQ := .proposalQ
  policyQ := .policyA
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := some .lockP

/--
Test-only idealized scheme: a signature is the exact canonical vote message.
Its equality acceptance relation makes message binding explicit without
assuming any concrete cryptographic implementation.
-/
abbrev exactVoteSignatureScheme : SignatureScheme Token where
  Signature := Vote Token
  Message := Vote Token
  canonicalVoteMessage := fun vote => vote
  canonicalVoteMessage_injective :=
    fun {_first _second} sameMessage => sameMessage
  Accepts := fun signature message => signature = message
  acceptanceBindsMessage := by
    intro signature first second firstAccepted secondAccepted
    exact firstAccepted.symm.trans secondAccepted

def runtimeOldProcessOne : SignerRuntime Token where
  signerQ := .signerA
  keyQ := .keyOld
  processQ := .processOne

def runtimeOldProcessTwo : SignerRuntime Token where
  signerQ := .signerA
  keyQ := .keyOld
  processQ := .processTwo

def runtimeNewKey : SignerRuntime Token where
  signerQ := .signerA
  keyQ := .keyNew
  processQ := .processTwo

def commitP : DurableLockCommit Token where
  lock := { vote := voteP, lockQ := .lockP }
  committedAt := 0

def commitQFresh : DurableLockCommit Token where
  lock := { vote := voteQFresh, lockQ := .lockQ }
  committedAt := 2

def releaseP : ReleasedSignature Token exactVoteSignatureScheme where
  commit := commitP
  envelope := { signedVote := voteP, signatureQ := voteP }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessOne
  runtimeSigner := rfl
  releasedAt := 1
  lockBeforeRelease := by decide

def releaseQAfterCrash : ReleasedSignature Token exactVoteSignatureScheme where
  commit := commitQFresh
  envelope := { signedVote := voteQFresh, signatureQ := voteQFresh }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessTwo
  runtimeSigner := rfl
  releasedAt := 3
  lockBeforeRelease := by decide

def releaseQAfterRotation :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := commitQFresh
  envelope := { signedVote := voteQFresh, signatureQ := voteQFresh }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeNewKey
  runtimeSigner := rfl
  releasedAt := 3
  lockBeforeRelease := by decide

/-! ## CM-VOTE-LOCK-00: same proposal, opposite verdict after lost lock -/

def commitPVerdictMutant : DurableLockCommit Token where
  lock := { vote := votePVerdictMutant, lockQ := .lockQ }
  committedAt := 2

def releasePVerdictAfterLostLock :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := commitPVerdictMutant
  envelope := {
    signedVote := votePVerdictMutant
    signatureQ := votePVerdictMutant
  }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessTwo
  runtimeSigner := rfl
  releasedAt := 3
  lockBeforeRelease := by decide

theorem verdict_only_pair_has_two_valid_exact_signatures :
    exactVoteSignatureScheme.Accepts
        releaseP.envelope.signatureQ
        (exactVoteSignatureScheme.canonicalVoteMessage (releasedVote releaseP)) ∧
      exactVoteSignatureScheme.Accepts
        releasePVerdictAfterLostLock.envelope.signatureQ
        (exactVoteSignatureScheme.canonicalVoteMessage
          (releasedVote releasePVerdictAfterLostLock)) :=
  ⟨releaseP.validSignature.accepted,
    releasePVerdictAfterLostLock.validSignature.accepted⟩

theorem verdict_only_pair_shares_context_round_and_proposal :
    SameDecisionContext
        (releasedVote releaseP)
        (releasedVote releasePVerdictAfterLostLock) ∧
      (releasedVote releaseP).round =
        (releasedVote releasePVerdictAfterLostLock).round ∧
      (releasedVote releaseP).proposalClassQ =
        (releasedVote releasePVerdictAfterLostLock).proposalClassQ ∧
      (releasedVote releaseP).verdict ≠
        (releasedVote releasePVerdictAfterLostLock).verdict := by
  exact ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl, rfl, by decide⟩

theorem verdict_only_lost_lock_can_equivocate_locally :
    ConflictingJudgments releaseP releasePVerdictAfterLostLock := by
  constructor
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  constructor
  · rfl
  constructor
  · decide
  constructor
  · intro unlock
    obtain ⟨certificate, lawful⟩ := unlock
    exact (Nat.lt_irrefl 0) lawful.higherRound
  · intro unlock
    obtain ⟨certificate, lawful⟩ := unlock
    exact (Nat.lt_irrefl 0) lawful.higherRound

theorem verdict_only_lost_lock_is_not_nonfaulty :
    ¬ NonFaultySignerContinuity
      releaseP releasePVerdictAfterLostLock := by
  intro continuity
  exact durable_signer_non_equivocation continuity
    verdict_only_lost_lock_can_equivocate_locally

theorem verdict_only_split_brain_processes_are_distinct :
    releaseP.runtime.processQ ≠
      releasePVerdictAfterLostLock.runtime.processQ := by
  decide

theorem verdict_only_split_brain_is_not_nonfaulty :
    ¬ NonFaultySignerContinuity
      releaseP releasePVerdictAfterLostLock :=
  verdict_only_lost_lock_is_not_nonfaulty

theorem verdict_only_nonfaulty_would_preserve_canonical_judgment
    (continuity :
      NonFaultySignerContinuity releaseP releasePVerdictAfterLostLock) :
    canonicalJudgment (releasedVote releaseP) =
      canonicalJudgment (releasedVote releasePVerdictAfterLostLock) :=
  same_round_continuity_canonical_judgment_equal continuity rfl

theorem p_and_fresh_q_conflict :
    ConflictingJudgments releaseP releaseQAfterCrash := by
  constructor
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  constructor
  · rfl
  constructor
  · decide
  constructor
  · intro unlock
    obtain ⟨certificate, lawful⟩ := unlock
    exact (Nat.lt_irrefl 0) lawful.higherRound
  · intro unlock
    obtain ⟨certificate, lawful⟩ := unlock
    exact (Nat.lt_irrefl 0) lawful.higherRound

/-! ## CM-VOTE-LOCK-01: sign, crash, lose lock, sign a fresh conflict -/

theorem crash_lost_lock_can_equivocate_locally :
    ConflictingJudgments releaseP releaseQAfterCrash :=
  p_and_fresh_q_conflict

theorem crash_lost_lock_is_not_nonfaulty :
    ¬ NonFaultySignerContinuity releaseP releaseQAfterCrash := by
  intro continuity
  exact durable_signer_non_equivocation continuity
    crash_lost_lock_can_equivocate_locally

/-! ## CM-VOTE-LOCK-02: split-brain processes sharing one key -/

theorem split_brain_processes_are_distinct :
    releaseP.runtime.processQ ≠ releaseQAfterCrash.runtime.processQ := by
  decide

theorem split_brain_without_shared_lock_is_not_nonfaulty :
    ¬ NonFaultySignerContinuity releaseP releaseQAfterCrash :=
  crash_lost_lock_is_not_nonfaulty

/-! ## CM-VOTE-LOCK-03: a bare proposal signature replays across context -/

def replayVote : Vote Token where
  configQ := .configB
  epochQ := .epochB
  slotQ := .slotB
  parentHeadQ := .headB
  round := 0
  proposalClassQ := .proposalP
  policyQ := .policyB
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := none

def bareProposalSignature : BareProposalSignature Token where
  proposalClassQ := .proposalP
  signatureQ := .signatureP

theorem bare_signature_replays_on_original_vote :
    BareSignatureAccepts bareProposalSignature voteP := by
  rfl

theorem bare_signature_replays_on_different_context :
    BareSignatureAccepts bareProposalSignature replayVote := by
  rfl

theorem bare_signature_replays_on_unbound_verdict_mutant :
    BareSignatureAccepts bareProposalSignature votePVerdictMutant := by
  rfl

theorem replay_context_changes_config_epoch_slot_and_head :
    voteP.configQ ≠ replayVote.configQ ∧
      voteP.epochQ ≠ replayVote.epochQ ∧
      voteP.slotQ ≠ replayVote.slotQ ∧
      voteP.parentHeadQ ≠ replayVote.parentHeadQ := by
  decide

/-! ## Safe binding: a signature cannot replay across the verdict coordinate -/

def verdictMutantEnvelope : SignatureEnvelope Token exactVoteSignatureScheme where
  signedVote := votePVerdictMutant
  signatureQ := voteP

theorem verdict_mutant_changes_only_the_signed_verdict :
    voteP.configQ = votePVerdictMutant.configQ ∧
      voteP.epochQ = votePVerdictMutant.epochQ ∧
      voteP.slotQ = votePVerdictMutant.slotQ ∧
      voteP.parentHeadQ = votePVerdictMutant.parentHeadQ ∧
      voteP.round = votePVerdictMutant.round ∧
      voteP.proposalClassQ = votePVerdictMutant.proposalClassQ ∧
      voteP.policyQ = votePVerdictMutant.policyQ ∧
      voteP.verdict ≠ votePVerdictMutant.verdict ∧
      voteP.signerQ = votePVerdictMutant.signerQ ∧
      voteP.priorVoteQ = votePVerdictMutant.priorVoteQ := by
  decide

theorem same_signature_cannot_accept_unbound_verdict_mutant :
    ¬ exactVoteSignatureScheme.Accepts
      voteP
      (exactVoteSignatureScheme.canonicalVoteMessage votePVerdictMutant) := by
  intro mutantAccepted
  have sameVote : voteP = votePVerdictMutant :=
    same_signature_acceptance_unique_vote
      (scheme := exactVoteSignatureScheme)
      (firstAccepted := rfl)
      (secondAccepted := mutantAccepted)
  exact (by decide : voteP.verdict ≠ votePVerdictMutant.verdict)
    (congrArg Vote.verdict sameVote)

theorem unbound_verdict_mutant_has_no_signature_binding :
    ¬ SignatureBinding exactVoteSignatureScheme verdictMutantEnvelope := by
  intro binding
  exact same_signature_cannot_accept_unbound_verdict_mutant binding.accepted

theorem released_signature_carries_valid_full_vote_binding :
    exactVoteSignatureScheme.Accepts
      releaseP.envelope.signatureQ
      (exactVoteSignatureScheme.canonicalVoteMessage (releasedVote releaseP)) :=
  releaseP.validSignature.accepted

/-! ## CM-VOTE-LOCK-04: key rotation drops the prior lock -/

theorem rotation_changes_physical_key :
    releaseP.runtime.keyQ ≠ releaseQAfterRotation.runtime.keyQ := by
  decide

theorem rotation_lost_lock_is_not_nonfaulty :
    ¬ NonFaultySignerContinuity releaseP releaseQAfterRotation := by
  intro continuity
  exact durable_signer_non_equivocation continuity p_and_fresh_q_conflict

/-! ## Positive control: certified higher-round unlock -/

def commitQUnlocked : DurableLockCommit Token where
  lock := { vote := voteQUnlocked, lockQ := .lockQ }
  committedAt := 3

def releaseQUnlocked :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := commitQUnlocked
  envelope := { signedVote := voteQUnlocked, signatureQ := voteQUnlocked }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessTwo
  runtimeSigner := rfl
  releasedAt := 4
  lockBeforeRelease := by decide

def unlockCertificate : UnlockCertificate Token where
  certificateQ := .unlockCert
  committedAt := 2

def lawfulUnlock :
    LawfulHigherRoundUnlock commitP commitQUnlocked unlockCertificate where
  sameDecisionContext := ⟨rfl, rfl, rfl, rfl, rfl⟩
  sameSigner := rfl
  higherRound := by decide
  priorVoteContinuity := rfl
  certificateBeforeNewLock := by decide

def unlockedContinuity :
    NonFaultySignerContinuity releaseP releaseQUnlocked where
  sameSigner := rfl
  lockContinuity := .forward (.unlock unlockCertificate lawfulUnlock)

theorem lawful_higher_round_unlock_is_not_equivocation :
    ¬ ConflictingJudgments releaseP releaseQUnlocked := by
  exact durable_signer_non_equivocation unlockedContinuity

#print axioms crash_lost_lock_is_not_nonfaulty
#print axioms split_brain_without_shared_lock_is_not_nonfaulty
#print axioms verdict_only_pair_has_two_valid_exact_signatures
#print axioms verdict_only_lost_lock_can_equivocate_locally
#print axioms verdict_only_lost_lock_is_not_nonfaulty
#print axioms verdict_only_split_brain_is_not_nonfaulty
#print axioms same_round_continuity_canonical_judgment_equal
#print axioms verdict_only_nonfaulty_would_preserve_canonical_judgment
#print axioms replay_context_changes_config_epoch_slot_and_head
#print axioms bare_signature_replays_on_unbound_verdict_mutant
#print axioms same_signature_acceptance_unique_vote
#print axioms same_signature_cannot_accept_unbound_verdict_mutant
#print axioms unbound_verdict_mutant_has_no_signature_binding
#print axioms released_signature_carries_valid_full_vote_binding
#print axioms rotation_lost_lock_is_not_nonfaulty
#print axioms lawful_higher_round_unlock_is_not_equivocation

end Residua.RCC.DurableVoteLock.Tests

import RCC.KeyEpochVote
import RCCTests.DurableVoteLock

/-!
# RCC-52 Key-Epoch Vote Countermodels

The positive witness consumes an actual RCC-41 release and the actual new phase
of an RCC-44 transition whose membership delta adds `epochA` and removes
`epochB`.  Three mutants demonstrate the load-bearing bindings:

* one runtime key cannot be reused across both transition epochs;
* an old signer epoch cannot be replayed in the new phase; and
* a vote for the old configuration cannot be replayed in the new phase.
-/

namespace Residua.RCC.KeyEpochVote.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.KeyEpochVote

/-- One actual key rotation: config B/epoch B retires at round zero. -/
def keyTransition :
    AuthorityTransition Token Token Token Token Token where
  oldConfig := .configB
  newConfig := .configA
  activationSlot := .slotA
  activationHead := .headA
  roundBoundary := 0
  membershipDelta := {
    added := [.epochA]
    removed := [.epochB]
  }
  preStateAuthority := .signerA

/-- The fixed transition domain accepts only the exact key transition. -/
def keyJointProtocol :
    JointQuorumProtocol
      Token Token Token Token Token Token Token where
  OldAccepts _ candidate := candidate = keyTransition
  NewAccepts _ candidate := candidate = keyTransition
  TransitionCoherent candidate := candidate = keyTransition
  jointBindsCoherent := by
    intro _oldReceipt _newReceipt _candidate oldAccepted _newAccepted
    exact oldAccepted
  coherentAtCoordinate := by
    intro _first _second firstCoherent secondCoherent _sameSlot _sameHead
      _sameRound
    exact firstCoherent.trans secondCoherent.symm

def keyJointEvidence :
    JointQuorumTransition keyJointProtocol keyTransition where
  oldReceipt := .configB
  newReceipt := .configA
  oldAccepted := rfl
  newAccepted := rfl

def keyWriterSpec : FencedWriterSpec Token Token where
  slotParent := fun _ => .headA

def keyJudgmentEquivalence : JudgmentEquivalence Token where
  Equivalent := Eq
  refl := by intro _judgment; rfl
  symm := by intro _first _second same; exact same.symm
  trans := by
    intro _first _second _third firstSecond secondThird
    exact Eq.trans firstSecond secondThird
  decide := fun first second =>
    inferInstanceAs (Decidable (first = second))

def keyJudgmentAdapter :
    ReconfigurationJudgmentAdapter
      Token Token Token Token Token Token keyJudgmentEquivalence where
  project _judgment := keyTransition
  equivalentBindsTransition := by
    intro _first _second _equivalent
    rfl

def keyWriterState :
    FencedWriterState Token Token Token Token where
  generation := .epochA
  canonicalHead := .headA
  decisions := fun _ => none

abbrev KeyAuthorityEvidence
    (_proposal : Proposal Token Token Token) : Type :=
  PUnit

def keyEnvelope :
    AuthorizedTransitionEnvelope
      KeyAuthorityEvidence keyJointProtocol keyWriterSpec
        keyJudgmentEquivalence keyJudgmentAdapter keyWriterState where
  transition := keyTransition
  authorization := .jointQuorum keyJointEvidence

/-- The exact post-boundary RCC-44 activation coordinate used by RCC-52. -/
def newKeyActivation :
    AuthorizedActivationEvidence
      KeyAuthorityEvidence keyJointProtocol keyWriterSpec
        keyJudgmentEquivalence keyJudgmentAdapter keyWriterState
        keyTransition keyEnvelope .slotA .headA 0 .new where
  transitionBound := rfl
  active := .new rfl rfl (Nat.zero_le 0)

/-- Lawfulness is proved over the actual transition membership lists. -/
def lawfulKeyTransition :
    LawfulKeyEpochTransition keyTransition where
  oldKeyEpochQ := .epochB
  newKeyEpochQ := .epochA
  oldEpochRemoved := by simp [keyTransition]
  newEpochAdded := by simp [keyTransition]
  noAddedRemovedOverlap := by
    intro keyEpoch added removed
    simp [keyTransition] at added removed
    cases added
    cases removed
  configEpochChanges := by decide

/-- The admitted registry binds the old physical key only to epoch A. -/
def keyRegistry : RuntimeKeyEpochRegistry Token where
  Binds signer runtimeKey keyEpoch :=
    signer = .signerA ∧ runtimeKey = .keyOld ∧ keyEpoch = .epochA
  runtimeKeyBindsOneEpoch := by
    intro signer runtimeKey firstEpoch secondEpoch firstBinding secondBinding
    exact firstBinding.2.2.trans secondBinding.2.2.symm

/-- Positive RCC-52 witness over the actual durable release and transition. -/
def releasePActive :
    KeyEpochVoteCertificate
      newKeyActivation lawfulKeyTransition keyRegistry releaseP where
  activeConfigEpochBound := rfl
  signerKeyEpochBound := rfl
  slotBound := rfl
  parentHeadBound := rfl
  roundBound := rfl
  runtimeKeyEpochBound := ⟨rfl, rfl, rfl⟩

theorem positive_vote_binds_full_signed_payload :
    ActiveAt keyTransition .slotA .headA 0 .new ∧
      (releasedKeyEpochPayload releaseP).signerQ = .signerA ∧
      (releasedKeyEpochPayload releaseP).signerKeyEpochQ = .epochA ∧
      (releasedKeyEpochPayload releaseP).runtimeKeyQ = .keyOld ∧
      (releasedKeyEpochPayload releaseP).activeConfigEpochQ = .configA ∧
      (releasedKeyEpochPayload releaseP).slotQ = .slotA ∧
      (releasedKeyEpochPayload releaseP).parentHeadQ = .headA ∧
      (releasedKeyEpochPayload releaseP).round = 0 ∧
      (releasedKeyEpochPayload releaseP).judgment =
        ⟨.proposalP, .verdictAccept⟩ ∧
      keyRegistry.Binds .signerA .keyOld .epochA :=
  certificate_binds_complete_vote_payload releasePActive

theorem active_epoch_comes_from_transition_added_membership :
    Token.epochA ∈ keyTransition.membershipDelta.added :=
  new_phase_active_epoch_is_transition_added lawfulKeyTransition

/-! ## Mutant 1: one runtime key reused across two signer epochs -/

theorem reused_runtime_key_cannot_bind_both_epochs
    (registry : RuntimeKeyEpochRegistry Token)
    (oldBinding :
      registry.Binds .signerA .keyOld .epochB)
    (newBinding :
      registry.Binds .signerA .keyOld .epochA) :
    False :=
  runtime_key_reuse_across_transition_epochs_impossible
    (lawful := lawfulKeyTransition) oldBinding newBinding

/-! ## Mutant 2: a retired signer epoch replayed after activation -/

def crossEpochVote : Vote Token where
  configQ := .configA
  epochQ := .epochB
  slotQ := .slotA
  parentHeadQ := .headA
  round := 0
  proposalClassQ := .proposalP
  policyQ := .policyA
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := none

def crossEpochCommit : DurableLockCommit Token where
  lock := { vote := crossEpochVote, lockQ := .lockP }
  committedAt := 0

def crossEpochRelease :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := crossEpochCommit
  envelope := {
    signedVote := crossEpochVote
    signatureQ := crossEpochVote
  }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessOne
  runtimeSigner := rfl
  releasedAt := 1
  lockBeforeRelease := by decide

theorem cross_epoch_replay_cannot_be_admissible :
    KeyEpochVoteCertificate
        newKeyActivation lawfulKeyTransition keyRegistry crossEpochRelease →
      False := by
  intro certificate
  exact (by decide :
      Token.epochB ≠ Token.epochA) certificate.signerKeyEpochBound

/--
The same old-epoch release has a mechanically derived retirement certificate;
it is not classified from an arbitrary `ClosedOrRetired` predicate.
-/
def crossEpochRetired :
    RetiredKeyEpochCertificate
      newKeyActivation lawfulKeyTransition crossEpochRelease where
  retiredEpochBound := rfl

theorem retired_epoch_comes_from_transition_removed_membership :
    Token.epochB ∈ keyTransition.membershipDelta.removed :=
  retired_epoch_is_transition_removed crossEpochRetired

theorem retired_epoch_is_refused :
    assessKeyEpochVote
      (none :
        Option
          (KeyEpochVoteCertificate
            newKeyActivation lawfulKeyTransition keyRegistry
              crossEpochRelease))
      (some crossEpochRetired) =
        KeyEpochVoteAssessment.refuse crossEpochRetired := by
  rfl

/-! ## Mutant 3: an old-configuration vote replayed in the new phase -/

def oldConfigVote : Vote Token where
  configQ := .configB
  epochQ := .epochA
  slotQ := .slotA
  parentHeadQ := .headA
  round := 0
  proposalClassQ := .proposalP
  policyQ := .policyA
  verdict := .verdictAccept
  signerQ := .signerA
  priorVoteQ := none

def oldConfigCommit : DurableLockCommit Token where
  lock := { vote := oldConfigVote, lockQ := .lockP }
  committedAt := 0

def oldConfigRelease :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := oldConfigCommit
  envelope := {
    signedVote := oldConfigVote
    signatureQ := oldConfigVote
  }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := runtimeOldProcessOne
  runtimeSigner := rfl
  releasedAt := 1
  lockBeforeRelease := by decide

theorem old_config_vote_cannot_be_admissible_after_activation :
    KeyEpochVoteCertificate
        newKeyActivation lawfulKeyTransition keyRegistry oldConfigRelease →
      False := by
  intro certificate
  exact (by decide :
      Token.configB ≠ Token.configA) certificate.activeConfigEpochBound

theorem positive_vote_is_admissible :
    assessKeyEpochVote
      (some releasePActive)
      (none :
        Option
          (RetiredKeyEpochCertificate
            newKeyActivation lawfulKeyTransition releaseP)) =
        KeyEpochVoteAssessment.admissible releasePActive := by
  rfl

theorem missing_evidence_awaits :
    assessKeyEpochVote
      (none :
        Option
          (KeyEpochVoteCertificate
            newKeyActivation lawfulKeyTransition keyRegistry releaseP))
      (none :
        Option
          (RetiredKeyEpochCertificate
            newKeyActivation lawfulKeyTransition releaseP)) =
        (KeyEpochVoteAssessment.await :
          KeyEpochVoteAssessment
            (KeyEpochVoteCertificate
              newKeyActivation lawfulKeyTransition keyRegistry releaseP)
            (RetiredKeyEpochCertificate
              newKeyActivation lawfulKeyTransition releaseP)) := by
  rfl

end Residua.RCC.KeyEpochVote.Tests

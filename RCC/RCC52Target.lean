import RCCTests.KeyEpochVote

/-! RCC-52 candidate receipt: key-epoch payload binding and replay refusal. -/
namespace Residua.RCC.RCC52Target

open Residua.RCC.KeyEpochVote.Tests
open Residua.RCC.KeyEpochVote
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests

structure Certificate where
  positive :
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
      keyRegistry.Binds .signerA .keyOld .epochA
  transitionAdded : Token.epochA ∈ keyTransition.membershipDelta.added
  runtimeReuseRefused :
    ∀ (registry : RuntimeKeyEpochRegistry Token),
      registry.Binds .signerA .keyOld .epochB →
      registry.Binds .signerA .keyOld .epochA → False
  crossEpochRefused :
    KeyEpochVoteCertificate
        newKeyActivation lawfulKeyTransition keyRegistry crossEpochRelease →
      False
  retiredEpochRefused :
    assessKeyEpochVote
      (none :
        Option
          (KeyEpochVoteCertificate
            newKeyActivation lawfulKeyTransition keyRegistry
              crossEpochRelease))
      (some crossEpochRetired) =
        KeyEpochVoteAssessment.refuse crossEpochRetired
  oldConfigRefused :
    KeyEpochVoteCertificate
        newKeyActivation lawfulKeyTransition keyRegistry oldConfigRelease →
      False

def certificate : Certificate where
  positive := positive_vote_binds_full_signed_payload
  transitionAdded := active_epoch_comes_from_transition_added_membership
  runtimeReuseRefused := reused_runtime_key_cannot_bind_both_epochs
  crossEpochRefused := cross_epoch_replay_cannot_be_admissible
  retiredEpochRefused := retired_epoch_is_refused
  oldConfigRefused := old_config_vote_cannot_be_admissible_after_activation

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
end Residua.RCC.RCC52Target

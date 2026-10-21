import RCCTests.LongRangeSafety

/-! RCC-54 candidate receipt: long-range authority remains history-bound. -/
namespace Residua.RCC.RCC54Target
open Residua.RCC.LongRangeSafety.Tests
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.HistoricalInclusion
open Residua.RCC.KeyEpochVote
open Residua.RCC.LongRangeSafety

structure Certificate where
  positive :
    Nonempty
        (KeyEpochVoteCertificate
          Residua.RCC.KeyEpochVote.Tests.newKeyActivation
          Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition
          Residua.RCC.KeyEpochVote.Tests.keyRegistry
          Residua.RCC.DurableVoteLock.Tests.releaseP) ∧
      Nonempty
          (FinalizedHistoricalInclusion
            Residua.RCC.HistoricalInclusion.Tests.checkpointProtocol
            Residua.RCC.HistoricalInclusion.Tests.HistoricalVoteEvidence
            Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint
            Token.epochA Token.proposalP) ∧
        Residua.RCC.HistoricalInclusion.Tests.checkpointProtocol.InCheckpoint
          Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint.checkpointQ
          .epochA .proposalP
  incompatibleItemRefused :
    exactVoteSignatureScheme.Accepts
        distinctRetiredRelease.envelope.signatureQ
        (exactVoteSignatureScheme.canonicalVoteMessage
          distinctRetiredRelease.envelope.signedVote) ∧
      assessRetiredClaim authorityAdapter
        Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
        distinctRetiredRelease.runtime.keyQ
        canonicalClaim incompatibleClaim
        (releasedKeyEpochPayload distinctRetiredRelease).judgment
        distinctIncompatibleAttempt =
          RetiredClaimAssessment.refuse
            distinctIncompatibleAttempt .checkpointItemMismatch
  staleForkRefused :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      distinctRetiredRelease.runtime.keyQ
      canonicalClaim staleForkClaim
      (releasedKeyEpochPayload distinctRetiredRelease).judgment
      distinctStaleAttempt =
        RetiredClaimAssessment.refuse
          distinctStaleAttempt .staleCheckpointOrFork
  retiredKeyRefused :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      Residua.RCC.KeyEpochVote.Tests.crossEpochRelease.runtime.keyQ
      canonicalClaim exactRetiredClaim
      (releasedKeyEpochPayload
        Residua.RCC.KeyEpochVote.Tests.crossEpochRelease).judgment
      reusedKeyAttempt =
        RetiredClaimAssessment.refuse
          reusedKeyAttempt .retiredKeyReusedAsActive
  missingAuthorityAwaits :
    assessLongRangeAuthority
      (none : Option HistoricalAuthorityCertificate) =
        (LongRangeAuthorityAssessment.await
          .activeAuthorityEvidencePending :
          LongRangeAuthorityAssessment HistoricalAuthorityCertificate)
  actualAuthorityCanonical :
    assessLongRangeAuthority (some historicalAuthority) =
      LongRangeAuthorityAssessment.authority historicalAuthority
  compromiseNotAuthority :
    exactVoteSignatureScheme.Accepts
      distinctRetiredRelease.envelope.signatureQ
      (exactVoteSignatureScheme.canonicalVoteMessage
        distinctRetiredRelease.envelope.signedVote)
  retiredBytesRefused :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      distinctRetiredRelease.runtime.keyQ
      canonicalClaim canonicalClaim
      (releasedKeyEpochPayload distinctRetiredRelease).judgment
      distinctExactAttempt =
        RetiredClaimAssessment.refuse
          distinctExactAttempt
          .retiredSignatureHasNoHistoryAuthority
  retiredReleaseRefused :
    ∀ (active :
      KeyEpochVoteCertificate
        Residua.RCC.KeyEpochVote.Tests.newKeyActivation
        Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition
        Residua.RCC.KeyEpochVote.Tests.keyRegistry
        distinctRetiredRelease),
      False

def certificate : Certificate where
  positive := accepted_history_consumes_actual_rcc52_and_rcc53
  incompatibleItemRefused := valid_old_key_bytes_on_incompatible_item_are_refused
  staleForkRefused := stale_checkpoint_or_fork_is_refused
  retiredKeyRefused := retired_key_reused_as_active_is_refused
  missingAuthorityAwaits := missing_historical_authority_only_awaits
  actualAuthorityCanonical := actual_authority_remains_canonical
  compromiseNotAuthority := later_compromise_bytes_remain_cryptographically_valid
  retiredBytesRefused := retired_bytes_never_gain_canonical_history_authority
  retiredReleaseRefused := retired_release_cannot_become_active

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
end Residua.RCC.RCC54Target

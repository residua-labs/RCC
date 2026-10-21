import RCCTests.MobileAdversarySafety

/-! RCC-55 candidate receipt: mobile-adversary coverage and refresh safety. -/
namespace Residua.RCC.RCC55Target
open Residua.RCC.MobileAdversarySafety.Tests
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.KeyEpochVote
open Residua.RCC.KeyEpochVote.Tests
open Residua.RCC.MobileAdversarySafety
open Residua.RCC.TemporalAuthenticity
open Residua.RCC.TemporalAuthenticity.Tests

structure Certificate where
  positive :
    ActiveAt keyTransition .slotA .headA 0 .new ∧
      (releasedKeyEpochPayload releaseP).signerKeyEpochQ = .epochA ∧
      (releasedKeyEpochPayload releaseP).activeConfigEpochQ = .configA ∧
      mobileCheckpointProtocol.Includes
        mobileInclusion.receipt mobileCheckpoint.checkpointQ
          mobileInclusion.coordinate mobileInclusion.item
          finalizedClosure.snapshot.slot finalizedClosure.snapshot.head
          finalizedClosure.snapshot.config
          finalizedClosure.snapshot.sourceAuthority
          finalizedClosure.snapshot.watermark
          finalizedClosure.snapshot.priorPartitions ∧
      mobileTemporalSafety.checkpointCadence <
        mobileTemporalSafety.corruptionHorizon ∧
      mobileRefreshObserved
        mobileTemporalSafety.refreshReceipt .processOne .slotA
          .epochB .epochA mobileTemporalSafety.refreshCadence ∧
      mobileErasureObserved
        mobileTemporalSafety.erasureReceipt .processOne .slotA
          .epochB .epochA ∧
      ∀ interval,
        RequiredCorruptionInterval interval →
        ∃ receipt,
          exposureObserved
            receipt .processOne .slotA .epochA .configA
              mobileTemporalSafety.corruptionHorizon interval
  incompleteAwaits :
    ∀ (residue : MobileAdversarySafetyResidue),
      assessMobileAdversarySafety
          (MobileAdversaryEvidence.incomplete
            (Safety :=
              MobileAdversarySafetyCertificate
                (AuthorityEvidence := KeyAuthorityEvidence)
                (jointProtocol := keyJointProtocol)
                (spec := keyWriterSpec)
                (equivalence := keyJudgmentEquivalence)
                (adapter := keyJudgmentAdapter)
                (state := keyWriterState)
                (transition := keyTransition)
                (envelope := keyEnvelope)
                (slot := Token.slotA)
                (head := Token.headA)
                (round := 0)
                (activation := newKeyActivation)
                (lawful := lawfulKeyTransition)
                (registry := keyRegistry)
                (scheme := exactVoteSignatureScheme)
                (release := releaseP)
                (FinalityAuthorityEvidence := AuthorityEvidence)
                (logicalTimeProtocol := mobileLogicalTimeProtocol)
                (checkpointProtocol := mobileCheckpointProtocol)
                (environment := admissionEnvironment)
                (history := finalizedHistory)
                (ConfigLawful := configLawful)
                (sourceProtocol := sourceProtocol)
                (ConfigStable := configStable)
                (closure := finalizedClosure)
                (checkpoint := mobileCheckpoint)
                (checkpointEpoch := Token.epochB)
                (item := HistoricalItem.anchored)
                (inclusion := mobileInclusion)
                (context := Token.processOne)
                (unit := Token.slotA)
                RequiredCorruptionInterval exposureProtocol)
            residue) =
        MobileAdversaryAssessment.await residue
  intervalOmissionRefused :
    ¬ Nonempty
      (CorruptionUniverseSeal
        RequiredCorruptionInterval omittedCorruptionIntervals)
  noErasureRefused :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        noErasureLogicalTimeProtocol mobileInclusion
          .epochB .epochA .processOne .slotA)
  slowCheckpointRefused :
    ∀ (certificate :
      MobileAdversarySafetyCertificate
        (AuthorityEvidence := KeyAuthorityEvidence)
        (jointProtocol := keyJointProtocol)
        (spec := keyWriterSpec)
        (equivalence := keyJudgmentEquivalence)
        (adapter := keyJudgmentAdapter)
        (state := keyWriterState)
        (transition := keyTransition)
        (envelope := keyEnvelope)
        (slot := Token.slotA)
        (head := Token.headA)
        (round := 0)
        (activation := newKeyActivation)
        (lawful := lawfulKeyTransition)
        (registry := keyRegistry)
        (scheme := exactVoteSignatureScheme)
        (release := releaseP)
        (FinalityAuthorityEvidence := AuthorityEvidence)
        (logicalTimeProtocol := mobileLogicalTimeProtocol)
        (checkpointProtocol := mobileCheckpointProtocol)
        (environment := admissionEnvironment)
        (history := finalizedHistory)
        (ConfigLawful := configLawful)
        (sourceProtocol := sourceProtocol)
        (ConfigStable := configStable)
        (closure := finalizedClosure)
        (checkpoint := mobileCheckpoint)
        (checkpointEpoch := Token.epochB)
        (item := HistoricalItem.anchored)
        (inclusion := mobileInclusion)
        (context := Token.processOne)
        (unit := Token.slotA)
        RequiredCorruptionInterval exposureProtocol)
      (slow :
        certificate.temporalSafety.corruptionHorizon ≤
          certificate.temporalSafety.checkpointCadence),
      False
  partitionExposureRefused :
    ¬ Nonempty
      (CompleteExposureEvidence
        partitionLocalExposureProtocol RequiredCorruptionInterval
          allCorruptionIntervals corruptionUniverseSeal
          .processOne .slotA .epochA .configA 10)

def certificate : Certificate where
  positive := complete_mobile_adversary_certificate_is_safe
  incompleteAwaits := every_incomplete_envelope_awaits
  intervalOmissionRefused := omitted_corruption_interval_cannot_seal_universe
  noErasureRefused := refresh_without_old_key_erasure_cannot_be_safe
  slowCheckpointRefused := checkpoint_slower_than_corruption_horizon_is_unsafe
  partitionExposureRefused := partition_local_evidence_cannot_cover_global_universe

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
end Residua.RCC.RCC55Target

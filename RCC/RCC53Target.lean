import RCCTests.HistoricalInclusion

/-! RCC-53 candidate receipt: historical inclusion and sealed-source coverage. -/
namespace Residua.RCC.RCC53Target
open Residua.RCC.HistoricalInclusion.Tests
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.HistoricalInclusion
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.KeyEpochVote
open Residua.RCC.KeyEpochVote.Tests

structure Certificate where
  positive :
    Nonempty
      (FinalizedClosureEvidence
        (environment := admissionEnvironment)
        (history := finalizedHistory)
        (ConfigLawful := configLawful)
        (protocol := sourceProtocol)
        (ConfigStable := configStable))
  semanticMember :
    checkpointProtocol.InCheckpoint
      sealedCheckpoint.checkpointQ .epochA .proposalP
  partitionCoverage :
    CoverageCertificate
      sourceProtocol.InUniverse finalizedClosure.snapshot.priorPartitions
  authentic :
    assessHistoricalInclusion (some releasePInclusion) =
      HistoricalInclusionAssessment.authentic releasePInclusion
  localNonfinalRefused :
    localGreenOnly.localGreen = true ∧
      assessHistoricalInclusion
        (none :
          Option
            (FinalizedHistoricalInclusion
              checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
                .epochA .proposalP)) =
        (HistoricalInclusionAssessment.await :
          HistoricalInclusionAssessment
            (FinalizedHistoricalInclusion
              checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
                .epochA .proposalP))
  emptyScanRefused :
    ¬ Nonempty
      (CoverageCertificate
        (fun entry =>
          checkpointProtocol.InCheckpoint
            Token.lockP entry.coordinate entry.item)
        ([] : List (CheckpointEntry Token Token)))
  shortScanRefused :
    ¬ Nonempty
      (CoverageCertificate
        (fun entry =>
          checkpointProtocol.InCheckpoint
            Token.lockP entry.coordinate entry.item)
        [firstEntry])
  missingInclusionAwaits :
    assessHistoricalInclusion
      (none :
        Option
          (FinalizedHistoricalInclusion
            checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
              .epochA .proposalP)) =
      (HistoricalInclusionAssessment.await :
        HistoricalInclusionAssessment
          (FinalizedHistoricalInclusion
            checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
              .epochA .proposalP))
  staleHeadRefused :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleHeadCoordinate)
  staleConfigRefused :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleConfigCoordinate)
  staleWatermarkRefused :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleWatermarkCoordinate)
  partitionOmissionRefused :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure omittedPartitionCoordinate)
  coordinateConflictRefused :
    ∀ (first :
      FinalizedHistoricalInclusion
        checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
          .epochA .proposalP)
      (second :
      FinalizedHistoricalInclusion
        checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
          .epochA .proposalQ),
      False

def certificate : Certificate where
  positive := positive_inclusion_consumes_actual_rcc45
  semanticMember := positive_inclusion_is_checkpoint_semantic_member
  partitionCoverage := checkpoint_retains_complete_source_partitions
  authentic := positive_inclusion_is_authentic
  localNonfinalRefused := local_nonfinal_checkpoint_cannot_create_inclusion
  emptyScanRefused := empty_checkpoint_scan_is_not_complete
  shortScanRefused := checkpoint_scan_omitting_second_entry_is_not_complete
  missingInclusionAwaits := absent_inclusion_only_awaits
  staleHeadRefused := stale_head_cannot_seal_checkpoint
  staleConfigRefused := stale_config_cannot_seal_checkpoint
  staleWatermarkRefused := stale_watermark_cannot_seal_checkpoint
  partitionOmissionRefused := omitted_partition_cannot_seal_checkpoint
  coordinateConflictRefused := same_coordinate_incompatible_items_cannot_both_be_included

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
end Residua.RCC.RCC53Target

import RCC.HistoricalInclusion
import RCCTests.FinalizedHeadWindow
import RCCTests.KeyEpochVote

/-!
# RCC-53 Historical Inclusion Countermodels

The positive fixture binds an RCC-52 admissible key-epoch vote into an actual
RCC-45 finalized checkpoint.  The checkpoint carries an exact two-entry
coordinate/item universe and inherits the complete two-partition RCC-45 source
window.

Mutants cover local/nonfinal evidence, empty or shortened checkpoint scans,
omitted source partitions, stale head/config/watermark, and incompatible items
at one historical coordinate.
-/

namespace Residua.RCC.HistoricalInclusion.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.HistoricalInclusion
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.KeyEpochVote
open Residua.RCC.KeyEpochVote.Tests

/-- The actual RCC-45 closure consumed by the historical checkpoint. -/
def finalizedClosure :
    FinalizedClosureEvidence
      (environment := admissionEnvironment)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      (protocol := sourceProtocol)
      (ConfigStable := configStable) where
  snapshot := currentSnapshot
  finalizedHead := headEnvelope
  finalizedWindow := fullSealEnvelope
  slotMatches := rfl
  parentMatches := rfl
  headMatches := rfl
  headConfigMatches := rfl
  windowHeadMatches := rfl
  windowConfigMatches := rfl
  sourceAuthorityMatches := rfl
  watermarkMatches := rfl
  partitionsMatch := rfl
  stableConfig := stableConfigEvidence

abbrev CheckpointCoordinate :=
  FinalizedCheckpointCoordinate
    Slot Head Config SourceAuthority Watermark Partition

def currentCheckpointCoordinate : CheckpointCoordinate :=
  finalizedCheckpointCoordinate finalizedClosure

def firstEntry : CheckpointEntry Token Token :=
  ⟨.epochA, .proposalP⟩

def secondEntry : CheckpointEntry Token Token :=
  ⟨.epochB, .proposalQ⟩

def fullCheckpointEntries : List (CheckpointEntry Token Token) :=
  [firstEntry, secondEntry]

/-- Exact semantic checkpoint membership for the two sealed entries. -/
def checkpointMember
    (checkpointQ coordinate item : Token) : Prop :=
  checkpointQ = .lockP ∧
    ((coordinate = .epochA ∧ item = .proposalP) ∨
      (coordinate = .epochB ∧ item = .proposalQ))

/--
The seal binds checkpoint identity, actual RCC-45 metadata, and the complete
finite entry enumeration.
-/
def checkpointSeal
    (receipt checkpointQ : Token)
    (coordinate : CheckpointCoordinate)
    (entries : List (CheckpointEntry Token Token)) : Prop :=
  receipt = .signatureP ∧
    checkpointQ = .lockP ∧
    coordinate = currentCheckpointCoordinate ∧
    entries = fullCheckpointEntries

def checkpointProtocol :
    CheckpointInclusionProtocol
      Token Token Token Slot Head Config SourceAuthority Watermark Partition where
  SealReceipt := Token
  InCheckpoint := checkpointMember
  Seals := checkpointSeal
  sameCoordinateUnique := by
    intro checkpointQ coordinate firstItem secondItem firstIncluded
      secondIncluded
    rcases firstIncluded.2 with first | first
    · rcases secondIncluded.2 with second | second
      · exact first.2.trans second.2.symm
      · have impossible : Token.epochA = Token.epochB :=
          first.1.symm.trans second.1
        exact False.elim ((by decide : Token.epochA ≠ Token.epochB) impossible)
    · rcases secondIncluded.2 with second | second
      · have impossible : Token.epochB = Token.epochA :=
          first.1.symm.trans second.1
        exact False.elim ((by decide : Token.epochB ≠ Token.epochA) impossible)
      · exact first.2.trans second.2.symm

/-- Sound and complete coverage of both semantic checkpoint entries. -/
def fullCheckpointCoverage :
    CoverageCertificate
      (fun entry =>
        checkpointProtocol.InCheckpoint
          Token.lockP entry.coordinate entry.item)
      fullCheckpointEntries where
  sound := by
    intro entry member
    simp only [fullCheckpointEntries, List.mem_cons] at member
    rcases member with first | second | impossible
    · cases first
      exact ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
    · cases second
      exact ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
    · cases impossible
  complete := by
    intro entry inCheckpoint
    rcases entry with ⟨coordinate, item⟩
    rcases inCheckpoint.2 with first | second
    · apply List.mem_cons.mpr
      left
      cases first.1
      cases first.2
      rfl
    · apply List.mem_cons.mpr
      right
      apply List.mem_singleton.mpr
      cases second.1
      cases second.2
      rfl

def sealedCheckpoint :
    SealedHistoricalCheckpoint
      checkpointProtocol finalizedClosure currentCheckpointCoordinate where
  checkpointQ := .lockP
  coordinateBound := rfl
  entries := fullCheckpointEntries
  sealReceipt := .signatureP
  sealed := ⟨rfl, rfl, rfl, rfl⟩
  coverage := fullCheckpointCoverage

/-- RCC-52 evidence for the item named by proposal-class identity. -/
abbrev HistoricalVoteEvidence (itemQ : Token) :=
  KeyEpochVoteItemEvidence
    (activation := newKeyActivation)
    (lawful := lawfulKeyTransition)
    (registry := keyRegistry)
    releaseP itemQ

def releasePItemEvidence :
    HistoricalVoteEvidence .proposalP where
  admissible := releasePActive
  itemBindsJudgment := rfl

def releasePInclusion :
    FinalizedHistoricalInclusion
      checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
        .epochA .proposalP where
  itemEvidence := releasePItemEvidence
  included := by
    apply List.mem_cons.mpr
    exact Or.inl rfl

theorem positive_inclusion_consumes_actual_rcc45 :
    Nonempty
      (FinalizedClosureEvidence
        (environment := admissionEnvironment)
        (history := finalizedHistory)
        (ConfigLawful := configLawful)
        (protocol := sourceProtocol)
        (ConfigStable := configStable)) :=
  sealed_checkpoint_consumes_actual_rcc45 sealedCheckpoint

theorem positive_inclusion_is_checkpoint_semantic_member :
    checkpointProtocol.InCheckpoint
      sealedCheckpoint.checkpointQ .epochA .proposalP :=
  finalized_historical_inclusion_sound releasePInclusion

theorem checkpoint_retains_complete_source_partitions :
    CoverageCertificate
      sourceProtocol.InUniverse finalizedClosure.snapshot.priorPartitions :=
  sealed_checkpoint_retains_source_partition_coverage sealedCheckpoint

theorem positive_inclusion_is_authentic :
    assessHistoricalInclusion (some releasePInclusion) =
      HistoricalInclusionAssessment.authentic releasePInclusion := by
  rfl

/-! ## Mutant 1: partition-local/nonfinal evidence -/

structure LocalCheckpointClaim where
  localHead : Head
  localConfig : Config
  localGreen : Bool

def localGreenOnly : LocalCheckpointClaim :=
  ⟨.headA, .v1, true⟩

theorem local_nonfinal_checkpoint_cannot_create_inclusion :
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
                .epochA .proposalP)) := by
  exact ⟨rfl, rfl⟩

/-! ## Mutant 2: empty or under-quotiented checkpoint universe -/

theorem empty_checkpoint_scan_is_not_complete :
    ¬ Nonempty
      (CoverageCertificate
        (fun entry =>
          checkpointProtocol.InCheckpoint
            Token.lockP entry.coordinate entry.item)
        ([] : List (CheckpointEntry Token Token))) := by
  rintro ⟨coverage⟩
  have firstCovered :=
    coverage.complete firstEntry
      ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
  cases firstCovered

theorem checkpoint_scan_omitting_second_entry_is_not_complete :
    ¬ Nonempty
      (CoverageCertificate
        (fun entry =>
          checkpointProtocol.InCheckpoint
            Token.lockP entry.coordinate entry.item)
        [firstEntry]) := by
  rintro ⟨coverage⟩
  have secondCovered :=
    coverage.complete secondEntry
      ⟨rfl, Or.inr ⟨rfl, rfl⟩⟩
  simp [firstEntry, secondEntry] at secondCovered

/-- Empty scan means Await, never an exclusion judgment. -/
theorem absent_inclusion_only_awaits :
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
              .epochA .proposalP)) := by
  rfl

/-! ## Mutant 3: stale RCC-45 checkpoint metadata -/

def staleHeadCoordinate : CheckpointCoordinate :=
  { currentCheckpointCoordinate with head := .headB }

def staleConfigCoordinate : CheckpointCoordinate :=
  { currentCheckpointCoordinate with config := .v2 }

def staleWatermarkCoordinate : CheckpointCoordinate :=
  { currentCheckpointCoordinate with watermark := .eleven }

def omittedPartitionCoordinate : CheckpointCoordinate :=
  { currentCheckpointCoordinate with priorPartitions := [.zero] }

theorem stale_head_cannot_seal_checkpoint :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleHeadCoordinate) := by
  rintro ⟨checkpoint⟩
  have sameHead :=
    congrArg FinalizedCheckpointCoordinate.head checkpoint.coordinateBound
  exact (by decide : Head.headB ≠ Head.headA) sameHead

theorem stale_config_cannot_seal_checkpoint :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleConfigCoordinate) := by
  rintro ⟨checkpoint⟩
  have sameConfig :=
    congrArg FinalizedCheckpointCoordinate.config checkpoint.coordinateBound
  exact (by decide : Config.v2 ≠ Config.v1) sameConfig

theorem stale_watermark_cannot_seal_checkpoint :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure staleWatermarkCoordinate) := by
  rintro ⟨checkpoint⟩
  have sameWatermark :=
    congrArg FinalizedCheckpointCoordinate.watermark checkpoint.coordinateBound
  exact (by decide : Watermark.eleven ≠ Watermark.ten) sameWatermark

theorem omitted_partition_cannot_seal_checkpoint :
    ¬ Nonempty
      (SealedHistoricalCheckpoint
        checkpointProtocol finalizedClosure omittedPartitionCoordinate) := by
  rintro ⟨checkpoint⟩
  have samePartitions :=
    congrArg
      FinalizedCheckpointCoordinate.priorPartitions checkpoint.coordinateBound
  exact
    (by decide :
      ([Partition.zero] : List Partition) ≠ [.zero, .one]) samePartitions

/-! ## Mutant 4: incompatible item at one coordinate -/

theorem same_coordinate_incompatible_items_cannot_both_be_included
    (first :
      FinalizedHistoricalInclusion
        checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
          .epochA .proposalP)
    (second :
      FinalizedHistoricalInclusion
        checkpointProtocol HistoricalVoteEvidence sealedCheckpoint
          .epochA .proposalQ) :
    False :=
  (by decide : Token.proposalP ≠ Token.proposalQ)
    (same_finalized_coordinate_inclusion_unique first second)

end Residua.RCC.HistoricalInclusion.Tests

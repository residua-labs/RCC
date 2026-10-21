import RCC.FinalizedHeadWindow
import RCC.KeyEpochVote

/-!
# RCC-53 Historical Inclusion

Historical authenticity is a positive inclusion claim over an actual RCC-45
finalized closure.  The checkpoint metadata and finite coordinate/item
universe are sealed together; sound-and-complete coverage prevents empty or
short caller enumerations from proving inclusion or absence.

Absence has no terminal constructor in this kernel.  Without a positive
membership witness the executable gate can only await more evidence.  A
negative historical conclusion requires a separate, independently specified
certificate language and is deliberately outside RCC-53.

Prelude-only Lean 4.14; no Mathlib, axioms, or proof placeholders.
-/

namespace Residua.RCC.HistoricalInclusion

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.KeyEpochVote

universe u

/-- The complete checkpoint coordinate inherited from an RCC-45 snapshot. -/
structure FinalizedCheckpointCoordinate
    (Slot Head Config SourceAuthority Watermark Partition : Type u) where
  slot : Slot
  head : Head
  config : Config
  sourceAuthority : SourceAuthority
  watermark : Watermark
  priorPartitions : List Partition
  deriving DecidableEq, Repr

/-- Mechanically project the exact metadata of an actual RCC-45 closure. -/
def finalizedCheckpointCoordinate
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)) :
    FinalizedCheckpointCoordinate
      Slot Head Config SourceAuthority Watermark Partition where
  slot := closure.snapshot.slot
  head := closure.snapshot.head
  config := closure.snapshot.config
  sourceAuthority := closure.snapshot.sourceAuthority
  watermark := closure.snapshot.watermark
  priorPartitions := closure.snapshot.priorPartitions

/-- One member of the finite historical coordinate/item universe. -/
structure CheckpointEntry (Coordinate Item : Type u) where
  coordinate : Coordinate
  item : Item
  deriving DecidableEq, Repr

/--
Authority protocol for a checkpoint's finite historical contents.

`InCheckpoint` is the semantic membership relation.  A seal binds the exact
RCC-45 metadata and finite enumeration.  `sameCoordinateUnique` is a protocol
law over semantic membership, not a q-based first-write-wins convention.
-/
structure CheckpointInclusionProtocol
    (CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition : Type u) where
  SealReceipt : Type u
  InCheckpoint : CheckpointQ → Coordinate → Item → Prop
  Seals :
    SealReceipt →
      CheckpointQ →
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition →
      List (CheckpointEntry Coordinate Item) →
      Prop
  sameCoordinateUnique :
    ∀ {checkpointQ coordinate firstItem secondItem},
      InCheckpoint checkpointQ coordinate firstItem →
      InCheckpoint checkpointQ coordinate secondItem →
      firstItem = secondItem

/--
A sealed historical checkpoint is indexed by the exact RCC-45 closure and the
metadata it claims.  `coordinateBound` rejects stale head/config/watermark and
partition omission.  Coverage seals the complete finite coordinate/item
universe and prevents vacuous scans.
-/
structure SealedHistoricalCheckpoint
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition)
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable))
    (claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition) where
  checkpointQ : CheckpointQ
  coordinateBound :
    claimedCoordinate = finalizedCheckpointCoordinate closure
  entries : List (CheckpointEntry Coordinate Item)
  sealReceipt : checkpointProtocol.SealReceipt
  sealed :
    checkpointProtocol.Seals
      sealReceipt checkpointQ claimedCoordinate entries
  coverage :
    CoverageCertificate
      (fun entry =>
        checkpointProtocol.InCheckpoint
          checkpointQ entry.coordinate entry.item)
      entries

/-- Every sealed checkpoint consumes the actual RCC-45 closure in its type. -/
theorem sealed_checkpoint_consumes_actual_rcc45
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    {claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition}
    (_checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate) :
    Nonempty
      (FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)) :=
  ⟨closure⟩

/--
The historical checkpoint retains RCC-45's complete authority-declared source
partition coverage.  It cannot substitute a shorter checkpoint-local list.
-/
theorem sealed_checkpoint_retains_source_partition_coverage
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    {claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition}
    (_checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate) :
    CoverageCertificate
      sourceProtocol.InUniverse closure.snapshot.priorPartitions := by
  rw [← closure.partitionsMatch]
  exact closure.finalizedWindow.windowSeal.coverage

/--
Bridge from RCC-52 to an RCC-53 historical item.  The item identity is the
canonical proposal-class coordinate of an actual admissible key-epoch vote.
-/
structure KeyEpochVoteItemEvidence
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat} {phase : AuthorityPhase}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round phase}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme)
    (itemQ : Q) : Type u where
  admissible :
    KeyEpochVoteCertificate activation lawful registry release
  itemBindsJudgment :
    itemQ =
      (releasedKeyEpochPayload release).judgment.proposalClassQ

/--
Positive historical inclusion.  The item carries independent authenticity
evidence and must occur in the sealed, coverage-complete checkpoint universe.
-/
structure FinalizedHistoricalInclusion
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition)
    (ItemEvidence : Item → Type u)
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    {claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition}
    (checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate)
    (coordinate : Coordinate)
    (item : Item) : Type u where
  itemEvidence : ItemEvidence item
  included :
    CheckpointEntry.mk coordinate item ∈ checkpoint.entries

/-- Inclusion in the finite enumeration implies semantic checkpoint membership. -/
theorem finalized_historical_inclusion_sound
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition}
    {ItemEvidence : Item → Type u}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    {claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition}
    {checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate}
    {coordinate : Coordinate} {item : Item}
    (inclusion :
      FinalizedHistoricalInclusion
        checkpointProtocol ItemEvidence checkpoint coordinate item) :
    checkpointProtocol.InCheckpoint checkpoint.checkpointQ coordinate item :=
  checkpoint.coverage.sound
    (CheckpointEntry.mk coordinate item) inclusion.included

/-- Same finalized checkpoint coordinate has one semantic historical item. -/
theorem same_finalized_coordinate_inclusion_unique
    {CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition}
    {ItemEvidence : Item → Type u}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    {claimedCoordinate :
      FinalizedCheckpointCoordinate
        Slot Head Config SourceAuthority Watermark Partition}
    {checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate}
    {coordinate : Coordinate} {firstItem secondItem : Item}
    (first :
      FinalizedHistoricalInclusion
        checkpointProtocol ItemEvidence checkpoint coordinate firstItem)
    (second :
      FinalizedHistoricalInclusion
        checkpointProtocol ItemEvidence checkpoint coordinate secondItem) :
    firstItem = secondItem :=
  checkpointProtocol.sameCoordinateUnique
    (finalized_historical_inclusion_sound first)
    (finalized_historical_inclusion_sound second)

/-- RCC-53 has only positive inclusion or honest waiting. -/
inductive HistoricalInclusionAssessment (Inclusion : Type u)
  | authentic :
      Inclusion → HistoricalInclusionAssessment Inclusion
  | await :
      HistoricalInclusionAssessment Inclusion

/-- Absence of a positive inclusion certificate is `Await`, never exclusion. -/
def assessHistoricalInclusion
    {Inclusion : Type u}
    (inclusion? : Option Inclusion) :
    HistoricalInclusionAssessment Inclusion :=
  match inclusion? with
  | some inclusion => .authentic inclusion
  | none => .await

end Residua.RCC.HistoricalInclusion

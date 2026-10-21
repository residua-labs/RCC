import RCC.AuthorityReconfiguration
import RCC.DurableVoteLock
import RCC.FinalizedHeadWindow

/-!
# RCC-52..RCC-55 Temporal Authenticity

This safety kernel binds key-epoch votes to actual RCC-41 releases and RCC-44
activation evidence, historical items to actual RCC-45 finalized closure
evidence, long-range authority to those finalized inclusions, and
mobile-adversary safety to one complete logical-time evidence envelope.

Cryptographic verification, physical secure erasure, wall-clock fidelity,
storage truth, refresh execution, adversary corruption rate, and forward
security remain fixed-protocol adapter obligations.  Natural-number cadence
relations are interpreted only inside one admitted logical-time context.

Prelude-only Lean 4.14; no Mathlib and no proof placeholders.
-/

namespace Residua.RCC.TemporalAuthenticity

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.FinalizedHeadWindow

universe u v

/-- Named RCC-52..55 Await/refusal classes. -/
inductive TemporalAuthenticityResidue
  | keyEpochEvidencePending
  | lateVoteForClosedKeyEpoch
  | historicalInclusionEvidencePending
  | historicalInclusionEvidenceConflict
  | historicalSignatureUnanchored
  | longRangeHistoryForgery
  | mobileAdversaryBudgetUnmodeled
  deriving DecidableEq, Repr

/-! ## RCC-52: key-epoch vote admissibility -/

/-- Configuration selected by one proof-carrying RCC-44 authority phase. -/
def phaseConfig
    {Config Slot Head Authority Member : Type u}
    (transition :
      AuthorityTransition Config Slot Head Authority Member) :
    AuthorityPhase → Config
  | .old => transition.oldConfig
  | .new => transition.newConfig

/--
The deployment binds a physical runtime key and logical signer epoch to the
complete released vote.  Active and closed evidence use different receipts;
absence of one never constructs the other.
-/
structure KeyEpochProtocol (Q : Type u) where
  ActiveReceipt : Type u
  ClosedReceipt : Type u
  Active :
    ActiveReceipt → Q → Q → Q → Q → Vote Q → Prop
  ClosedOrRetired :
    ClosedReceipt → Q → Q → Q → Prop
  activeClosedDisjoint :
    ∀ {activeReceipt closedReceipt signer runtimeKey keyEpoch config vote},
      Active
          activeReceipt signer runtimeKey keyEpoch config vote →
        ClosedOrRetired
          closedReceipt signer runtimeKey keyEpoch →
        False

/--
An admissible vote contains both the actual RCC-41 release and the exact
fixed-domain RCC-44 activation evidence.
-/
structure KeyEpochVoteCertificate
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    (keyProtocol : KeyEpochProtocol Q)
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
    (activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round phase)
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) where
  configBound :
    (releasedVote release).configQ = phaseConfig transition phase
  slotBound : (releasedVote release).slotQ = slot
  parentHeadBound : (releasedVote release).parentHeadQ = head
  roundBound : (releasedVote release).round = round
  activeReceipt : keyProtocol.ActiveReceipt
  active :
    keyProtocol.Active
      activeReceipt
      (releasedVote release).signerQ
      release.runtime.keyQ
      (releasedVote release).epochQ
      (phaseConfig transition phase)
      (releasedVote release)

/--
Negative RCC-52 evidence is certified either by an activation/config mismatch
or by a fixed-protocol closed/retired epoch receipt.
-/
inductive ClosedOrRetiredKeyEpochCertificate
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    (keyProtocol : KeyEpochProtocol Q)
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
    (activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round phase)
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) : Type u
  | configurationMismatch :
      (releasedVote release).configQ ≠ phaseConfig transition phase →
      ClosedOrRetiredKeyEpochCertificate keyProtocol activation release
  | closedOrRetired :
      (receipt : keyProtocol.ClosedReceipt) →
      keyProtocol.ClosedOrRetired
        receipt
        (releasedVote release).signerQ
        release.runtime.keyQ
        (releasedVote release).epochQ →
      ClosedOrRetiredKeyEpochCertificate keyProtocol activation release

/-- RCC-52 result: missing is Await; Refuse retains certified negative data. -/
inductive KeyEpochVoteAssessment
    (Admissible Closed : Type u)
  | admissible :
      Admissible → KeyEpochVoteAssessment Admissible Closed
  | await :
      TemporalAuthenticityResidue →
      KeyEpochVoteAssessment Admissible Closed
  | refuse :
      Closed → TemporalAuthenticityResidue →
      KeyEpochVoteAssessment Admissible Closed

/-- Preserve the evidence polarity at the RCC-52 gate. -/
def assessKeyEpochVote
    {Admissible Closed : Type u}
    (admissible? : Option Admissible)
    (closed? : Option Closed) :
    KeyEpochVoteAssessment Admissible Closed :=
  match admissible?, closed? with
  | some _, some certificate =>
      .refuse certificate .lateVoteForClosedKeyEpoch
  | some certificate, none => .admissible certificate
  | none, some certificate =>
      .refuse certificate .lateVoteForClosedKeyEpoch
  | none, none => .await .keyEpochEvidencePending

/--
Positive RCC-52 evidence and a closed/retired certificate for the same actual
release cannot coexist.  Configuration mismatch is contradicted by the
positive binding; explicit closure is contradicted by the fixed protocol law.
-/
theorem key_epoch_active_and_closed_certificates_conflict
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    {keyProtocol : KeyEpochProtocol Q}
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
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    (active :
      KeyEpochVoteCertificate keyProtocol activation release)
    (closed :
      ClosedOrRetiredKeyEpochCertificate
        keyProtocol activation release) :
    False := by
  cases active with
  | mk configBound _ _ _ activeReceipt activeEvidence =>
      cases closed with
      | configurationMismatch mismatch =>
          exact mismatch configBound
      | closedOrRetired closedReceipt closedEvidence =>
          exact
            keyProtocol.activeClosedDisjoint
              activeEvidence closedEvidence

/-- An RCC-52 certificate exposes every active configuration/key binding. -/
theorem key_epoch_vote_certificate_binds_active_epochs
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    {keyProtocol : KeyEpochProtocol Q}
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
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    (certificate :
      KeyEpochVoteCertificate keyProtocol activation release) :
    ActiveAt transition slot head round phase ∧
      (releasedVote release).configQ = phaseConfig transition phase ∧
      (releasedVote release).slotQ = slot ∧
      (releasedVote release).parentHeadQ = head ∧
      (releasedVote release).round = round ∧
      keyProtocol.Active
        certificate.activeReceipt
        (releasedVote release).signerQ
        release.runtime.keyQ
        (releasedVote release).epochQ
        (phaseConfig transition phase)
        (releasedVote release) :=
  ⟨activation.active, certificate.configBound, certificate.slotBound,
    certificate.parentHeadBound, certificate.roundBound, certificate.active⟩

/-! ## RCC-53: finalized checkpoint historical inclusion -/

/--
Inclusion and certified exclusion are receipt languages over the complete
RCC-45 checkpoint coordinate.  Same-coordinate inclusion is single-valued.
-/
structure CheckpointInclusionProtocol
    (CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition : Type u) where
  InclusionReceipt : Type u
  ExclusionReceipt : Type u
  Includes :
    InclusionReceipt → CheckpointQ → Coordinate → Item →
      Slot → Head → Config → SourceAuthority → Watermark → List Partition →
        Prop
  Excludes :
    ExclusionReceipt → CheckpointQ → Coordinate → Item →
      Slot → Head → Config → SourceAuthority → Watermark → List Partition →
        Prop
  exclusionSound :
    ∀ {exclusionReceipt inclusionReceipt checkpoint coordinate item
      slot head config authority watermark partitions},
      Excludes exclusionReceipt checkpoint coordinate item
        slot head config authority watermark partitions →
      ¬ Includes inclusionReceipt checkpoint coordinate item
        slot head config authority watermark partitions
  sameCoordinateUnique :
    ∀ {firstReceipt secondReceipt checkpoint coordinate firstItem secondItem
      slot head config authority watermark partitions},
      Includes firstReceipt checkpoint coordinate firstItem
          slot head config authority watermark partitions →
      Includes secondReceipt checkpoint coordinate secondItem
          slot head config authority watermark partitions →
      firstItem = secondItem

/-- A checkpoint identity indexed by the actual RCC-45 finalized closure. -/
structure FinalizedCheckpoint
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (CheckpointQ : Type u)
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
        (ConfigStable := ConfigStable)) where
  checkpointQ : CheckpointQ

/-- One concrete historical item included in one actual finalized checkpoint. -/
structure FinalizedCheckpointInclusion
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
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (checkpoint : FinalizedCheckpoint CheckpointQ closure)
    (expectedCoordinate : Coordinate)
    (expectedItem : Item) where
  receipt : checkpointProtocol.InclusionReceipt
  included :
    checkpointProtocol.Includes
      receipt checkpoint.checkpointQ expectedCoordinate expectedItem
      closure.snapshot.slot closure.snapshot.head closure.snapshot.config
      closure.snapshot.sourceAuthority closure.snapshot.watermark
      closure.snapshot.priorPartitions

/-- Dot-notation accessor for the indexed historical coordinate. -/
def FinalizedCheckpointInclusion.coordinate
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {expectedCoordinate : Coordinate} {expectedItem : Item}
    (_certificate :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint expectedCoordinate expectedItem) :
    Coordinate :=
  expectedCoordinate

/-- Dot-notation accessor for the indexed historical item. -/
def FinalizedCheckpointInclusion.item
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {expectedCoordinate : Coordinate} {expectedItem : Item}
    (_certificate :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint expectedCoordinate expectedItem) :
    Item :=
  expectedItem

/-- Certified absence/mismatch inside the same actual finalized checkpoint. -/
structure FinalizedCheckpointExclusion
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
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (checkpoint : FinalizedCheckpoint CheckpointQ closure)
    (coordinate : Coordinate)
    (item : Item) where
  receipt : checkpointProtocol.ExclusionReceipt
  excluded :
    checkpointProtocol.Excludes
      receipt checkpoint.checkpointQ coordinate item
      closure.snapshot.slot closure.snapshot.head closure.snapshot.config
      closure.snapshot.sourceAuthority closure.snapshot.watermark
      closure.snapshot.priorPartitions

/-- RCC-53 result with distinct pending and certified-exclusion polarities. -/
inductive HistoricalInclusionAssessment
    (Inclusion Exclusion : Type u)
  | authentic :
      Inclusion → HistoricalInclusionAssessment Inclusion Exclusion
  | await :
      TemporalAuthenticityResidue →
      HistoricalInclusionAssessment Inclusion Exclusion
  | refuse :
      Exclusion → TemporalAuthenticityResidue →
      HistoricalInclusionAssessment Inclusion Exclusion

/-- Assess only supplied positive or certified-negative checkpoint evidence. -/
def assessHistoricalInclusion
    {Inclusion Exclusion : Type u}
    (inclusion? : Option Inclusion)
    (exclusion? : Option Exclusion) :
    HistoricalInclusionAssessment Inclusion Exclusion :=
  match inclusion?, exclusion? with
  | some _, some certificate =>
      .refuse certificate .historicalInclusionEvidenceConflict
  | some certificate, none => .authentic certificate
  | none, some certificate =>
      .refuse certificate .historicalSignatureUnanchored
  | none, none => .await .historicalInclusionEvidencePending

/--
Actual inclusion and exclusion receipts for the same finalized checkpoint,
coordinate, and item cannot coexist under the fixed checkpoint protocol.
-/
theorem finalized_checkpoint_inclusion_and_exclusion_conflict
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {coordinate : Coordinate} {item : Item}
    (inclusion :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint coordinate item)
    (exclusion :
      FinalizedCheckpointExclusion
        checkpointProtocol checkpoint coordinate item) :
    False :=
  checkpointProtocol.exclusionSound exclusion.excluded inclusion.included

/-- RCC-53 inclusion retains the actual RCC-45 closure in its type. -/
theorem finalized_checkpoint_inclusion_consumes_rcc45
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {coordinate : Coordinate} {item : Item}
    (_certificate :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint coordinate item) :
    Nonempty
      (FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)) ∧
      checkpointProtocol.Includes
        _certificate.receipt checkpoint.checkpointQ coordinate item
        closure.snapshot.slot closure.snapshot.head closure.snapshot.config
        closure.snapshot.sourceAuthority closure.snapshot.watermark
        closure.snapshot.priorPartitions :=
  ⟨⟨closure⟩, _certificate.included⟩

/-- Included history is single-valued at one finalized checkpoint coordinate. -/
theorem same_finalized_checkpoint_coordinate_unique
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {firstCoordinate secondCoordinate : Coordinate}
    {firstItem secondItem : Item}
    (first :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint firstCoordinate firstItem)
    (second :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint secondCoordinate secondItem)
    (sameCoordinate : firstCoordinate = secondCoordinate) :
    firstItem = secondItem := by
  subst secondCoordinate
  exact checkpointProtocol.sameCoordinateUnique first.included second.included

/-! ## RCC-54: retired-key long-range safety -/

/-- A retired key may still validate bytes; it does not gain history authority. -/
structure RetiredKeyProtocol
    (Q : Type u) (scheme : SignatureScheme Q)
    (Coordinate Item : Type u) where
  RetirementReceipt : Type u
  CompromiseReceipt : Type u
  ClaimReceipt : Type u
  Retired :
    RetirementReceipt → ReleasedSignature Q scheme → Prop
  CompromisedAfterRetirement :
    CompromiseReceipt → ReleasedSignature Q scheme → Prop
  Claims :
    ClaimReceipt → ReleasedSignature Q scheme → Coordinate → Item → Prop

/-- CM-TIME-01 with actual signature, retirement, compromise, and fork proof. -/
structure RetiredKeyCompromiseAttempt
    {Q Coordinate Item CheckpointQ Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {scheme : SignatureScheme Q}
    (retiredProtocol : RetiredKeyProtocol Q scheme Coordinate Item)
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {anchoredCoordinate : Coordinate} {anchoredItem : Item}
    (anchored :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint anchoredCoordinate anchoredItem) where
  release : ReleasedSignature Q scheme
  retirementReceipt : retiredProtocol.RetirementReceipt
  retired : retiredProtocol.Retired retirementReceipt release
  compromiseReceipt : retiredProtocol.CompromiseReceipt
  compromisedLater :
    retiredProtocol.CompromisedAfterRetirement compromiseReceipt release
  claimReceipt : retiredProtocol.ClaimReceipt
  claimedCoordinate : Coordinate
  claimedItem : Item
  claims :
    retiredProtocol.Claims
      claimReceipt release claimedCoordinate claimedItem
  coordinateBound : claimedCoordinate = anchored.coordinate
  differentItem : claimedItem ≠ anchored.item

/-- RCC-54 grants authority only to an RCC-53 inclusion. -/
inductive LongRangeAssessment (Authority Attempt : Type u)
  | authority : Authority → LongRangeAssessment Authority Attempt
  | await :
      TemporalAuthenticityResidue →
      LongRangeAssessment Authority Attempt
  | refuse :
      Attempt → TemporalAuthenticityResidue →
      LongRangeAssessment Authority Attempt

/-- Retired-key attempts never inhabit the authority branch. -/
def assessLongRangeHistory
    {Authority Attempt : Type u}
    (authority? : Option Authority)
    (attempt? : Option Attempt) :
    LongRangeAssessment Authority Attempt :=
  match authority?, attempt? with
  | some certificate, _ => .authority certificate
  | none, some attempt => .refuse attempt .longRangeHistoryForgery
  | none, none => .await .historicalInclusionEvidencePending

/--
Even with an actual later-compromised retired-key release in scope, accepted
history at the same finalized checkpoint coordinate remains single-valued.
-/
theorem later_retired_key_compromise_cannot_change_checkpointed_history
    {Q Coordinate Item CheckpointQ Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {scheme : SignatureScheme Q}
    {retiredProtocol : RetiredKeyProtocol Q scheme Coordinate Item}
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {anchoredCoordinate candidateCoordinate : Coordinate}
    {anchoredItem candidateItem : Item}
    (anchored :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint anchoredCoordinate anchoredItem)
    (candidate :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint candidateCoordinate candidateItem)
    (attempt :
      RetiredKeyCompromiseAttempt retiredProtocol anchored)
    (sameCoordinate : candidateCoordinate = anchoredCoordinate) :
    candidate.item = anchored.item ∧
      retiredProtocol.Retired
        attempt.retirementReceipt attempt.release ∧
      retiredProtocol.CompromisedAfterRetirement
        attempt.compromiseReceipt attempt.release ∧
      retiredProtocol.Claims
        attempt.claimReceipt attempt.release
          attempt.claimedCoordinate attempt.claimedItem := by
  exact
    ⟨same_finalized_checkpoint_coordinate_unique
        candidate anchored sameCoordinate,
      attempt.retired, attempt.compromisedLater, attempt.claims⟩

/-! ## RCC-55: mobile-adversary safety envelope -/

/--
All relations are observations in one admitted logical-time context/unit, not
wall-clock facts supplied by the kernel.
-/
structure LogicalTimeProtocol
    (Context Unit KeyEpoch CheckpointQ : Type u) where
  ContextReceipt : Type u
  RefreshReceipt : Type u
  ErasureReceipt : Type u
  CheckpointOrderReceipt : Type u
  AdversaryWindowReceipt : Type u
  InstantaneousBoundReceipt : Type u
  ContextAdmitted : ContextReceipt → Context → Unit → Prop
  RefreshObserved :
    RefreshReceipt → Context → Unit → KeyEpoch → KeyEpoch → Nat → Prop
  ErasureObserved :
    ErasureReceipt → Context → Unit → KeyEpoch → KeyEpoch → Prop
  CheckpointBeforeOrAtRefresh :
    CheckpointOrderReceipt → Context → Unit → CheckpointQ →
      KeyEpoch → KeyEpoch → Nat → Nat → Prop
  AdversaryWindowObserved :
    AdversaryWindowReceipt → Context → Unit → Nat → Prop
  InstantaneousBoundObserved :
    InstantaneousBoundReceipt → Context → Unit → Prop

/-- Explicit admitted context plus corruption-horizon evidence. -/
structure AdversaryWindowBound
    {Context Unit KeyEpoch CheckpointQ : Type u}
    (logicalTimeProtocol :
      LogicalTimeProtocol Context Unit KeyEpoch CheckpointQ)
    (context : Context) (unit : Unit) (horizon : Nat) where
  contextReceipt : logicalTimeProtocol.ContextReceipt
  contextAdmitted :
    logicalTimeProtocol.ContextAdmitted contextReceipt context unit
  windowReceipt : logicalTimeProtocol.AdversaryWindowReceipt
  windowObserved :
    logicalTimeProtocol.AdversaryWindowObserved
      windowReceipt context unit horizon

/-- Instantaneous bounds are explicit but insufficient on their own. -/
structure InstantaneousFaultBoundEvidence
    {Context Unit KeyEpoch CheckpointQ : Type u}
    (logicalTimeProtocol :
      LogicalTimeProtocol Context Unit KeyEpoch CheckpointQ)
    (context : Context) (unit : Unit) where
  receipt : logicalTimeProtocol.InstantaneousBoundReceipt
  observed :
    logicalTimeProtocol.InstantaneousBoundObserved receipt context unit

/-- Complete conditional RCC-55 safety envelope. -/
structure MobileAdversarySafetyEnvelope
    {Context Unit KeyEpoch CheckpointQ Item Slot Head Config SourceAuthority
      Watermark Partition Judgment Generation Epoch EffectSlot Occurrence
      FailureName EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (logicalTimeProtocol :
      LogicalTimeProtocol Context Unit KeyEpoch CheckpointQ)
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ KeyEpoch Item Slot Head Config SourceAuthority Watermark
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {checkpointEpoch : KeyEpoch} {item : Item}
    (inclusion :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint checkpointEpoch item)
    (oldEpoch newEpoch : KeyEpoch)
    (context : Context) (unit : Unit) where
  checkpointCadence : Nat
  refreshCadence : Nat
  corruptionHorizon : Nat
  checkpointCadencePositive : 0 < checkpointCadence
  refreshCadencePositive : 0 < refreshCadence
  checkpointNoSlowerThanRefresh :
    checkpointCadence ≤ refreshCadence
  refreshWithinCorruptionHorizon :
    refreshCadence < corruptionHorizon
  checkpointEpochBound : inclusion.coordinate = oldEpoch
  refreshReceipt : logicalTimeProtocol.RefreshReceipt
  refreshObserved :
    logicalTimeProtocol.RefreshObserved
      refreshReceipt context unit oldEpoch newEpoch refreshCadence
  erasureReceipt : logicalTimeProtocol.ErasureReceipt
  erasureObserved :
    logicalTimeProtocol.ErasureObserved
      erasureReceipt context unit oldEpoch newEpoch
  checkpointOrderReceipt : logicalTimeProtocol.CheckpointOrderReceipt
  checkpointBeforeOrAtRefresh :
    logicalTimeProtocol.CheckpointBeforeOrAtRefresh
      checkpointOrderReceipt context unit checkpoint.checkpointQ
      oldEpoch newEpoch checkpointCadence refreshCadence
  adversaryWindow :
    AdversaryWindowBound
      logicalTimeProtocol context unit corruptionHorizon
  instantaneousBound :
    InstantaneousFaultBoundEvidence logicalTimeProtocol context unit

/-- RCC-55 result: incomplete evidence is honest Await. -/
inductive MobileSafetyAssessment (Safety : Type u)
  | safe : Safety → MobileSafetyAssessment Safety
  | await :
      TemporalAuthenticityResidue → MobileSafetyAssessment Safety

/-- Preserve full-envelope versus missing-evidence polarity. -/
def assessMobileSafety
    {Safety : Type u}
    (safety? : Option Safety) :
    MobileSafetyAssessment Safety :=
  match safety? with
  | some safety => .safe safety
  | none => .await .mobileAdversaryBudgetUnmodeled

/-- The envelope exposes its cadence order and bound finalized checkpoint. -/
theorem mobile_adversary_safety_envelope_relations
    {Context Unit KeyEpoch CheckpointQ Item Slot Head Config SourceAuthority
      Watermark Partition Judgment Generation Epoch EffectSlot Occurrence
      FailureName EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {logicalTimeProtocol :
      LogicalTimeProtocol Context Unit KeyEpoch CheckpointQ}
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ KeyEpoch Item Slot Head Config SourceAuthority Watermark
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
    {checkpoint : FinalizedCheckpoint CheckpointQ closure}
    {checkpointEpoch : KeyEpoch} {item : Item}
    {inclusion :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint checkpointEpoch item}
    {oldEpoch newEpoch : KeyEpoch}
    {context : Context} {unit : Unit}
    (safety :
      MobileAdversarySafetyEnvelope
        logicalTimeProtocol inclusion oldEpoch newEpoch context unit) :
    0 < safety.checkpointCadence ∧
      0 < safety.refreshCadence ∧
      safety.checkpointCadence ≤ safety.refreshCadence ∧
      safety.refreshCadence < safety.corruptionHorizon ∧
      inclusion.coordinate = oldEpoch ∧
      logicalTimeProtocol.RefreshObserved
        safety.refreshReceipt context unit oldEpoch newEpoch
          safety.refreshCadence ∧
      logicalTimeProtocol.ErasureObserved
        safety.erasureReceipt context unit oldEpoch newEpoch ∧
      logicalTimeProtocol.CheckpointBeforeOrAtRefresh
        safety.checkpointOrderReceipt context unit checkpoint.checkpointQ
          oldEpoch newEpoch safety.checkpointCadence safety.refreshCadence ∧
      logicalTimeProtocol.ContextAdmitted
        safety.adversaryWindow.contextReceipt context unit ∧
      logicalTimeProtocol.AdversaryWindowObserved
        safety.adversaryWindow.windowReceipt context unit
          safety.corruptionHorizon ∧
      logicalTimeProtocol.InstantaneousBoundObserved
        safety.instantaneousBound.receipt context unit :=
  ⟨safety.checkpointCadencePositive, safety.refreshCadencePositive,
    safety.checkpointNoSlowerThanRefresh,
    safety.refreshWithinCorruptionHorizon,
    safety.checkpointEpochBound,
    safety.refreshObserved, safety.erasureObserved,
    safety.checkpointBeforeOrAtRefresh,
    safety.adversaryWindow.contextAdmitted,
    safety.adversaryWindow.windowObserved,
    safety.instantaneousBound.observed⟩

end Residua.RCC.TemporalAuthenticity

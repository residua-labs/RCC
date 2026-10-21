import RCC.TemporalAuthenticity
import RCCTests.DurableVoteLock
import RCCTests.FinalizedHeadWindow

/-!
# RCC-52..RCC-55 Temporal Authenticity Tests

Each positive branch carries the exact upstream certificate it consumes.
Missing evidence is Await; refusal requires a proof-carrying closed epoch,
sealed checkpoint exclusion, or different-item long-range attempt.
-/

namespace Residua.RCC.TemporalAuthenticity.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.TemporalAuthenticity
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.FinalizedHeadWindow.Tests

/-! ## RCC-52: actual RCC-41 release plus actual RCC-44 activation -/

def transition :
    AuthorityTransition Token Token Token Token Token where
  oldConfig := .configB
  newConfig := .configA
  activationSlot := .slotA
  activationHead := .headA
  roundBoundary := 0
  membershipDelta := {
    added := [.keyNew]
    removed := [.keyOld]
  }
  preStateAuthority := .signerA

def jointProtocol :
    JointQuorumProtocol Token Token Token Token Token Token Token where
  OldAccepts receipt candidate :=
    receipt = .signatureP ∧ candidate = transition
  NewAccepts receipt candidate :=
    receipt = .signatureQ ∧ candidate = transition
  TransitionCoherent candidate := candidate = transition
  jointBindsCoherent := by
    intro oldReceipt newReceipt candidate oldAccepted _newAccepted
    exact oldAccepted.2
  coherentAtCoordinate := by
    intro first second firstCoherent secondCoherent _sameSlot _sameHead
      _sameRound
    exact firstCoherent.trans secondCoherent.symm

def jointEvidence : JointQuorumTransition jointProtocol transition where
  oldReceipt := .signatureP
  newReceipt := .signatureQ
  oldAccepted := ⟨rfl, rfl⟩
  newAccepted := ⟨rfl, rfl⟩

def rcc44WriterSpec : FencedWriterSpec Token Token where
  slotParent := fun _ => .headA

def tokenEquivalence : JudgmentEquivalence Token where
  Equivalent := Eq
  refl := by intro _; rfl
  symm := by intro _ _ equality; exact equality.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide := fun first second => inferInstanceAs (Decidable (first = second))

def transitionAdapter :
    ReconfigurationJudgmentAdapter
      Token Token Token Token Token Token tokenEquivalence where
  project := fun _ => transition
  equivalentBindsTransition := by
    intro _ _ _
    rfl

/--
The handoff authority language is indexed by its exact transition proposal.
The active fixture uses joint-quorum authorization, but retaining this exact
family prevents the alternative finalized-handoff branch from accepting an
unrelated proposal witness.
-/
def transitionProposal : Proposal Token Token Token :=
  ⟨.slotA, .headA, .proposalP⟩

inductive TransitionAuthorityEvidence :
    Proposal Token Token Token → Type
  | admitted :
      TransitionAuthorityEvidence transitionProposal

def rcc44WriterState :
    FencedWriterState Token Token Token Token where
  generation := .processOne
  canonicalHead := .headA
  decisions := fun _ => some .proposalP

def transitionEnvelope :
    AuthorizedTransitionEnvelope
      TransitionAuthorityEvidence jointProtocol rcc44WriterSpec
        tokenEquivalence transitionAdapter rcc44WriterState where
  transition := transition
  authorization := .jointQuorum jointEvidence

def activation :
    AuthorizedActivationEvidence
      TransitionAuthorityEvidence jointProtocol rcc44WriterSpec
        tokenEquivalence transitionAdapter rcc44WriterState
        transition transitionEnvelope
        .slotA .headA 0 .new where
  transitionBound := rfl
  active := .new rfl rfl (Nat.zero_le 0)

def activeKeyEpochRelation
    (receipt signer key epoch config : Token) (vote : Vote Token) : Prop :=
  receipt = .unlockCert ∧
    signer = .signerA ∧
    key = .keyOld ∧
    epoch = .epochA ∧
    config = .configA ∧
    vote = voteP

def closedKeyEpochRelation
    (receipt signer key epoch : Token) : Prop :=
  receipt = .lockQ ∧
    signer = .signerA ∧
    key = .keyOld ∧
    epoch = .epochB

def keyEpochProtocol : KeyEpochProtocol Token where
  ActiveReceipt := Token
  ClosedReceipt := Token
  Active := activeKeyEpochRelation
  ClosedOrRetired := closedKeyEpochRelation
  activeClosedDisjoint := by
    intro activeReceipt closedReceipt signer runtimeKey keyEpoch config vote
      active closed
    have activeEpoch : keyEpoch = .epochA :=
      active.2.2.2.1
    have closedEpoch : keyEpoch = .epochB :=
      closed.2.2.2
    exact
      (by decide : Token.epochA ≠ Token.epochB)
        (activeEpoch.symm.trans closedEpoch)

def activeVoteCertificate :
    KeyEpochVoteCertificate keyEpochProtocol activation releaseP where
  configBound := rfl
  slotBound := rfl
  parentHeadBound := rfl
  roundBound := rfl
  activeReceipt := .unlockCert
  active := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def retiredCommit : DurableLockCommit Token where
  lock := {
    vote := replayVote
    lockQ := .lockQ
  }
  committedAt := 0

def retiredEnvelope :
    SignatureEnvelope Token exactVoteSignatureScheme where
  signedVote := replayVote
  signatureQ := replayVote

def retiredRuntime : SignerRuntime Token where
  signerQ := .signerA
  keyQ := .keyOld
  processQ := .processTwo

def retiredRelease :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := retiredCommit
  envelope := retiredEnvelope
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := retiredRuntime
  runtimeSigner := rfl
  releasedAt := 1
  lockBeforeRelease := by decide

def retiredVoteCertificate :
    ClosedOrRetiredKeyEpochCertificate
      keyEpochProtocol activation retiredRelease :=
  .closedOrRetired .lockQ ⟨rfl, rfl, rfl, rfl⟩

abbrev ActiveVoteCertificate :=
  KeyEpochVoteCertificate keyEpochProtocol activation releaseP

abbrev ActiveVoteClosedCertificate :=
  ClosedOrRetiredKeyEpochCertificate
    keyEpochProtocol activation releaseP

abbrev RetiredVoteAdmissibleCertificate :=
  KeyEpochVoteCertificate keyEpochProtocol activation retiredRelease

abbrev RetiredVoteClosedCertificate :=
  ClosedOrRetiredKeyEpochCertificate
    keyEpochProtocol activation retiredRelease

theorem active_vote_is_admissible :
    Nonempty ActiveVoteCertificate :=
  ⟨activeVoteCertificate⟩

theorem fixed_key_protocol_forbids_active_and_closed_epoch
    {activeReceipt closedReceipt signer runtimeKey keyEpoch config : Token}
    {vote : Vote Token}
    (active :
      keyEpochProtocol.Active
        activeReceipt signer runtimeKey keyEpoch config vote)
    (closed :
      keyEpochProtocol.ClosedOrRetired
        closedReceipt signer runtimeKey keyEpoch) :
    False :=
  keyEpochProtocol.activeClosedDisjoint active closed

theorem active_and_closed_certificates_cannot_coexist
    (closed : ActiveVoteClosedCertificate) :
    False :=
  key_epoch_active_and_closed_certificates_conflict
    activeVoteCertificate closed

theorem active_vote_binds_both_epoch_domains :
    ActiveAt transition .slotA .headA 0 .new ∧
      (releasedVote releaseP).configQ = phaseConfig transition .new ∧
      (releasedVote releaseP).slotQ = .slotA ∧
      (releasedVote releaseP).parentHeadQ = .headA ∧
      (releasedVote releaseP).round = 0 ∧
      keyEpochProtocol.Active
        activeVoteCertificate.activeReceipt
        (releasedVote releaseP).signerQ
        releaseP.runtime.keyQ
        (releasedVote releaseP).epochQ
        (phaseConfig transition .new)
        (releasedVote releaseP) :=
  key_epoch_vote_certificate_binds_active_epochs activeVoteCertificate

theorem missing_key_epoch_evidence_awaits :
    (match assessKeyEpochVote
        (none : Option ActiveVoteCertificate)
        (none : Option ActiveVoteClosedCertificate) with
      | .await .keyEpochEvidencePending => true
      | _ => false) = true := by
  rfl

theorem explicit_retired_epoch_refuses_late_vote :
    (match assessKeyEpochVote
        (none : Option RetiredVoteAdmissibleCertificate)
        (some retiredVoteCertificate) with
      | .refuse _ .lateVoteForClosedKeyEpoch => true
      | _ => false) = true := by
  rfl

theorem simultaneous_positive_and_closed_inputs_refuse :
    (match assessKeyEpochVote (some ()) (some ()) with
      | .refuse _ .lateVoteForClosedKeyEpoch => true
      | _ => false) = true := by
  rfl

theorem late_vote_refusal_contains_retirement_proof :
    keyEpochProtocol.ClosedOrRetired
      .lockQ
      (releasedVote retiredRelease).signerQ
      retiredRelease.runtime.keyQ
      (releasedVote retiredRelease).epochQ :=
  ⟨rfl, rfl, rfl, rfl⟩

/-! ## RCC-53: actual RCC-45 finalized closure and complete coverage -/

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

inductive HistoricalItem
  | anchored
  | unanchored
  deriving DecidableEq, Repr

def checkpointIncludes
    (receipt checkpoint coordinate : Token)
    (item : HistoricalItem)
    (slot : Slot) (head : Head) (config : Config)
    (authority : SourceAuthority) (watermark : Watermark)
    (partitions : List Partition) : Prop :=
  receipt = .signatureP ∧
    checkpoint = .lockP ∧
    coordinate = .epochA ∧
    item = .anchored ∧
    slot = .deploy ∧
    head = .headA ∧
    config = .v1 ∧
    authority = .origin ∧
    watermark = .ten ∧
    partitions = [.zero, .one]

def checkpointExcludes
    (receipt checkpoint coordinate : Token)
    (item : HistoricalItem)
    (slot : Slot) (head : Head) (config : Config)
    (authority : SourceAuthority) (watermark : Watermark)
    (partitions : List Partition) : Prop :=
  receipt = .signatureQ ∧
    checkpoint = .lockP ∧
    coordinate = .epochA ∧
    item = .unanchored ∧
    slot = .deploy ∧
    head = .headA ∧
    config = .v1 ∧
    authority = .origin ∧
    watermark = .ten ∧
    partitions = [.zero, .one]

def checkpointProtocol :
    CheckpointInclusionProtocol
      Token Token HistoricalItem Slot Head Config SourceAuthority Watermark
        Partition where
  InclusionReceipt := Token
  ExclusionReceipt := Token
  Includes := checkpointIncludes
  Excludes := checkpointExcludes
  exclusionSound := by
    intro exclusionReceipt inclusionReceipt checkpoint coordinate item slot
      head config authority watermark partitions excluded included
    have excludedItem : item = .unanchored :=
      excluded.2.2.2.1
    have includedItem : item = .anchored :=
      included.2.2.2.1
    exact (by decide : HistoricalItem.unanchored ≠ .anchored)
      (excludedItem.symm.trans includedItem)
  sameCoordinateUnique := by
    intro firstReceipt secondReceipt checkpoint coordinate firstItem secondItem
      slot head config authority watermark partitions firstIncluded
      secondIncluded
    exact firstIncluded.2.2.2.1.trans secondIncluded.2.2.2.1.symm

def checkpoint :
    FinalizedCheckpoint Token finalizedClosure where
  checkpointQ := .lockP

def anchoredInclusion :
    FinalizedCheckpointInclusion
      checkpointProtocol checkpoint .epochA .anchored where
  receipt := .signatureP
  included :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

def sealedExclusion :
    FinalizedCheckpointExclusion
      checkpointProtocol checkpoint .epochA .unanchored where
  receipt := .signatureQ
  excluded :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

abbrev AnchoredInclusion :=
  FinalizedCheckpointInclusion
    checkpointProtocol checkpoint .epochA .anchored

abbrev AnchoredExclusion :=
  FinalizedCheckpointExclusion
    checkpointProtocol checkpoint .epochA .anchored

theorem finalized_checkpoint_inclusion_is_authentic :
    Nonempty AnchoredInclusion :=
  ⟨anchoredInclusion⟩

theorem finalized_inclusion_consumes_actual_rcc45_closure :
    Nonempty
      (FinalizedClosureEvidence
        (environment := admissionEnvironment)
        (history := finalizedHistory)
        (ConfigLawful := configLawful)
        (protocol := sourceProtocol)
        (ConfigStable := configStable)) ∧
      checkpointProtocol.Includes
        anchoredInclusion.receipt checkpoint.checkpointQ .epochA .anchored
        finalizedClosure.snapshot.slot finalizedClosure.snapshot.head
        finalizedClosure.snapshot.config
        finalizedClosure.snapshot.sourceAuthority
        finalizedClosure.snapshot.watermark
        finalizedClosure.snapshot.priorPartitions :=
  finalized_checkpoint_inclusion_consumes_rcc45 anchoredInclusion

theorem absent_historical_evidence_only_awaits :
    (match assessHistoricalInclusion
        (none : Option AnchoredInclusion)
        (none : Option AnchoredExclusion) with
      | .await .historicalInclusionEvidencePending => true
      | _ => false) = true := by
  rfl

theorem sealed_unanchored_candidate_is_refused :
    (match assessHistoricalInclusion
        (none :
          Option
            (FinalizedCheckpointInclusion
              checkpointProtocol checkpoint .epochA .unanchored))
        (some sealedExclusion) with
      | .refuse _ .historicalSignatureUnanchored => true
      | _ => false) = true := by
  rfl

theorem simultaneous_inclusion_and_exclusion_is_not_authentic :
    (match assessHistoricalInclusion (some ()) (some ()) with
      | .authentic _ => false
      | _ => true) = true := by
  rfl

theorem simultaneous_inclusion_and_exclusion_fail_closed :
    (match assessHistoricalInclusion (some ()) (some ()) with
      | .refuse _ .historicalInclusionEvidenceConflict => true
      | _ => false) = true := by
  rfl

theorem same_checkpoint_inclusion_and_exclusion_cannot_coexist
    (exclusion : AnchoredExclusion) :
    False :=
  finalized_checkpoint_inclusion_and_exclusion_conflict
    anchoredInclusion exclusion

theorem same_checkpoint_historical_items_are_unique
    (other : AnchoredInclusion) :
    HistoricalItem.anchored = HistoricalItem.anchored :=
  same_finalized_checkpoint_coordinate_unique
    anchoredInclusion other rfl

/-! ## RCC-54 / CM-TIME-01: valid old-key bytes are not history authority -/

def retiredAt
    (receipt : Token)
    (release : ReleasedSignature Token exactVoteSignatureScheme) : Prop :=
  receipt = .lockQ ∧ release = retiredRelease

def compromisedLater
    (receipt : Token)
    (release : ReleasedSignature Token exactVoteSignatureScheme) : Prop :=
  receipt = .unlockCert ∧ release = retiredRelease

def retiredReleaseClaims
    (receipt : Token)
    (release : ReleasedSignature Token exactVoteSignatureScheme)
    (coordinate : Token) (item : HistoricalItem) : Prop :=
  receipt = .signatureQ ∧
    release = retiredRelease ∧
    coordinate = .epochA ∧
    item = .unanchored

def retiredProtocol :
    RetiredKeyProtocol
      Token exactVoteSignatureScheme Token HistoricalItem where
  RetirementReceipt := Token
  CompromiseReceipt := Token
  ClaimReceipt := Token
  Retired := retiredAt
  CompromisedAfterRetirement := compromisedLater
  Claims := retiredReleaseClaims

def oldKeyAttempt :
    RetiredKeyCompromiseAttempt retiredProtocol anchoredInclusion where
  release := retiredRelease
  retirementReceipt := .lockQ
  retired := ⟨rfl, rfl⟩
  compromiseReceipt := .unlockCert
  compromisedLater := ⟨rfl, rfl⟩
  claimReceipt := .signatureQ
  claimedCoordinate := .epochA
  claimedItem := .unanchored
  claims := ⟨rfl, rfl, rfl, rfl⟩
  coordinateBound := rfl
  differentItem := by decide

abbrev ForgedItemInclusion :=
  FinalizedCheckpointInclusion
    checkpointProtocol checkpoint .epochA .unanchored

abbrev OldKeyAttempt :=
  RetiredKeyCompromiseAttempt retiredProtocol anchoredInclusion

theorem retired_key_signature_remains_locally_valid :
    exactVoteSignatureScheme.Accepts
      oldKeyAttempt.release.envelope.signatureQ
      (exactVoteSignatureScheme.canonicalVoteMessage
        oldKeyAttempt.release.envelope.signedVote) :=
  oldKeyAttempt.release.validSignature.accepted

theorem missing_checkpoint_authority_awaits :
    (match assessLongRangeHistory
        (none : Option AnchoredInclusion)
        (none : Option OldKeyAttempt) with
      | .await .historicalInclusionEvidencePending => true
      | _ => false) = true := by
  rfl

theorem old_key_forged_history_has_no_authority :
    (match assessLongRangeHistory
        (none : Option ForgedItemInclusion)
        (some oldKeyAttempt) with
      | .refuse _ .longRangeHistoryForgery => true
      | _ => false) = true := by
  rfl

theorem authority_remains_authoritative_when_attempt_is_also_supplied :
    (match assessLongRangeHistory
        (some anchoredInclusion)
        (some oldKeyAttempt) with
      | .authority _ => true
      | _ => false) = true := by
  rfl

theorem later_compromise_cannot_change_anchored_history
    (candidate : AnchoredInclusion) :
    candidate.item = anchoredInclusion.item ∧
      retiredProtocol.Retired
        oldKeyAttempt.retirementReceipt oldKeyAttempt.release ∧
      retiredProtocol.CompromisedAfterRetirement
        oldKeyAttempt.compromiseReceipt oldKeyAttempt.release ∧
      retiredProtocol.Claims
        oldKeyAttempt.claimReceipt oldKeyAttempt.release
          oldKeyAttempt.claimedCoordinate oldKeyAttempt.claimedItem :=
  later_retired_key_compromise_cannot_change_checkpointed_history
    anchoredInclusion candidate oldKeyAttempt rfl

/-! ## RCC-55 / CM-TIME-02: mobile safety needs the complete envelope -/

def contextAdmitted
    (receipt context unit : Token) : Prop :=
  receipt = .policyA ∧ context = .processOne ∧ unit = .slotA

def refreshObserved
    (receipt context unit oldEpoch newEpoch : Token)
    (cadence : Nat) : Prop :=
  receipt = .keyNew ∧
    context = .processOne ∧
    unit = .slotA ∧
    oldEpoch = .epochA ∧
    newEpoch = .epochB ∧
    cadence = 4

def erasureObserved
    (receipt context unit oldEpoch newEpoch : Token) : Prop :=
  receipt = .keyOld ∧
    context = .processOne ∧
    unit = .slotA ∧
    oldEpoch = .epochA ∧
    newEpoch = .epochB

def checkpointBeforeRefresh
    (receipt context unit checkpointQ oldEpoch newEpoch : Token)
    (checkpointCadence refreshCadence : Nat) : Prop :=
  receipt = .lockP ∧
    context = .processOne ∧
    unit = .slotA ∧
    checkpointQ = .lockP ∧
    oldEpoch = .epochA ∧
    newEpoch = .epochB ∧
    checkpointCadence = 2 ∧
    refreshCadence = 4

def adversaryWindowObserved
    (receipt context unit : Token) (horizon : Nat) : Prop :=
  receipt = .policyB ∧
    context = .processOne ∧
    unit = .slotA ∧
    horizon = 10

def instantaneousBoundObserved
    (receipt context unit : Token) : Prop :=
  receipt = .verdictAccept ∧
    context = .processOne ∧
    unit = .slotA

def logicalTimeProtocol : LogicalTimeProtocol Token Token Token Token where
  ContextReceipt := Token
  RefreshReceipt := Token
  ErasureReceipt := Token
  CheckpointOrderReceipt := Token
  AdversaryWindowReceipt := Token
  InstantaneousBoundReceipt := Token
  ContextAdmitted := contextAdmitted
  RefreshObserved := refreshObserved
  ErasureObserved := erasureObserved
  CheckpointBeforeOrAtRefresh := checkpointBeforeRefresh
  AdversaryWindowObserved := adversaryWindowObserved
  InstantaneousBoundObserved := instantaneousBoundObserved

def adversaryWindow :
    AdversaryWindowBound
      logicalTimeProtocol .processOne .slotA 10 where
  contextReceipt := .policyA
  contextAdmitted := ⟨rfl, rfl, rfl⟩
  windowReceipt := .policyB
  windowObserved := ⟨rfl, rfl, rfl, rfl⟩

def instantaneousBound :
    InstantaneousFaultBoundEvidence
      logicalTimeProtocol .processOne .slotA where
  receipt := .verdictAccept
  observed := ⟨rfl, rfl, rfl⟩

def mobileSafety :
    MobileAdversarySafetyEnvelope
      logicalTimeProtocol anchoredInclusion
        .epochA .epochB .processOne .slotA where
  checkpointCadence := 2
  refreshCadence := 4
  corruptionHorizon := 10
  checkpointCadencePositive := by decide
  refreshCadencePositive := by decide
  checkpointNoSlowerThanRefresh := by decide
  refreshWithinCorruptionHorizon := by decide
  checkpointEpochBound := rfl
  refreshReceipt := .keyNew
  refreshObserved := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  erasureReceipt := .keyOld
  erasureObserved := ⟨rfl, rfl, rfl, rfl, rfl⟩
  checkpointOrderReceipt := .lockP
  checkpointBeforeOrAtRefresh :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  adversaryWindow := adversaryWindow
  instantaneousBound := instantaneousBound

abbrev MobileSafety :=
  MobileAdversarySafetyEnvelope
    logicalTimeProtocol anchoredInclusion
      .epochA .epochB .processOne .slotA

theorem complete_mobile_safety_envelope_is_safe :
    (match assessMobileSafety (some mobileSafety) with
      | .safe _ => true
      | _ => false) = true := by
  rfl

theorem instantaneous_bound_alone_awaits :
    (match assessMobileSafety (none : Option MobileSafety) with
      | .await .mobileAdversaryBudgetUnmodeled => true
      | _ => false) = true := by
  rfl

def missingRefreshProtocol : LogicalTimeProtocol Token Token Token Token :=
  { logicalTimeProtocol with
    RefreshObserved := fun _ _ _ _ _ _ => False }

def missingErasureProtocol : LogicalTimeProtocol Token Token Token Token :=
  { logicalTimeProtocol with
    ErasureObserved := fun _ _ _ _ _ => False }

def missingCheckpointProtocol :
    LogicalTimeProtocol Token Token Token Token :=
  { logicalTimeProtocol with
    CheckpointBeforeOrAtRefresh := fun _ _ _ _ _ _ _ _ => False }

def missingWindowProtocol : LogicalTimeProtocol Token Token Token Token :=
  { logicalTimeProtocol with
    AdversaryWindowObserved := fun _ _ _ _ => False }

theorem missing_refresh_cannot_construct_mobile_safety :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        missingRefreshProtocol anchoredInclusion
          .epochA .epochB .processOne .slotA) := by
  rintro ⟨safety⟩
  exact safety.refreshObserved

theorem missing_erasure_cannot_construct_mobile_safety :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        missingErasureProtocol anchoredInclusion
          .epochA .epochB .processOne .slotA) := by
  rintro ⟨safety⟩
  exact safety.erasureObserved

theorem missing_checkpoint_cannot_construct_mobile_safety :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        missingCheckpointProtocol anchoredInclusion
          .epochA .epochB .processOne .slotA) := by
  rintro ⟨safety⟩
  exact safety.checkpointBeforeOrAtRefresh

theorem missing_window_cannot_construct_mobile_safety :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        missingWindowProtocol anchoredInclusion
          .epochA .epochB .processOne .slotA) := by
  rintro ⟨safety⟩
  exact safety.adversaryWindow.windowObserved

theorem mobile_safety_relates_all_temporal_evidence :
    0 < mobileSafety.checkpointCadence ∧
      0 < mobileSafety.refreshCadence ∧
      mobileSafety.checkpointCadence ≤ mobileSafety.refreshCadence ∧
      mobileSafety.refreshCadence < mobileSafety.corruptionHorizon ∧
      anchoredInclusion.coordinate = Token.epochA ∧
      refreshObserved
        mobileSafety.refreshReceipt .processOne .slotA .epochA .epochB
          mobileSafety.refreshCadence ∧
      erasureObserved
        mobileSafety.erasureReceipt .processOne .slotA .epochA .epochB ∧
      checkpointBeforeRefresh
        mobileSafety.checkpointOrderReceipt
        .processOne .slotA checkpoint.checkpointQ .epochA .epochB
          mobileSafety.checkpointCadence mobileSafety.refreshCadence ∧
      contextAdmitted
        mobileSafety.adversaryWindow.contextReceipt .processOne .slotA ∧
      adversaryWindowObserved
        mobileSafety.adversaryWindow.windowReceipt .processOne .slotA
          mobileSafety.corruptionHorizon ∧
      instantaneousBoundObserved
        mobileSafety.instantaneousBound.receipt .processOne .slotA :=
  mobile_adversary_safety_envelope_relations mobileSafety

#print axioms key_epoch_vote_certificate_binds_active_epochs
#print axioms key_epoch_active_and_closed_certificates_conflict
#print axioms finalized_checkpoint_inclusion_consumes_rcc45
#print axioms finalized_checkpoint_inclusion_and_exclusion_conflict
#print axioms same_finalized_checkpoint_coordinate_unique
#print axioms later_retired_key_compromise_cannot_change_checkpointed_history
#print axioms mobile_adversary_safety_envelope_relations
#print axioms assessKeyEpochVote
#print axioms assessHistoricalInclusion
#print axioms assessLongRangeHistory
#print axioms assessMobileSafety

end Residua.RCC.TemporalAuthenticity.Tests

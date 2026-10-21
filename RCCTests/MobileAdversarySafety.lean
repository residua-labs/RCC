import RCC.MobileAdversarySafety
import RCCTests.KeyEpochVote
import RCCTests.TemporalAuthenticity

/-!
# RCC-55 Mobile-Adversary Safety Countermodels

The positive fixture consumes:

* the actual strong RCC-52 key/config vote certificate;
* an actual RCC-45 finalized checkpoint over the retired key epoch;
* refresh, old-key erasure, checkpoint-order, and corruption-horizon receipts;
* an exact four-interval corruption universe; and
* exposure evidence for every interval in both partitions.

The mutants refuse an omitted interval, refresh without erasure, checkpoint
cadence outside the corruption horizon, and partition-local exposure.
-/

namespace Residua.RCC.MobileAdversarySafety.Tests

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

/-! ## Actual finalized checkpoint over the retired epoch -/

def mobileCheckpointIncludes
    (receipt checkpointQ coordinate : Token)
    (item : HistoricalItem)
    (slot : Slot)
    (head : Head)
    (config : Config)
    (authority : SourceAuthority)
    (watermark : Watermark)
    (partitions : List Partition) : Prop :=
  receipt = .signatureP ∧
    checkpointQ = .lockP ∧
    coordinate = .epochB ∧
    item = .anchored ∧
    slot = .deploy ∧
    head = .headA ∧
    config = .v1 ∧
    authority = .origin ∧
    watermark = .ten ∧
    partitions = [.zero, .one]

def mobileCheckpointProtocol :
    CheckpointInclusionProtocol
      Token Token HistoricalItem Slot Head Config SourceAuthority Watermark
        Partition where
  InclusionReceipt := Token
  ExclusionReceipt := Token
  Includes := mobileCheckpointIncludes
  Excludes := fun _ _ _ _ _ _ _ _ _ _ => False
  exclusionSound := by
    intro _ _ _ _ _ _ _ _ _ _ _ excluded _
    exact excluded
  sameCoordinateUnique := by
    intro _ _ _ _ firstItem secondItem _ _ _ _ _ _ firstIncluded
      secondIncluded
    exact firstIncluded.2.2.2.1.trans secondIncluded.2.2.2.1.symm

def mobileCheckpoint :
    FinalizedCheckpoint Token finalizedClosure where
  checkpointQ := .lockP

def mobileInclusion :
    FinalizedCheckpointInclusion
      mobileCheckpointProtocol mobileCheckpoint .epochB .anchored where
  receipt := .signatureP
  included :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## Logical-time refresh, erasure, checkpoint, and corruption horizon -/

def mobileContextAdmitted
    (receipt context unit : Token) : Prop :=
  receipt = .policyA ∧ context = .processOne ∧ unit = .slotA

def mobileRefreshObserved
    (receipt context unit oldEpoch newEpoch : Token)
    (cadence : Nat) : Prop :=
  receipt = .keyNew ∧
    context = .processOne ∧
    unit = .slotA ∧
    oldEpoch = .epochB ∧
    newEpoch = .epochA ∧
    cadence = 4

def mobileErasureObserved
    (receipt context unit oldEpoch newEpoch : Token) : Prop :=
  receipt = .keyOld ∧
    context = .processOne ∧
    unit = .slotA ∧
    oldEpoch = .epochB ∧
    newEpoch = .epochA

def mobileCheckpointBeforeRefresh
    (receipt context unit checkpointQ oldEpoch newEpoch : Token)
    (checkpointCadence refreshCadence : Nat) : Prop :=
  receipt = .lockP ∧
    context = .processOne ∧
    unit = .slotA ∧
    checkpointQ = .lockP ∧
    oldEpoch = .epochB ∧
    newEpoch = .epochA ∧
    checkpointCadence = 2 ∧
    refreshCadence = 4

def mobileAdversaryWindowObserved
    (receipt context unit : Token)
    (horizon : Nat) : Prop :=
  receipt = .policyB ∧
    context = .processOne ∧
    unit = .slotA ∧
    horizon = 10

def mobileInstantaneousBoundObserved
    (receipt context unit : Token) : Prop :=
  receipt = .verdictAccept ∧
    context = .processOne ∧
    unit = .slotA

def mobileLogicalTimeProtocol :
    LogicalTimeProtocol Token Token Token Token where
  ContextReceipt := Token
  RefreshReceipt := Token
  ErasureReceipt := Token
  CheckpointOrderReceipt := Token
  AdversaryWindowReceipt := Token
  InstantaneousBoundReceipt := Token
  ContextAdmitted := mobileContextAdmitted
  RefreshObserved := mobileRefreshObserved
  ErasureObserved := mobileErasureObserved
  CheckpointBeforeOrAtRefresh := mobileCheckpointBeforeRefresh
  AdversaryWindowObserved := mobileAdversaryWindowObserved
  InstantaneousBoundObserved := mobileInstantaneousBoundObserved

def mobileAdversaryWindow :
    AdversaryWindowBound
      mobileLogicalTimeProtocol .processOne .slotA 10 where
  contextReceipt := .policyA
  contextAdmitted := ⟨rfl, rfl, rfl⟩
  windowReceipt := .policyB
  windowObserved := ⟨rfl, rfl, rfl, rfl⟩

def mobileInstantaneousBound :
    InstantaneousFaultBoundEvidence
      mobileLogicalTimeProtocol .processOne .slotA where
  receipt := .verdictAccept
  observed := ⟨rfl, rfl, rfl⟩

def mobileTemporalSafety :
    MobileAdversarySafetyEnvelope
      mobileLogicalTimeProtocol mobileInclusion
        .epochB .epochA .processOne .slotA where
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
  adversaryWindow := mobileAdversaryWindow
  instantaneousBound := mobileInstantaneousBound

/-! ## Complete two-partition corruption universe -/

inductive CorruptionInterval
  | zeroEarly
  | zeroLate
  | oneEarly
  | oneLate
  deriving DecidableEq, Repr

def RequiredCorruptionInterval (_ : CorruptionInterval) : Prop :=
  True

def allCorruptionIntervals : List CorruptionInterval :=
  [.zeroEarly, .zeroLate, .oneEarly, .oneLate]

def corruptionUniverseSeal :
    CorruptionUniverseSeal
      RequiredCorruptionInterval allCorruptionIntervals where
  exact := by
    intro interval
    constructor
    · intro _member
      trivial
    · intro _required
      cases interval <;> simp [allCorruptionIntervals]

def exposureObserved
    (receipt context unit keyEpoch configEpoch : Token)
    (horizon : Nat)
    (_interval : CorruptionInterval) : Prop :=
  receipt = .policyB ∧
    context = .processOne ∧
    unit = .slotA ∧
    keyEpoch = .epochA ∧
    configEpoch = .configA ∧
    horizon = 10

def exposureProtocol :
    ExposureProtocol
      Token Token Token Token CorruptionInterval where
  Receipt := Token
  Observed := exposureObserved

def completeExposure :
    CompleteExposureEvidence
      exposureProtocol RequiredCorruptionInterval allCorruptionIntervals
        corruptionUniverseSeal .processOne .slotA .epochA .configA 10 where
  receipt := fun _interval _member => .policyB
  observed := by
    intro _interval _member
    exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

def completeSafety :
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
      RequiredCorruptionInterval exposureProtocol where
  activeVote := releasePActive
  temporalSafety := mobileTemporalSafety
  corruptionIntervals := allCorruptionIntervals
  corruptionSeal := corruptionUniverseSeal
  exposure := completeExposure

theorem complete_mobile_adversary_certificate_is_safe :
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
              mobileTemporalSafety.corruptionHorizon interval :=
  mobile_adversary_safety completeSafety

theorem every_incomplete_envelope_awaits
    (residue : MobileAdversarySafetyResidue) :
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
      MobileAdversaryAssessment.await residue :=
  incomplete_mobile_adversary_evidence_awaits residue

/-! ## Mutant 1: a declared corruption interval is omitted -/

def omittedCorruptionIntervals : List CorruptionInterval :=
  [.zeroEarly, .zeroLate, .oneEarly]

theorem omitted_corruption_interval_cannot_seal_universe :
    ¬ Nonempty
      (CorruptionUniverseSeal
        RequiredCorruptionInterval omittedCorruptionIntervals) := by
  rintro ⟨universeSeal⟩
  have required : RequiredCorruptionInterval .oneLate :=
    True.intro
  have enumerated : CorruptionInterval.oneLate ∈ omittedCorruptionIntervals :=
    universeSeal.requiredEnumerated required
  simp [omittedCorruptionIntervals] at enumerated

/-! ## Mutant 2: refresh without old-key erasure -/

def noErasureLogicalTimeProtocol :
    LogicalTimeProtocol Token Token Token Token :=
  { mobileLogicalTimeProtocol with
    ErasureObserved := fun _ _ _ _ _ => False }

theorem refresh_without_old_key_erasure_cannot_be_safe :
    ¬ Nonempty
      (MobileAdversarySafetyEnvelope
        noErasureLogicalTimeProtocol mobileInclusion
          .epochB .epochA .processOne .slotA) := by
  rintro ⟨safety⟩
  exact safety.erasureObserved

/-! ## Mutant 3: checkpoint cadence exceeds the corruption horizon -/

theorem checkpoint_slower_than_corruption_horizon_is_unsafe
    (certificate :
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
        certificate.temporalSafety.checkpointCadence) :
    False :=
  (Nat.not_lt_of_ge slow)
    (Nat.lt_of_le_of_lt
      certificate.temporalSafety.checkpointNoSlowerThanRefresh
      certificate.temporalSafety.refreshWithinCorruptionHorizon)

/-! ## Mutant 4: one partition supplies only local exposure evidence -/

def partitionLocalExposureObserved
    (receipt context unit keyEpoch configEpoch : Token)
    (horizon : Nat)
    (interval : CorruptionInterval) : Prop :=
  exposureObserved
      receipt context unit keyEpoch configEpoch horizon interval ∧
    (interval = .zeroEarly ∨ interval = .zeroLate)

def partitionLocalExposureProtocol :
    ExposureProtocol
      Token Token Token Token CorruptionInterval where
  Receipt := Token
  Observed := partitionLocalExposureObserved

theorem partition_local_evidence_cannot_cover_global_universe :
    ¬ Nonempty
      (CompleteExposureEvidence
        partitionLocalExposureProtocol RequiredCorruptionInterval
          allCorruptionIntervals corruptionUniverseSeal
          .processOne .slotA .epochA .configA 10) := by
  rintro ⟨localEvidence⟩
  obtain ⟨_receipt, _observed, localInterval⟩ :=
    localEvidence.coversRequired
      (interval := CorruptionInterval.oneLate) True.intro
  cases localInterval with
  | inl zeroEarly =>
      exact (by decide :
        CorruptionInterval.oneLate ≠ CorruptionInterval.zeroEarly) zeroEarly
  | inr zeroLate =>
      exact (by decide :
        CorruptionInterval.oneLate ≠ CorruptionInterval.zeroLate) zeroLate

#print axioms mobile_adversary_safety
#print axioms incomplete_mobile_adversary_evidence_awaits
#print axioms complete_mobile_adversary_certificate_is_safe
#print axioms omitted_corruption_interval_cannot_seal_universe
#print axioms refresh_without_old_key_erasure_cannot_be_safe
#print axioms checkpoint_slower_than_corruption_horizon_is_unsafe
#print axioms partition_local_evidence_cannot_cover_global_universe

end Residua.RCC.MobileAdversarySafety.Tests

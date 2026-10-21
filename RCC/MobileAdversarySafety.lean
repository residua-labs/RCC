import RCC.KeyEpochVote
import RCC.TemporalAuthenticity

/-!
# RCC-55 Mobile-Adversary Safety

The earlier temporal-authenticity envelope relates refresh, erasure,
checkpoint cadence, and one corruption horizon.  This module closes the
remaining global bindings:

* the active key and configuration come from an actual RCC-52 new-phase vote;
* the checkpoint is an actual RCC-45 finalized checkpoint inclusion;
* the temporal envelope rotates exactly the RCC-52 old epoch to its new epoch;
* one sealed finite universe is exact for all declared corruption intervals;
* every interval in that universe carries exposure evidence for the same
  active key, active configuration, logical unit, and corruption horizon.

Incomplete evidence is represented only as `Await`; it cannot construct a
safe result.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.MobileAdversarySafety

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.KeyEpochVote
open Residua.RCC.TemporalAuthenticity

universe u

/--
A finite interval enumeration is exact for the declared corruption universe.
An empty or partition-local list cannot prove a global negative claim merely
by omitting a required interval.
-/
structure CorruptionUniverseSeal
    {Interval : Type u}
    (Required : Interval → Prop)
    (intervals : List Interval) : Prop where
  exact :
    ∀ interval,
      interval ∈ intervals ↔ Required interval

/--
Domain realization of exposure evidence.  The observation is indexed by every
semantic coordinate that can change the mobile-adversary conclusion.
-/
structure ExposureProtocol
    (Context Unit KeyEpoch Config Interval : Type u) where
  Receipt : Type u
  Observed :
    Receipt → Context → Unit → KeyEpoch → Config → Nat → Interval → Prop

/--
Every member of the sealed corruption universe is covered for one active key,
configuration, logical unit, and corruption horizon.
-/
structure CompleteExposureEvidence
    {Context Unit KeyEpoch Config Interval : Type u}
    (protocol : ExposureProtocol Context Unit KeyEpoch Config Interval)
    (Required : Interval → Prop)
    (intervals : List Interval)
    (universeSeal : CorruptionUniverseSeal Required intervals)
    (context : Context)
    (unit : Unit)
    (activeKeyEpoch : KeyEpoch)
    (activeConfigEpoch : Config)
    (corruptionHorizon : Nat) where
  receipt :
    ∀ interval,
      interval ∈ intervals →
      protocol.Receipt
  observed :
    ∀ interval membership,
      protocol.Observed
        (receipt interval membership)
        context unit activeKeyEpoch activeConfigEpoch corruptionHorizon interval

/--
Complete RCC-55 certificate.

The RCC-52 activation is fixed to the new phase.  Consequently the temporal
envelope must refresh and erase precisely the `lawful.oldKeyEpochQ` key into
`lawful.newKeyEpochQ`, while all exposure evidence is indexed by that same new
key and the actual transition's new configuration.
-/
structure MobileAdversarySafetyCertificate
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
    {slot head : Q}
    {round : Nat}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    {Context Unit CheckpointQ Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {FinalityAuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {logicalTimeProtocol :
      LogicalTimeProtocol Context Unit Q CheckpointQ}
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Q Item Slot Head Config SourceAuthority Watermark Partition}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment FinalityAuthorityEvidence Generation Epoch EffectSlot
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
    {checkpointEpoch : Q}
    {item : Item}
    {inclusion :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint checkpointEpoch item}
    {context : Context}
    {unit : Unit}
    {Interval : Type u}
    (Required : Interval → Prop)
    (exposureProtocol :
      ExposureProtocol Context Unit Q Q Interval) where
  activeVote :
    KeyEpochVoteCertificate activation lawful registry release
  temporalSafety :
    MobileAdversarySafetyEnvelope
      logicalTimeProtocol inclusion
        lawful.oldKeyEpochQ lawful.newKeyEpochQ context unit
  corruptionIntervals : List Interval
  corruptionSeal :
    CorruptionUniverseSeal Required corruptionIntervals
  exposure :
    CompleteExposureEvidence
      exposureProtocol Required corruptionIntervals corruptionSeal
        context unit lawful.newKeyEpochQ transition.newConfig
          temporalSafety.corruptionHorizon

/-- Named evidence gaps.  Every incomplete packet remains an honest Await. -/
inductive MobileAdversarySafetyResidue
  | activeEpochEvidenceMissing
  | finalizedCheckpointMissing
  | temporalEnvelopeIncomplete
  | corruptionUniverseUnsealed
  | exposureEvidenceIncomplete
  deriving DecidableEq, Repr

/-- Only a complete proof-carrying certificate may enter the safe branch. -/
inductive MobileAdversaryEvidence (Safety : Type u)
  | complete : Safety → MobileAdversaryEvidence Safety
  | incomplete :
      MobileAdversarySafetyResidue → MobileAdversaryEvidence Safety

/-- Final RCC-55 polarity: complete is safe; every evidence gap is Await. -/
inductive MobileAdversaryAssessment (Safety : Type u)
  | safe : Safety → MobileAdversaryAssessment Safety
  | await :
      MobileAdversarySafetyResidue → MobileAdversaryAssessment Safety

/-- Mechanical assessment; an incomplete envelope has no safe constructor. -/
def assessMobileAdversarySafety
    {Safety : Type u}
    (evidence : MobileAdversaryEvidence Safety) :
    MobileAdversaryAssessment Safety :=
  match evidence with
  | .complete certificate => .safe certificate
  | .incomplete residue => .await residue

/-- Every declared interval occurs in the exact sealed enumeration. -/
theorem CorruptionUniverseSeal.requiredEnumerated
    {Interval : Type u}
    {Required : Interval → Prop}
    {intervals : List Interval}
    (universeSeal : CorruptionUniverseSeal Required intervals)
    {interval : Interval}
    (required : Required interval) :
    interval ∈ intervals :=
  (universeSeal.exact interval).mpr required

/--
The complete exposure packet yields an observation for every declared
corruption interval, not merely every interval a local partition listed.
-/
theorem CompleteExposureEvidence.coversRequired
    {Context Unit KeyEpoch Config Interval : Type u}
    {protocol : ExposureProtocol Context Unit KeyEpoch Config Interval}
    {Required : Interval → Prop}
    {intervals : List Interval}
    {universeSeal : CorruptionUniverseSeal Required intervals}
    {context : Context}
    {unit : Unit}
    {activeKeyEpoch : KeyEpoch}
    {activeConfigEpoch : Config}
    {corruptionHorizon : Nat}
    (exposure :
      CompleteExposureEvidence
        protocol Required intervals universeSeal context unit activeKeyEpoch
          activeConfigEpoch corruptionHorizon)
    {interval : Interval}
    (required : Required interval) :
    ∃ receipt,
      protocol.Observed
        receipt context unit activeKeyEpoch activeConfigEpoch
          corruptionHorizon interval := by
  have membership : interval ∈ intervals :=
    universeSeal.requiredEnumerated required
  exact
    ⟨exposure.receipt interval membership,
      exposure.observed interval membership⟩

/--
RCC-55 safety conclusion over the actual RCC-52 key/config epoch, actual
finalized checkpoint, cadence/horizon order, refresh+erasure pair, and every
declared corruption interval.
-/
theorem mobile_adversary_safety
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
    {slot head : Q}
    {round : Nat}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    {Context Unit CheckpointQ Item Slot Head Config SourceAuthority Watermark
      Partition Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {FinalityAuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {logicalTimeProtocol :
      LogicalTimeProtocol Context Unit Q CheckpointQ}
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Q Item Slot Head Config SourceAuthority Watermark Partition}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment FinalityAuthorityEvidence Generation Epoch EffectSlot
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
    {checkpointEpoch : Q}
    {item : Item}
    {inclusion :
      FinalizedCheckpointInclusion
        checkpointProtocol checkpoint checkpointEpoch item}
    {context : Context}
    {unit : Unit}
    {Interval : Type u}
    {Required : Interval → Prop}
    {exposureProtocol :
      ExposureProtocol Context Unit Q Q Interval}
    (certificate :
      MobileAdversarySafetyCertificate
        (AuthorityEvidence := AuthorityEvidence)
        (jointProtocol := jointProtocol)
        (spec := spec)
        (equivalence := equivalence)
        (adapter := adapter)
        (state := state)
        (transition := transition)
        (envelope := envelope)
        (slot := slot)
        (head := head)
        (round := round)
        (activation := activation)
        (lawful := lawful)
        (registry := registry)
        (scheme := scheme)
        (release := release)
        (FinalityAuthorityEvidence := FinalityAuthorityEvidence)
        (logicalTimeProtocol := logicalTimeProtocol)
        (checkpointProtocol := checkpointProtocol)
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (sourceProtocol := sourceProtocol)
        (ConfigStable := ConfigStable)
        (closure := closure)
        (checkpoint := checkpoint)
        (checkpointEpoch := checkpointEpoch)
        (item := item)
        (inclusion := inclusion)
        (context := context)
        (unit := unit)
        Required exposureProtocol) :
    ActiveAt transition slot head round .new ∧
      (releasedKeyEpochPayload release).signerKeyEpochQ =
        lawful.newKeyEpochQ ∧
      (releasedKeyEpochPayload release).activeConfigEpochQ =
        transition.newConfig ∧
      checkpointProtocol.Includes
        inclusion.receipt checkpoint.checkpointQ inclusion.coordinate
          inclusion.item closure.snapshot.slot
          closure.snapshot.head
          closure.snapshot.config
          closure.snapshot.sourceAuthority
          closure.snapshot.watermark
          closure.snapshot.priorPartitions ∧
      certificate.temporalSafety.checkpointCadence <
        certificate.temporalSafety.corruptionHorizon ∧
      logicalTimeProtocol.RefreshObserved
        certificate.temporalSafety.refreshReceipt context unit
          lawful.oldKeyEpochQ lawful.newKeyEpochQ
          certificate.temporalSafety.refreshCadence ∧
      logicalTimeProtocol.ErasureObserved
        certificate.temporalSafety.erasureReceipt context unit
          lawful.oldKeyEpochQ lawful.newKeyEpochQ ∧
      ∀ interval,
        Required interval →
        ∃ receipt,
          exposureProtocol.Observed
            receipt context unit lawful.newKeyEpochQ transition.newConfig
              certificate.temporalSafety.corruptionHorizon interval := by
  exact
    ⟨activation.active,
      certificate.activeVote.signerKeyEpochBound,
      certificate.activeVote.activeConfigEpochBound,
      inclusion.included,
      Nat.lt_of_le_of_lt
        certificate.temporalSafety.checkpointNoSlowerThanRefresh
        certificate.temporalSafety.refreshWithinCorruptionHorizon,
      certificate.temporalSafety.refreshObserved,
      certificate.temporalSafety.erasureObserved,
      fun _interval required =>
        certificate.exposure.coversRequired required⟩

/-- Every incomplete evidence constructor assesses to Await. -/
theorem incomplete_mobile_adversary_evidence_awaits
    {Safety : Type u}
    (residue : MobileAdversarySafetyResidue) :
    assessMobileAdversarySafety
        (MobileAdversaryEvidence.incomplete (Safety := Safety) residue) =
      MobileAdversaryAssessment.await residue := by
  rfl

end Residua.RCC.MobileAdversarySafety

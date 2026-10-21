import RCC.KeyEpochVote
import RCC.HistoricalInclusion

/-!
# RCC-54 Long-Range Safety after Key Retirement

Historical authority is the conjunction of two upstream certificates:

* an actual RCC-52 active key/config-epoch vote; and
* an actual RCC-53 inclusion in an RCC-45 finalized checkpoint.

A later compromise of a retired RCC-52 key may still produce cryptographically
valid bytes.  Those bytes never construct historical authority.  Logical
retirement and compromise observations are explicit, the compromise is ordered
after retirement inside one admitted window, and every presented checkpoint,
coordinate, item, and judgment is checked against the actual upstream
certificates.

Missing positive evidence is Await, not rejection and not authority.  A stale
checkpoint/fork, an incompatible item, or reuse of the retired runtime key as
the active runtime key is a typed refusal.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, declared axioms,
unchecked definitions, or hidden choice operators.
-/

namespace Residua.RCC.LongRangeSafety

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.HistoricalInclusion
open Residua.RCC.KeyEpochVote

universe u

/-- Named refusal/Await classes for the strengthened RCC-54 gate. -/
inductive LongRangeSafetyResidue
  | activeAuthorityEvidencePending
  | checkpointIdentityMismatch
  | staleCheckpointOrFork
  | checkpointCoordinateMismatch
  | checkpointItemMismatch
  | activeSlotMismatch
  | activeHeadMismatch
  | activeConfigEpochMismatch
  | activeKeyEpochMismatch
  | judgmentItemMismatch
  | retiredKeyReusedAsActive
  | retiredSignatureHasNoHistoryAuthority
  deriving DecidableEq, Repr

/--
RCC-52 and RCC-53 use different object domains.  This adapter is the explicit
realization boundary between finalized checkpoint coordinates and the complete
signed RCC-52 payload.
-/
structure HistoricalAuthorityAdapter
    (Q CheckpointQ Slot Head Config Coordinate Item : Type u) where
  slotQ : Slot → Q
  headQ : Head → Q
  configQ : Config → Q
  coordinateKeyEpochQ : Coordinate → Q
  itemJudgment : Item → CanonicalJudgment Q

/-- The exact history claim presented to the long-range authority gate. -/
structure PresentedHistoricalClaim
    (CheckpointQ Slot Head Config Coordinate Item : Type u) where
  checkpointQ : CheckpointQ
  slot : Slot
  head : Head
  config : Config
  coordinate : Coordinate
  item : Item

/--
The values mechanically projected from one actual RCC-52 release and one
actual RCC-53 finalized inclusion.
-/
structure HistoricalAuthorityFacts
    (Q CheckpointQ Slot Head Config Coordinate Item : Type u) where
  activePayload : KeyEpochVotePayload Q
  checkpointQ : CheckpointQ
  slot : Slot
  head : Head
  config : Config
  coordinate : Coordinate
  item : Item

/--
All equality evidence required before a presented claim may represent the
actual RCC-52/RCC-53 pair.  The type is indexed by both the mechanically
projected facts and the untrusted presentation.
-/
structure ExactHistoricalAuthorityBinding
    {Q CheckpointQ Slot Head Config Coordinate Item : Type u}
    (adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item)
    (facts :
      HistoricalAuthorityFacts
        Q CheckpointQ Slot Head Config Coordinate Item)
    (claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item) : Prop where
  checkpointBound : claim.checkpointQ = facts.checkpointQ
  slotBound : claim.slot = facts.slot
  headBound : claim.head = facts.head
  configBound : claim.config = facts.config
  coordinateBound : claim.coordinate = facts.coordinate
  itemBound : claim.item = facts.item
  activeSlotBound :
    facts.activePayload.slotQ = adapter.slotQ facts.slot
  activeHeadBound :
    facts.activePayload.parentHeadQ = adapter.headQ facts.head
  activeConfigBound :
    facts.activePayload.activeConfigEpochQ = adapter.configQ facts.config
  activeKeyEpochBound :
    facts.activePayload.signerKeyEpochQ =
      adapter.coordinateKeyEpochQ facts.coordinate
  judgmentBound :
    facts.activePayload.judgment = adapter.itemJudgment facts.item

/-- Result of checking one complete presented historical-authority packet. -/
inductive HistoricalAuthorityBindingAssessment
    {Q CheckpointQ Slot Head Config Coordinate Item : Type u}
    (adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item)
    (facts :
      HistoricalAuthorityFacts
        Q CheckpointQ Slot Head Config Coordinate Item)
    (claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item)
  | authority :
      ExactHistoricalAuthorityBinding adapter facts claim →
      HistoricalAuthorityBindingAssessment adapter facts claim
  | refuse :
      LongRangeSafetyResidue →
      HistoricalAuthorityBindingAssessment adapter facts claim

/--
Executable equality gate.  Head or config drift is the stale-checkpoint/fork
class; each remaining mismatch retains a distinct typed refusal.
-/
def verifyHistoricalAuthorityBinding
    {Q CheckpointQ Slot Head Config Coordinate Item : Type u}
    [DecidableEq Q] [DecidableEq CheckpointQ] [DecidableEq Slot]
    [DecidableEq Head] [DecidableEq Config] [DecidableEq Coordinate]
    [DecidableEq Item]
    (adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item)
    (facts :
      HistoricalAuthorityFacts
        Q CheckpointQ Slot Head Config Coordinate Item)
    (claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item) :
    HistoricalAuthorityBindingAssessment adapter facts claim :=
  if checkpointBound : claim.checkpointQ = facts.checkpointQ then
    if slotBound : claim.slot = facts.slot then
      if headBound : claim.head = facts.head then
        if configBound : claim.config = facts.config then
          if coordinateBound : claim.coordinate = facts.coordinate then
            if itemBound : claim.item = facts.item then
              if activeSlotBound :
                  facts.activePayload.slotQ = adapter.slotQ facts.slot then
                if activeHeadBound :
                    facts.activePayload.parentHeadQ =
                      adapter.headQ facts.head then
                  if activeConfigBound :
                      facts.activePayload.activeConfigEpochQ =
                        adapter.configQ facts.config then
                    if activeKeyEpochBound :
                        facts.activePayload.signerKeyEpochQ =
                          adapter.coordinateKeyEpochQ facts.coordinate then
                      if judgmentBound :
                          facts.activePayload.judgment =
                            adapter.itemJudgment facts.item then
                        .authority {
                          checkpointBound := checkpointBound
                          slotBound := slotBound
                          headBound := headBound
                          configBound := configBound
                          coordinateBound := coordinateBound
                          itemBound := itemBound
                          activeSlotBound := activeSlotBound
                          activeHeadBound := activeHeadBound
                          activeConfigBound := activeConfigBound
                          activeKeyEpochBound := activeKeyEpochBound
                          judgmentBound := judgmentBound
                        }
                      else
                        .refuse .judgmentItemMismatch
                    else
                      .refuse .activeKeyEpochMismatch
                  else
                    .refuse .activeConfigEpochMismatch
                else
                  .refuse .activeHeadMismatch
              else
                .refuse .activeSlotMismatch
            else
              .refuse .checkpointItemMismatch
          else
            .refuse .checkpointCoordinateMismatch
        else
          .refuse .staleCheckpointOrFork
      else
        .refuse .staleCheckpointOrFork
    else
      .refuse .activeSlotMismatch
  else
    .refuse .checkpointIdentityMismatch

/-! ## Actual RCC-52 plus RCC-53 authority -/

/--
The only positive historical-authority object.  Its fields are the actual
upstream certificates; callers cannot substitute a boolean active-key claim
or a caller-supplied checkpoint fact.
-/
structure ActualHistoricalAuthority
    {Q CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition HistoryJudgment Generation Epoch EffectSlot Occurrence
      FailureName EventQ : Type u}
    {TransitionAuthorityEvidence : Proposal Q Q Q → Type u}
    {HistoryAuthorityEvidence :
      Proposal Slot Head HistoryJudgment → Type u}
    [DecidableEq Q] [DecidableEq Head] [DecidableEq Generation]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {transitionAdapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state}
    {activationSlot activationHead : Q} {activationRound : Nat}
    {activation :
      AuthorizedActivationEvidence
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state transition envelope
          activationSlot activationHead activationRound .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {activeRelease : ReleasedSignature Q scheme}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {environment :
      AdmissionEnvironment
        Slot Head HistoryJudgment HistoryAuthorityEvidence Generation Epoch
          EffectSlot Occurrence FailureName EventQ}
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
    (checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition)
    (ItemEvidence : Item → Type u)
    (checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate)
    (coordinate : Coordinate)
    (item : Item)
    (adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item) where
  active :
    KeyEpochVoteCertificate
      activation lawful registry activeRelease
  inclusion :
    FinalizedHistoricalInclusion
      checkpointProtocol ItemEvidence checkpoint coordinate item
  claim :
    PresentedHistoricalClaim
      CheckpointQ Slot Head Config Coordinate Item
  binding :
    ExactHistoricalAuthorityBinding adapter {
      activePayload := releasedKeyEpochPayload activeRelease
      checkpointQ := checkpoint.checkpointQ
      slot := closure.snapshot.slot
      head := closure.snapshot.head
      config := closure.snapshot.config
      coordinate := coordinate
      item := item
    } claim

/-! ## Logical retirement and later compromise -/

/--
Logical time is supplied only through admitted receipts.  No theorem reads an
ambient clock.  Retirement names the actual RCC-44 old/new configuration and
removed signer epoch; compromise names the physical runtime key and the same
removed epoch inside one admitted observation window.
-/
structure CompromiseWindowProtocol
    (Q : Type u) (scheme : SignatureScheme Q)
    (Time Window : Type u) where
  RetirementReceipt : Type u
  CompromiseReceipt : Type u
  RetiredAt :
    RetirementReceipt → Q → Q → Q → Time → Prop
  CompromisedAt :
    CompromiseReceipt → scheme.Signature → Q → Q → Time → Window → Prop
  Before : Time → Time → Prop
  WithinWindow : Time → Window → Prop

/--
A later compromise consumes the actual RCC-52 retirement certificate for the
actual transition.  Valid signature bytes remain present in `retiredRelease`;
this object grants no active-key or checkpoint authority.
-/
structure LaterRetiredKeyCompromise
    {Q CheckpointQ Slot Head Config Coordinate Item Time Window : Type u}
    {TransitionAuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {transitionAdapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state}
    {activationSlot activationHead : Q} {activationRound : Nat}
    {activation :
      AuthorizedActivationEvidence
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state transition envelope
          activationSlot activationHead activationRound .new}
    {lawful : LawfulKeyEpochTransition transition}
    {scheme : SignatureScheme Q}
    {retiredRelease : ReleasedSignature Q scheme}
    (protocol : CompromiseWindowProtocol Q scheme Time Window)
    (claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item) where
  retired :
    RetiredKeyEpochCertificate activation lawful retiredRelease
  retirementTime : Time
  compromiseTime : Time
  observationWindow : Window
  retirementReceipt : protocol.RetirementReceipt
  retiredObserved :
    protocol.RetiredAt retirementReceipt
      transition.oldConfig transition.newConfig lawful.oldKeyEpochQ
      retirementTime
  compromiseReceipt : protocol.CompromiseReceipt
  compromisedObserved :
    protocol.CompromisedAt compromiseReceipt
      retiredRelease.envelope.signatureQ retiredRelease.runtime.keyQ
      lawful.oldKeyEpochQ compromiseTime observationWindow
  laterThanRetirement :
    protocol.Before retirementTime compromiseTime
  compromiseInWindow :
    protocol.WithinWindow compromiseTime observationWindow

/-- A retired claim has no authority constructor by construction. -/
inductive RetiredClaimAssessment (Attempt : Type u)
  | refuse :
      Attempt → LongRangeSafetyResidue →
      RetiredClaimAssessment Attempt

/--
Mechanical comparison of a later retired-key claim with the actual canonical
authority.  Even an exact replay ends in the named no-authority refusal.
-/
def assessRetiredClaim
    {Q CheckpointQ Slot Head Config Coordinate Item : Type u}
    {Attempt :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item → Type u}
    [DecidableEq Q] [DecidableEq CheckpointQ] [DecidableEq Slot]
    [DecidableEq Head] [DecidableEq Config] [DecidableEq Coordinate]
    [DecidableEq Item]
    (adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item)
    (activeRuntimeKey retiredRuntimeKey : Q)
    (canonicalClaim retiredClaim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item)
    (retiredJudgment : CanonicalJudgment Q)
    (attempt : Attempt retiredClaim) :
    RetiredClaimAssessment (Attempt retiredClaim) :=
  if _sameRuntimeKey : retiredRuntimeKey = activeRuntimeKey then
    .refuse attempt .retiredKeyReusedAsActive
  else if _sameCheckpoint : retiredClaim.checkpointQ =
      canonicalClaim.checkpointQ then
    if _sameSlot : retiredClaim.slot = canonicalClaim.slot then
      if _sameHead : retiredClaim.head = canonicalClaim.head then
        if _sameConfig : retiredClaim.config = canonicalClaim.config then
          if _sameCoordinate :
              retiredClaim.coordinate = canonicalClaim.coordinate then
            if _sameItem : retiredClaim.item = canonicalClaim.item then
              if _sameJudgment :
                  retiredJudgment =
                    adapter.itemJudgment retiredClaim.item then
                .refuse attempt .retiredSignatureHasNoHistoryAuthority
              else
                .refuse attempt .judgmentItemMismatch
            else
              .refuse attempt .checkpointItemMismatch
          else
            .refuse attempt .checkpointCoordinateMismatch
        else
          .refuse attempt .staleCheckpointOrFork
      else
        .refuse attempt .staleCheckpointOrFork
    else
      .refuse attempt .activeSlotMismatch
  else
    .refuse attempt .checkpointIdentityMismatch

/-- Final same-epoch polarity: absent authority only Awaits. -/
inductive LongRangeAuthorityAssessment (Authority : Type u)
  | authority :
      Authority → LongRangeAuthorityAssessment Authority
  | await :
      LongRangeSafetyResidue → LongRangeAuthorityAssessment Authority

/--
Only an actual proof-carrying authority object can inhabit the positive branch.
Retired attempts are assessed separately and cannot be promoted by this gate.
-/
def assessLongRangeAuthority
    {Authority : Type u}
    (authority? : Option Authority) :
    LongRangeAuthorityAssessment Authority :=
  match authority? with
  | some authority => .authority authority
  | none => .await .activeAuthorityEvidencePending

/-! ## Load-bearing bridge theorems -/

/-- Positive authority retains both actual upstream certificates. -/
theorem historical_authority_consumes_rcc52_and_rcc53
    {Q CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
      Partition HistoryJudgment Generation Epoch EffectSlot Occurrence
      FailureName EventQ : Type u}
    {TransitionAuthorityEvidence : Proposal Q Q Q → Type u}
    {HistoryAuthorityEvidence :
      Proposal Slot Head HistoryJudgment → Type u}
    [DecidableEq Q] [DecidableEq Head] [DecidableEq Generation]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {transitionAdapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state}
    {activationSlot activationHead : Q} {activationRound : Nat}
    {activation :
      AuthorizedActivationEvidence
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state transition envelope
          activationSlot activationHead activationRound .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {activeRelease : ReleasedSignature Q scheme}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {environment :
      AdmissionEnvironment
        Slot Head HistoryJudgment HistoryAuthorityEvidence Generation Epoch
          EffectSlot Occurrence FailureName EventQ}
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
    {checkpointProtocol :
      CheckpointInclusionProtocol
        CheckpointQ Coordinate Item Slot Head Config SourceAuthority Watermark
          Partition}
    {ItemEvidence : Item → Type u}
    {checkpoint :
      SealedHistoricalCheckpoint
        checkpointProtocol closure claimedCoordinate}
    {coordinate : Coordinate} {item : Item}
    {adapter :
      HistoricalAuthorityAdapter
        Q CheckpointQ Slot Head Config Coordinate Item}
    (authority :
      ActualHistoricalAuthority
        (TransitionAuthorityEvidence := TransitionAuthorityEvidence)
        (HistoryAuthorityEvidence := HistoryAuthorityEvidence)
        (jointProtocol := jointProtocol)
        (spec := spec)
        (equivalence := equivalence)
        (transitionAdapter := transitionAdapter)
        (state := state)
        (transition := transition)
        (envelope := envelope)
        (activation := activation)
        (lawful := lawful)
        (registry := registry)
        (scheme := scheme)
        (activeRelease := activeRelease)
        (history := history)
        (environment := environment)
        (ConfigLawful := ConfigLawful)
        (sourceProtocol := sourceProtocol)
        (ConfigStable := ConfigStable)
        (closure := closure)
        checkpointProtocol ItemEvidence checkpoint coordinate item adapter) :
    Nonempty
        (KeyEpochVoteCertificate
          activation lawful registry activeRelease) ∧
      Nonempty
          (FinalizedHistoricalInclusion
            checkpointProtocol ItemEvidence checkpoint coordinate item) ∧
        checkpointProtocol.InCheckpoint
          checkpoint.checkpointQ coordinate item :=
  ⟨⟨authority.active⟩, ⟨authority.inclusion⟩,
    finalized_historical_inclusion_sound authority.inclusion⟩

/-- The old release retains ordinary cryptographic validity after compromise. -/
theorem later_compromise_signature_remains_cryptographically_valid
    {Q CheckpointQ Slot Head Config Coordinate Item Time Window : Type u}
    {TransitionAuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {transitionAdapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state}
    {activationSlot activationHead : Q} {activationRound : Nat}
    {activation :
      AuthorizedActivationEvidence
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state transition envelope
          activationSlot activationHead activationRound .new}
    {lawful : LawfulKeyEpochTransition transition}
    {scheme : SignatureScheme Q}
    {retiredRelease : ReleasedSignature Q scheme}
    {protocol : CompromiseWindowProtocol Q scheme Time Window}
    {claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item}
    (_attempt :
      LaterRetiredKeyCompromise
        (TransitionAuthorityEvidence := TransitionAuthorityEvidence)
        (jointProtocol := jointProtocol)
        (spec := spec)
        (equivalence := equivalence)
        (transitionAdapter := transitionAdapter)
        (state := state)
        (transition := transition)
        (envelope := envelope)
        (activation := activation)
        (lawful := lawful)
        (scheme := scheme)
        (retiredRelease := retiredRelease)
        protocol claim) :
    scheme.Accepts retiredRelease.envelope.signatureQ
      (scheme.canonicalVoteMessage retiredRelease.envelope.signedVote) :=
  retiredRelease.validSignature.accepted

/--
An actual retired release cannot also acquire an RCC-52 active certificate in
the new phase.  The contradiction is the real membership-delta proof.
-/
theorem retired_release_cannot_gain_active_history_authority
    {Q CheckpointQ Slot Head Config Coordinate Item Time Window : Type u}
    {TransitionAuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {transitionAdapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state}
    {activationSlot activationHead : Q} {activationRound : Nat}
    {activation :
      AuthorizedActivationEvidence
        TransitionAuthorityEvidence jointProtocol spec equivalence
          transitionAdapter state transition envelope
          activationSlot activationHead activationRound .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {retiredRelease : ReleasedSignature Q scheme}
    {protocol : CompromiseWindowProtocol Q scheme Time Window}
    {claim :
      PresentedHistoricalClaim
        CheckpointQ Slot Head Config Coordinate Item}
    (attempt :
      LaterRetiredKeyCompromise
        (TransitionAuthorityEvidence := TransitionAuthorityEvidence)
        (jointProtocol := jointProtocol)
        (spec := spec)
        (equivalence := equivalence)
        (transitionAdapter := transitionAdapter)
        (state := state)
        (transition := transition)
        (envelope := envelope)
        (activation := activation)
        (lawful := lawful)
        (scheme := scheme)
        (retiredRelease := retiredRelease)
        protocol claim)
    (active :
      KeyEpochVoteCertificate
        activation lawful registry retiredRelease) :
    False :=
  active_and_retired_new_epoch_conflict active attempt.retired

end Residua.RCC.LongRangeSafety

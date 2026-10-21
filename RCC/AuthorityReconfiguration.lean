import RCC.AdmissionLinearizer

/-!
# RCC-44 Authority Reconfiguration

An authority transition binds both configurations, its activation coordinate,
round boundary, membership delta, and pre-state authority.  Authorization has
exactly two proof-carrying forms: a fixed-domain joint quorum or an actual
RCC-42 successful finalizer handoff.

This is a safety kernel.  Joint-quorum cryptography and runtime receipt truth
remain adapter obligations.  The kernel does not realize CAS/storage, effects,
process recovery, delivery, or liveness.  Slot is arbitrary; only the natural
round boundary is ordered.

Prelude-only Lean 4.14; no Mathlib and no proof placeholders.
-/

namespace Residua.RCC.AuthorityReconfiguration

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer

universe u

/-- Membership changes bound into one authority transition. -/
structure MembershipDelta (Member : Type u) where
  added : List Member
  removed : List Member
  deriving DecidableEq, Repr

/-- The complete authority-transition identity. -/
structure AuthorityTransition
    (Config Slot Head Authority Member : Type u) where
  oldConfig : Config
  newConfig : Config
  activationSlot : Slot
  activationHead : Head
  roundBoundary : Nat
  membershipDelta : MembershipDelta Member
  preStateAuthority : Authority
  deriving DecidableEq, Repr

/--
The deployment adapter defines joint-quorum receipt validity over the complete
transition.  Receipt relations alone are insufficient: a protocol must also
bind every jointly accepted transition into one coherent transition set and
prove that this set is single-valued at an activation slot/head/round boundary.
That law prevents permissive `True` relations from authorizing two conflicting
reconfigurations at one decision coordinate.
-/
structure JointQuorumProtocol
    (Config Slot Head Authority Member OldReceipt NewReceipt : Type u) where
  OldAccepts :
    OldReceipt → AuthorityTransition Config Slot Head Authority Member → Prop
  NewAccepts :
    NewReceipt → AuthorityTransition Config Slot Head Authority Member → Prop
  TransitionCoherent :
    AuthorityTransition Config Slot Head Authority Member → Prop
  jointBindsCoherent :
    ∀ {oldReceipt newReceipt transition},
      OldAccepts oldReceipt transition →
      NewAccepts newReceipt transition →
      TransitionCoherent transition
  coherentAtCoordinate :
    ∀ {first second},
      TransitionCoherent first →
      TransitionCoherent second →
      first.activationSlot = second.activationSlot →
      first.activationHead = second.activationHead →
      first.roundBoundary = second.roundBoundary →
      first = second

/-- Both old and new quorum domains accepted the same complete transition. -/
structure JointQuorumTransition
    {Config Slot Head Authority Member OldReceipt NewReceipt : Type u}
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (transition :
      AuthorityTransition Config Slot Head Authority Member) where
  oldReceipt : OldReceipt
  newReceipt : NewReceipt
  oldAccepted : protocol.OldAccepts oldReceipt transition
  newAccepted : protocol.NewAccepts newReceipt transition

/-- A joint-quorum certificate lands in the protocol's coherent transition set. -/
theorem JointQuorumTransition.transitionCoherent
    {Config Slot Head Authority Member OldReceipt NewReceipt : Type u}
    {protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt}
    {transition :
      AuthorityTransition Config Slot Head Authority Member}
    (certificate : JointQuorumTransition protocol transition) :
    protocol.TransitionCoherent transition :=
  protocol.jointBindsCoherent
    certificate.oldAccepted certificate.newAccepted

/--
Projection from an RCC-42 canonical judgment to the complete RCC-44 transition.
Equivalent finalized judgments must retain every transition coordinate.
-/
structure ReconfigurationJudgmentAdapter
    (Config Slot Head Authority Member Judgment : Type u)
    (equivalence : JudgmentEquivalence Judgment) where
  project :
    Judgment → AuthorityTransition Config Slot Head Authority Member
  equivalentBindsTransition :
    ∀ {first second},
      equivalence.Equivalent first second →
      project first = project second

/--
A unique finalized handoff contains the actual RCC-42 executable success chain,
not merely `FinalizedInState` or a caller-supplied finality predicate.
-/
structure FinalizedHandoff
    {Config Slot Head Authority Member Judgment Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (state : FencedWriterState Slot Head Judgment Generation)
    (transition :
      AuthorityTransition Config Slot Head Authority Member) where
  request :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation
  successful : SuccessfulFinalize spec equivalence state request
  transitionBound :
    adapter.project request.authorization.proposal.judgment = transition
  activationSlotBound :
    request.authorization.proposal.slot = transition.activationSlot
  activationHeadBound :
    request.authorization.proposal.expectedParent = transition.activationHead

/--
Two handoffs in one RCC-42 writer state and decision slot bind the same complete
transition.  The proof consumes RCC-42 same-slot finality uniqueness.
-/
theorem finalized_handoffs_same_state_same_slot_transition_equal
    {Config Slot Head Authority Member Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence}
    {state : FencedWriterState Slot Head Judgment Generation}
    {firstTransition secondTransition :
      AuthorityTransition Config Slot Head Authority Member}
    (first :
      FinalizedHandoff
        AuthorityEvidence spec equivalence adapter state firstTransition)
    (second :
      FinalizedHandoff
        AuthorityEvidence spec equivalence adapter state secondTransition)
    (sameSlot :
      first.request.authorization.proposal.slot =
        second.request.authorization.proposal.slot) :
    firstTransition = secondTransition := by
  have equivalentJudgments :=
    successful_finalizes_same_slot_equivalent
      spec equivalence state first.successful second.successful sameSlot
  have sameProjectedTransition :=
    adapter.equivalentBindsTransition equivalentJudgments
  exact first.transitionBound.symm.trans
    (sameProjectedTransition.trans second.transitionBound)

/--
The only admitted transition authorities in one fixed protocol/writer domain.
Callers cannot existentially replace that protocol or writer state.
-/
inductive TransitionAuthorization
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (state : FencedWriterState Slot Head Judgment Generation)
    (transition :
      AuthorityTransition Config Slot Head Authority Member) : Type u
  | jointQuorum :
      JointQuorumTransition protocol transition →
      TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter state transition
  | finalizedHandoff :
      FinalizedHandoff
        AuthorityEvidence spec equivalence adapter state transition →
      protocol.TransitionCoherent transition →
      TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter state transition

/-- Every authorization form is bound into the protocol's coherent set. -/
theorem TransitionAuthorization.transitionCoherent
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt}
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence}
    {state : FencedWriterState Slot Head Judgment Generation}
    {transition :
      AuthorityTransition Config Slot Head Authority Member}
    (authorization :
      TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter state transition) :
    protocol.TransitionCoherent transition := by
  cases authorization with
  | jointQuorum certificate =>
      exact certificate.transitionCoherent
  | finalizedHandoff _ coherent =>
      exact coherent

/--
Two authorized reconfigurations in one fixed protocol domain cannot conflict at
the same activation slot, head, and round boundary.  This covers joint/joint,
handoff/handoff, and mixed joint/handoff authorization forms.
-/
theorem authorized_transitions_same_coordinate_equal
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt}
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {first second :
      AuthorityTransition Config Slot Head Authority Member}
    (firstAuthorized :
      TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter firstState first)
    (secondAuthorized :
      TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter secondState second)
    (sameSlot : first.activationSlot = second.activationSlot)
    (sameHead : first.activationHead = second.activationHead)
    (sameRound : first.roundBoundary = second.roundBoundary) :
    first = second :=
  protocol.coherentAtCoordinate
    firstAuthorized.transitionCoherent
    secondAuthorized.transitionCoherent
    sameSlot sameHead sameRound

/-- Existential transition plus proof in one fixed authorization domain. -/
structure AuthorizedTransitionEnvelope
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (state : FencedWriterState Slot Head Judgment Generation) where
  transition :
    AuthorityTransition Config Slot Head Authority Member
  authorization :
    TransitionAuthorization
      AuthorityEvidence protocol spec equivalence adapter state transition

/-- Authority phase selected at the transition coordinate. -/
inductive AuthorityPhase
  | old
  | new
  deriving DecidableEq, Repr

/--
The old phase occupies rounds below the boundary; the new phase occupies the
boundary and later rounds.  Both are bound to the exact activation slot/head.
-/
inductive ActiveAt
    {Config Slot Head Authority Member : Type u}
    (transition :
      AuthorityTransition Config Slot Head Authority Member)
    (slot : Slot) (head : Head) (round : Nat) : AuthorityPhase → Prop
  | old :
      slot = transition.activationSlot →
      head = transition.activationHead →
      round < transition.roundBoundary →
      ActiveAt transition slot head round .old
  | new :
      slot = transition.activationSlot →
      head = transition.activationHead →
      transition.roundBoundary ≤ round →
      ActiveAt transition slot head round .new

/-- Old and new authority cannot both be active at one decision coordinate. -/
theorem old_and_new_not_simultaneously_active
    {Config Slot Head Authority Member : Type u}
    {transition :
      AuthorityTransition Config Slot Head Authority Member}
    {slot : Slot} {head : Head} {round : Nat} :
    ¬ (ActiveAt transition slot head round .old ∧
      ActiveAt transition slot head round .new) := by
  rintro ⟨oldActive, newActive⟩
  cases oldActive with
  | old _ _ beforeBoundary =>
      cases newActive with
      | new _ _ atOrAfterBoundary =>
          exact (Nat.not_lt_of_ge atOrAfterBoundary) beforeBoundary

/-- Caller claim presented to the activation gate. -/
inductive AuthorityClaim
  | old
  | new
  | both
  deriving DecidableEq, Repr

/-- Named RCC-44 refusal classes. -/
inductive ReconfigurationResidue
  | unboundTransitionContext
  | earlyNewStart
  | lateOldVote
  | overlap
  | disjointFinalization
  deriving DecidableEq, Repr

/--
Positive activation evidence retains both the fixed-domain authorization and
its equality to the transition being assessed.
-/
structure AuthorizedActivationEvidence
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (state : FencedWriterState Slot Head Judgment Generation)
    (transition :
      AuthorityTransition Config Slot Head Authority Member)
    (envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence protocol spec equivalence adapter state)
    (slot : Slot) (head : Head) (round : Nat)
    (phase : AuthorityPhase) : Type u where
  transitionBound : envelope.transition = transition
  active : ActiveAt transition slot head round phase

/-- Activation result with proof-carrying positive branches. -/
inductive ActivationAssessment
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (state : FencedWriterState Slot Head Judgment Generation)
    (transition :
      AuthorityTransition Config Slot Head Authority Member)
    (envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence protocol spec equivalence adapter state)
    (slot : Slot) (head : Head) (round : Nat) : Type u
  | activeOld :
      AuthorizedActivationEvidence
        AuthorityEvidence protocol spec equivalence adapter state
          transition envelope slot head round .old →
      ActivationAssessment
        AuthorityEvidence protocol spec equivalence adapter state
          transition envelope slot head round
  | activeNew :
      AuthorizedActivationEvidence
        AuthorityEvidence protocol spec equivalence adapter state
          transition envelope slot head round .new →
      ActivationAssessment
        AuthorityEvidence protocol spec equivalence adapter state
          transition envelope slot head round
  | refuse :
      ReconfigurationResidue →
      ActivationAssessment
        AuthorityEvidence protocol spec equivalence adapter state
          transition envelope slot head round

/--
Check an authorized transition envelope against one expected transition and
activation coordinate.  Early/late refer only to the natural round boundary.
-/
def assessActivation
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Config] [DecidableEq Slot] [DecidableEq Head]
    [DecidableEq Authority] [DecidableEq Member] [DecidableEq Generation]
    {protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt}
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence}
    {state : FencedWriterState Slot Head Judgment Generation}
    (expected :
      AuthorityTransition Config Slot Head Authority Member)
    (envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence protocol spec equivalence adapter state)
    (slot : Slot) (head : Head) (round : Nat) (claim : AuthorityClaim) :
    ActivationAssessment
      AuthorityEvidence protocol spec equivalence adapter state
        expected envelope slot head round :=
  if transitionBound : envelope.transition = expected then
    if slotBound : slot = expected.activationSlot then
      if headBound : head = expected.activationHead then
        match claim with
        | .both => .refuse .overlap
        | .old =>
            if beforeBoundary : round < expected.roundBoundary then
              .activeOld
                ⟨transitionBound, .old slotBound headBound beforeBoundary⟩
            else
              .refuse .lateOldVote
        | .new =>
            if atOrAfterBoundary : expected.roundBoundary ≤ round then
              .activeNew
                ⟨transitionBound, .new slotBound headBound atOrAfterBoundary⟩
            else
              .refuse .earlyNewStart
      else
        .refuse .unboundTransitionContext
    else
      .refuse .unboundTransitionContext
  else
    .refuse .unboundTransitionContext

/--
One locally successful lane.  It carries an actual RCC-42 success but no claim
that a second lane shares its writer state or authorization domain.
-/
structure LocalSuccessfulFinalize
    (Config : Type u)
    {Slot Head Authority Member Judgment Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (transition :
      AuthorityTransition Config Slot Head Authority Member) where
  claimedConfig : Config
  state : FencedWriterState Slot Head Judgment Generation
  request :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation
  successful : SuccessfulFinalize spec equivalence state request
  transitionBound :
    adapter.project request.authorization.proposal.judgment = transition

/--
Two locally successful lanes are a disjoint-finalization attempt only when
proof also shows that the candidate lacks joint/handoff authorization in the
fixed shared domain.  Different writer states alone do not establish fault.
-/
structure DisjointFinalizationAttempt
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt)
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence)
    (sharedState : FencedWriterState Slot Head Judgment Generation)
    (transition :
      AuthorityTransition Config Slot Head Authority Member) where
  oldLane :
    LocalSuccessfulFinalize
      (Slot := Slot) (Head := Head) (Authority := Authority)
      (Member := Member) (Judgment := Judgment) (Generation := Generation)
      Config AuthorityEvidence spec equivalence adapter transition
  newLane :
    LocalSuccessfulFinalize
      (Slot := Slot) (Head := Head) (Authority := Authority)
      (Member := Member) (Judgment := Judgment) (Generation := Generation)
      Config AuthorityEvidence spec equivalence adapter transition
  oldConfigBound : oldLane.claimedConfig = transition.oldConfig
  newConfigBound : newLane.claimedConfig = transition.newConfig
  noSharedAuthorization :
    TransitionAuthorization
        AuthorityEvidence protocol spec equivalence adapter sharedState transition →
      False

/-- Shared assessment surface for transition admission/refusal. -/
inductive ReconfigurationAssessment
  | refuse : ReconfigurationResidue → ReconfigurationAssessment
  deriving DecidableEq, Repr

/--
Refuse two locally successful lanes only because the attempt carries proof that
the fixed shared authorization domain admits neither joint quorum nor handoff.
-/
def assessDisjointFinalization
    {Config Slot Head Authority Member OldReceipt NewReceipt Judgment
      Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {protocol :
      JointQuorumProtocol
        Config Slot Head Authority Member OldReceipt NewReceipt}
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {adapter :
      ReconfigurationJudgmentAdapter
        Config Slot Head Authority Member Judgment equivalence}
    {sharedState : FencedWriterState Slot Head Judgment Generation}
    {transition :
      AuthorityTransition Config Slot Head Authority Member}
    (_attempt :
      DisjointFinalizationAttempt
        (Config := Config) (Slot := Slot) (Head := Head)
        (Authority := Authority) (Member := Member)
        (OldReceipt := OldReceipt) (NewReceipt := NewReceipt)
        (Judgment := Judgment) (Generation := Generation)
        AuthorityEvidence protocol spec equivalence adapter sharedState
          transition) :
    ReconfigurationAssessment :=
  .refuse .disjointFinalization

end Residua.RCC.AuthorityReconfiguration

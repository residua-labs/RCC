import RCC.AuthorityReconfiguration

/-!
# RCC-44 Authority Reconfiguration Countermodels

Only a fixed-domain joint quorum or an actual RCC-42 successful finalizer
handoff authorizes one complete transition.  Local finality in disjoint lanes
does not create a shared transition authority.
-/

namespace Residua.RCC.AuthorityReconfiguration.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration

inductive Config
  | old | new | other
  deriving DecidableEq, Repr

inductive Slot
  | activation | other
  deriving DecidableEq, Repr

inductive Head
  | canonical | fork
  deriving DecidableEq, Repr

inductive Authority
  | oldAuthority
  deriving DecidableEq, Repr

inductive Member
  | oldMember | newMember
  deriving DecidableEq, Repr

inductive OldReceipt
  | oldQC | unrelated
  deriving DecidableEq, Repr

inductive NewReceipt
  | newQC | unrelated
  deriving DecidableEq, Repr

inductive Judgment
  | authorizedTransition | disjointTransition
  deriving DecidableEq, Repr

structure AuthorityEvidence
    (proposal : Proposal Slot Head Judgment) : Type where
  slotBound : proposal.slot = .activation
  parentBound : proposal.expectedParent = .canonical

inductive Generation
  | current
  deriving DecidableEq, Repr

def transition :
    AuthorityTransition Config Slot Head Authority Member where
  oldConfig := .old
  newConfig := .new
  activationSlot := .activation
  activationHead := .canonical
  roundBoundary := 10
  membershipDelta := {
    added := [.newMember]
    removed := [.oldMember]
  }
  preStateAuthority := .oldAuthority

def disjointTransition :
    AuthorityTransition Config Slot Head Authority Member where
  oldConfig := .old
  newConfig := .other
  activationSlot := .activation
  activationHead := .canonical
  roundBoundary := 10
  membershipDelta := {
    added := []
    removed := [.oldMember]
  }
  preStateAuthority := .oldAuthority

def jointProtocol :
    JointQuorumProtocol
      Config Slot Head Authority Member OldReceipt NewReceipt where
  OldAccepts receipt candidate :=
    receipt = .oldQC ∧ candidate = transition
  NewAccepts receipt candidate :=
    receipt = .newQC ∧ candidate = transition
  TransitionCoherent candidate := candidate = transition
  jointBindsCoherent := by
    intro oldReceipt newReceipt candidate oldAccepted _newAccepted
    exact oldAccepted.2
  coherentAtCoordinate := by
    intro first second firstCoherent secondCoherent _sameSlot _sameHead
      _sameRound
    exact firstCoherent.trans secondCoherent.symm

def jointEvidence : JointQuorumTransition jointProtocol transition where
  oldReceipt := .oldQC
  newReceipt := .newQC
  oldAccepted := ⟨rfl, rfl⟩
  newAccepted := ⟨rfl, rfl⟩

def writerSpec : FencedWriterSpec Slot Head where
  slotParent := fun _ => .canonical

def judgmentEq : JudgmentEquivalence Judgment where
  Equivalent := Eq
  refl := by intro _; rfl
  symm := by intro _ _ equality; exact equality.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide := fun first second => inferInstanceAs (Decidable (first = second))

def judgmentAdapter :
    ReconfigurationJudgmentAdapter
      Config Slot Head Authority Member Judgment judgmentEq where
  project judgment :=
    match judgment with
    | .authorizedTransition => transition
    | .disjointTransition => disjointTransition
  equivalentBindsTransition := by
    intro first second equality
    cases equality
    rfl

def authorizedProposal : Proposal Slot Head Judgment :=
  ⟨.activation, .canonical, .authorizedTransition⟩

def authorizedRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨⟨authorizedProposal, ⟨rfl, rfl⟩⟩, .current⟩

def writerState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun
    | .activation => some .authorizedTransition
    | .other => none

def authorizedOutput :
    FencedFinalizeOutput
      writerSpec judgmentEq writerState authorizedRequest where
  finality := {
    authorization := authorizedRequest.authorization
    linearizationEvidence := {
      generation := .current
      slot := .activation
      parentHead := .canonical
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .authorizedTransition, rfl, rfl⟩

def authorizedSuccess :
    SuccessfulFinalize writerSpec judgmentEq writerState authorizedRequest where
  output := authorizedOutput
  accepted := by rfl

def finalizedHandoff :
    FinalizedHandoff
      AuthorityEvidence writerSpec judgmentEq judgmentAdapter writerState
        transition where
  request := authorizedRequest
  successful := authorizedSuccess
  transitionBound := rfl
  activationSlotBound := rfl
  activationHeadBound := rfl

abbrev TestAuthorization
    (candidate :
      AuthorityTransition Config Slot Head Authority Member) :=
  TransitionAuthorization
    AuthorityEvidence jointProtocol writerSpec judgmentEq judgmentAdapter
      writerState candidate

theorem joint_quorum_is_authorized :
    Nonempty (TestAuthorization transition) :=
  ⟨.jointQuorum jointEvidence⟩

theorem actual_successful_finalize_handoff_is_authorized :
    Nonempty (TestAuthorization transition) :=
  ⟨.finalizedHandoff finalizedHandoff rfl⟩

theorem finalized_handoff_consumes_actual_success :
    finalizedHandoff.successful.accepted =
      (show fencedFinalize writerSpec judgmentEq writerState authorizedRequest =
        .Ok authorizedOutput from rfl) := by
  rfl

theorem same_state_handoffs_bind_one_transition
    (other :
      FinalizedHandoff
        AuthorityEvidence writerSpec judgmentEq judgmentAdapter writerState
          transition) :
    transition = transition :=
  finalized_handoffs_same_state_same_slot_transition_equal
    finalizedHandoff other
      (finalizedHandoff.activationSlotBound.trans
        other.activationSlotBound.symm)

def jointEnvelope :
    AuthorizedTransitionEnvelope
      AuthorityEvidence jointProtocol writerSpec judgmentEq judgmentAdapter
        writerState where
  transition := transition
  authorization := .jointQuorum jointEvidence

def handoffEnvelope :
    AuthorizedTransitionEnvelope
      AuthorityEvidence jointProtocol writerSpec judgmentEq judgmentAdapter
        writerState where
  transition := transition
  authorization := .finalizedHandoff finalizedHandoff rfl

theorem old_before_boundary_is_active :
    (match assessActivation transition jointEnvelope .activation .canonical 9
        .old with
      | .activeOld _ => true
      | _ => false) = true := by
  rfl

theorem new_at_boundary_is_active :
    (match assessActivation transition handoffEnvelope .activation .canonical 10
        .new with
      | .activeNew _ => true
      | _ => false) = true := by
  rfl

theorem old_and_new_never_overlap :
    ¬ (ActiveAt transition .activation .canonical 10 .old ∧
      ActiveAt transition .activation .canonical 10 .new) :=
  old_and_new_not_simultaneously_active

theorem early_new_start_is_refused :
    (match assessActivation transition jointEnvelope .activation .canonical 9
        .new with
      | .refuse .earlyNewStart => true
      | _ => false) = true := by
  rfl

theorem late_old_vote_is_refused :
    (match assessActivation transition jointEnvelope .activation .canonical 10
        .old with
      | .refuse .lateOldVote => true
      | _ => false) = true := by
  rfl

theorem overlap_is_refused :
    (match assessActivation transition jointEnvelope .activation .canonical 9
        .both with
      | .refuse .overlap => true
      | _ => false) = true := by
  rfl

theorem unbound_slot_is_refused :
    (match assessActivation transition jointEnvelope .other .canonical 9
        .old with
      | .refuse .unboundTransitionContext => true
      | _ => false) = true := by
  rfl

theorem unbound_head_is_refused :
    (match assessActivation transition jointEnvelope .activation .fork 9
        .old with
      | .refuse .unboundTransitionContext => true
      | _ => false) = true := by
  rfl

theorem unbound_transition_context_is_refused :
    (match assessActivation disjointTransition jointEnvelope
        .activation .canonical 10 .new with
      | .refuse .unboundTransitionContext => true
      | _ => false) = true := by
  rfl

def disjointProposal : Proposal Slot Head Judgment :=
  ⟨.activation, .canonical, .disjointTransition⟩

def disjointRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨⟨disjointProposal, ⟨rfl, rfl⟩⟩, .current⟩

def oldLaneState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun
    | .activation => some .disjointTransition
    | .other => none

def newLaneState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .canonical
  decisions := fun _ => some .disjointTransition

def oldLaneOutput :
    FencedFinalizeOutput
      writerSpec judgmentEq oldLaneState disjointRequest where
  finality := {
    authorization := disjointRequest.authorization
    linearizationEvidence := {
      generation := .current
      slot := .activation
      parentHead := .canonical
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .disjointTransition, rfl, rfl⟩

def newLaneOutput :
    FencedFinalizeOutput
      writerSpec judgmentEq newLaneState disjointRequest where
  finality := {
    authorization := disjointRequest.authorization
    linearizationEvidence := {
      generation := .current
      slot := .activation
      parentHead := .canonical
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .disjointTransition, rfl, rfl⟩

def oldLaneSuccess :
    SuccessfulFinalize writerSpec judgmentEq oldLaneState disjointRequest where
  output := oldLaneOutput
  accepted := by rfl

def newLaneSuccess :
    SuccessfulFinalize writerSpec judgmentEq newLaneState disjointRequest where
  output := newLaneOutput
  accepted := by rfl

def oldLocalLane :
    LocalSuccessfulFinalize
      (Slot := Slot) (Head := Head) (Authority := Authority)
      (Member := Member) (Judgment := Judgment) (Generation := Generation)
      Config AuthorityEvidence writerSpec judgmentEq judgmentAdapter
        disjointTransition where
  claimedConfig := .old
  state := oldLaneState
  request := disjointRequest
  successful := oldLaneSuccess
  transitionBound := rfl

def newLocalLane :
    LocalSuccessfulFinalize
      (Slot := Slot) (Head := Head) (Authority := Authority)
      (Member := Member) (Judgment := Judgment) (Generation := Generation)
      Config AuthorityEvidence writerSpec judgmentEq judgmentAdapter
        disjointTransition where
  claimedConfig := .other
  state := newLaneState
  request := disjointRequest
  successful := newLaneSuccess
  transitionBound := rfl

theorem disjoint_transition_has_no_shared_authorization :
    TestAuthorization disjointTransition → False := by
  intro authorization
  cases authorization with
  | jointQuorum evidence =>
      exact (by decide : disjointTransition ≠ transition)
        evidence.oldAccepted.2
  | finalizedHandoff handoff _coherent =>
      have sameTransition :
          disjointTransition = transition :=
        finalized_handoffs_same_state_same_slot_transition_equal
          handoff finalizedHandoff
            (handoff.activationSlotBound.trans
              finalizedHandoff.activationSlotBound.symm)
      exact (by decide : disjointTransition ≠ transition) sameTransition

/--
The old protocol shape `OldAccepts := True; NewAccepts := True` cannot be made
lawful in a domain containing two distinct transitions at the same activation
coordinate.  The missing inhabitant is exactly the transition-coherence proof.
-/
theorem constant_true_bare_relations_cannot_form_lawful_protocol :
    ¬ ∃ protocol :
        JointQuorumProtocol
          Config Slot Head Authority Member OldReceipt NewReceipt,
      (∀ receipt candidate, protocol.OldAccepts receipt candidate) ∧
      (∀ receipt candidate, protocol.NewAccepts receipt candidate) := by
  rintro ⟨protocol, oldAlways, newAlways⟩
  have firstCoherent : protocol.TransitionCoherent transition :=
    protocol.jointBindsCoherent
      (oldAlways .oldQC transition) (newAlways .newQC transition)
  have secondCoherent : protocol.TransitionCoherent disjointTransition :=
    protocol.jointBindsCoherent
      (oldAlways .oldQC disjointTransition)
      (newAlways .newQC disjointTransition)
  have sameTransition : transition = disjointTransition :=
    protocol.coherentAtCoordinate
      firstCoherent secondCoherent rfl rfl rfl
  exact (by decide : transition ≠ disjointTransition) sameTransition

theorem authorized_fixture_coordinate_is_unique
    {candidate : AuthorityTransition Config Slot Head Authority Member}
    (authorization : TestAuthorization candidate)
    (sameSlot : candidate.activationSlot = transition.activationSlot)
    (sameHead : candidate.activationHead = transition.activationHead)
    (sameRound : candidate.roundBoundary = transition.roundBoundary) :
    candidate = transition :=
  authorized_transitions_same_coordinate_equal
    authorization
    (TransitionAuthorization.finalizedHandoff finalizedHandoff rfl)
    sameSlot sameHead sameRound

def disjointAttempt :
    DisjointFinalizationAttempt
      AuthorityEvidence jointProtocol writerSpec judgmentEq judgmentAdapter
        writerState disjointTransition where
  oldLane := oldLocalLane
  newLane := newLocalLane
  oldConfigBound := rfl
  newConfigBound := rfl
  noSharedAuthorization := disjoint_transition_has_no_shared_authorization

theorem disjoint_lanes_each_have_actual_success :
    oldLocalLane.successful.accepted =
        (show fencedFinalize writerSpec judgmentEq oldLaneState disjointRequest =
          .Ok oldLaneOutput from rfl) ∧
      newLocalLane.successful.accepted =
        (show fencedFinalize writerSpec judgmentEq newLaneState disjointRequest =
          .Ok newLaneOutput from rfl) := by
  exact ⟨rfl, rfl⟩

theorem disjoint_local_finalizations_without_shared_domain_are_refused :
    (match assessDisjointFinalization disjointAttempt with
      | .refuse .disjointFinalization => true
      | _ => false) = true := by
  rfl

#print axioms joint_quorum_is_authorized
#print axioms actual_successful_finalize_handoff_is_authorized
#print axioms finalized_handoff_consumes_actual_success
#print axioms same_state_handoffs_bind_one_transition
#print axioms old_and_new_never_overlap
#print axioms disjoint_lanes_each_have_actual_success
#print axioms finalized_handoffs_same_state_same_slot_transition_equal
#print axioms old_and_new_not_simultaneously_active
#print axioms authorized_transitions_same_coordinate_equal
#print axioms authorized_fixture_coordinate_is_unique
#print axioms constant_true_bare_relations_cannot_form_lawful_protocol
#print axioms assessActivation
#print axioms assessDisjointFinalization

end Residua.RCC.AuthorityReconfiguration.Tests

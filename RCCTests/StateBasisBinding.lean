import RCC.StateBasisBinding
import RCCTests.GlobalSerializability

/-!
# RCC-47 State-Basis Binding Adapter Countermodels

The positive fixture consumes the actual RCC-42 successful finalizer and RCC-45
finalized-head event already used by the global-serializability tests.

CM-RCC47-BASIS-01 demonstrates the missing old bridge: a valid semantic
`GlobalSerializability.StateBasisBinding` for `genesis` can coexist with host
CAS/append receipts that actually consume `headA`, because the old carrier has
no receipt fields.  The new adapter rejects the same stale pre-state.
-/

namespace Residua.RCC.StateBasisBinding.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.StateBasisBinding

/-- Canonical and stale host observations for the test mutation adapter. -/
inductive CASReceipt
  | canonical
  | stale
  deriving DecidableEq

inductive AppendReceipt
  | canonical
  | stale
  deriving DecidableEq

/--
The host admits both observations.  Safety therefore cannot come from an
opaque `accepted` tag; it comes from binding the projected receipt coordinates
to one proof-carrying state basis.
-/
def mutationAdapter : MutationAdapter Head Slot Head Judgment where
  CASReceipt := CASReceipt
  AppendReceipt := AppendReceipt
  casProposal := fun _ => proposalA
  casExpectedParent
    | .canonical => .genesis
    | .stale => .headA
  CASAccepted := fun _ => True
  appendProposal := fun _ => proposalA
  appendExpectedParent
    | .canonical => .genesis
    | .stale => .headA
  appendPostState
    | .canonical => .headA
    | .stale => .headB
  AppendAccepted := fun _ => True

/--
One non-vacuous canonical RCC-42 evolution for the exact writer snapshot
retained by `actualFinalizedEvent`.
-/
def globalLinearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Nat
        actualFinalizedEvent.environment.writerSpec
        actualFinalizedEvent.environment.equivalence where
  Precedes := fun first second => first ≤ second
  precedesRefl := Nat.le_refl
  precedesTrans := by
    intro first second third firstBeforeSecond secondBeforeThird
    exact Nat.le_trans firstBeforeSecond secondBeforeThird
  comparable := Nat.le_total
  activeGeneration := fun _ _ => .current
  canonicalDecision :=
    fun _ _ => actualFinalizedEvent.environment.writerState.decisions
  decisionPreserved := by
    intro first second head slot judgment _ committed
    exact committed

def canonicalWriterSnapshot :
    CanonicalWriterSnapshot
      globalLinearizer 0 actualFinalizedEvent.environment.writerState where
  generationBound := rfl
  decisionBound := by
    intro slot
    rfl

def globalFinality :
    GloballySuccessfulFinalize
      globalLinearizer 0 actualFinalizedEvent.environment.writerState
        actualFinalizedEvent.certificate.admission.finalizeRequest where
  snapshot := canonicalWriterSnapshot
  localSuccess := actualFinalizedEvent.certificate.admission.finalizeSuccess

def actualStateBasis : StateBasis surface Head.genesis where
  root := .genesis
  rootBound := rfl

def actualMutation :
    BasisBoundMutation
      surface mutationAdapter .genesis actualStateBasis
        actualFinalizedEvent.proposal where
  casReceipt := .canonical
  casAccepted := True.intro
  casProposalBound := rfl
  casBasisBound := rfl
  appendReceipt := .canonical
  appendAccepted := True.intro
  appendProposalBound := rfl
  appendBasisBound := rfl
  appendPostStateBound := rfl

/-- Positive inhabitant: RCC-42, RCC-45, CAS, append, and state basis all agree. -/
def actualFinalizedMutation :
    FinalizedStateMutation
      surface mutationAdapter 0 .genesis actualFinalizedEvent globalLinearizer where
  basis := actualStateBasis
  basisParentBound := rfl
  globalFinality := globalFinality
  globalMatchesRCC45 := rfl
  mutation := actualMutation
  postHeadBound := rfl

theorem actual_adapter_refines_original_rcc47 :
    Nonempty
      (GlobalSerializability.StateBasisBinding
        surface .genesis actualFinalizedEvent) :=
  ⟨actualFinalizedMutation.toSemanticBinding⟩

theorem actual_proposal_parent_is_actual_pre_state_root :
    actualFinalizedEvent.proposal.expectedParent =
      surface.stateRoot .genesis :=
  finalized_proposal_expected_parent_eq_pre_state_root actualFinalizedMutation

theorem actual_cas_and_append_consume_one_basis :
    mutationAdapter.casProposal actualMutation.casReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.appendProposal actualMutation.appendReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.casExpectedParent actualMutation.casReceipt =
        surface.stateRoot .genesis ∧
      mutationAdapter.appendExpectedParent actualMutation.appendReceipt =
        surface.stateRoot .genesis :=
  cas_append_and_proposal_share_basis actualFinalizedMutation

theorem actual_append_realizes_finalized_successor :
    mutationAdapter.appendPostState actualMutation.appendReceipt =
        surface.apply .genesis actualFinalizedEvent.proposal ∧
      surface.stateRoot
          (surface.apply .genesis actualFinalizedEvent.proposal) =
        actualFinalizedEvent.certificate.head :=
  append_realizes_finalized_transition actualFinalizedMutation

theorem actual_global_finality_is_the_rcc45_success :
    actualFinalizedMutation.globalFinality.localSuccess =
      actualFinalizedEvent.certificate.admission.finalizeSuccess :=
  global_finality_matches_rcc45 actualFinalizedMutation

/--
CM-RCC47-BASIS-01 control: the old semantic basis proof is valid, while
independent host receipts can claim a different actual pre-state.  Nothing in
the old carrier consumes or compares these receipts.
-/
theorem old_projection_coexists_with_stale_host_mutation :
    Nonempty
        (GlobalSerializability.StateBasisBinding
          surface .genesis actualFinalizedEvent) ∧
      mutationAdapter.CASAccepted .stale ∧
      mutationAdapter.AppendAccepted .stale ∧
      mutationAdapter.casExpectedParent .stale = surface.stateRoot .headA ∧
      mutationAdapter.appendExpectedParent .stale =
        surface.stateRoot .headA := by
  exact
    ⟨⟨actualBasis⟩, True.intro, True.intro, rfl, rfl⟩

/--
CM-RCC47-BASIS-01 refusal: the strengthened adapter cannot certify that same
RCC-45 event against the stale `headA` pre-state.
-/
theorem stale_host_pre_state_cannot_receive_finalized_binding :
    ¬ Nonempty
      (FinalizedStateMutation
        surface mutationAdapter 0 .headA actualFinalizedEvent
          globalLinearizer) := by
  exact stale_pre_state_root_cannot_bind Head.noConfusion

#print axioms finalized_proposal_expected_parent_eq_pre_state_root
#print axioms FinalizedStateMutation.toSemanticBinding
#print axioms cas_append_and_proposal_share_basis
#print axioms append_realizes_finalized_transition
#print axioms stale_pre_state_root_cannot_bind
#print axioms global_finality_matches_rcc45
#print axioms actual_proposal_parent_is_actual_pre_state_root
#print axioms actual_adapter_refines_original_rcc47
#print axioms actual_cas_and_append_consume_one_basis
#print axioms actual_append_realizes_finalized_successor
#print axioms actual_global_finality_is_the_rcc45_success
#print axioms old_projection_coexists_with_stale_host_mutation
#print axioms stale_host_pre_state_cannot_receive_finalized_binding

end Residua.RCC.StateBasisBinding.Tests

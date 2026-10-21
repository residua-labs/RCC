import RCC.GlobalSerializability

/-!
# RCC-47 State-Basis Binding Adapter

The original RCC-47 `GlobalSerializability.StateBasisBinding` correctly states
two semantic equalities, but it does not consume an actual CAS receipt or an
actual append receipt.  Consequently an implementation could prove the
semantic projection for one state while mutating another state outside that
proof.

This adapter closes that realization gap.  It binds:

* the RCC-45 finalized proposal and successor head;
* the RCC-42 global admission-linearizer snapshot and successful finalizer;
* the actual pre-state root;
* the CAS expected parent; and
* the append expected parent and post-state

through one proof-carrying `StateBasis`.  CAS and append receipts are still
domain-specific runtime objects; proving that a concrete runtime adapter emits
truthful receipt fields remains an implementation-refinement obligation.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.StateBasisBinding

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability

universe u

/--
One exact pre-state basis.  The root is data, not a caller-supplied Boolean,
and its proof binds it to the state consumed by the semantic transition.
-/
structure StateBasis
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (preState : State) where
  root : Head
  rootBound : root = surface.stateRoot preState

/--
Domain-specific observation surface for the actual compare-and-swap and
durable append operations.

The kernel does not invent these receipts.  A runtime refinement must show that
the projections below describe the bytes and state transition actually used by
the host CAS and append implementation.
-/
structure MutationAdapter
    (State Slot Head Judgment : Type u) where
  CASReceipt : Type u
  AppendReceipt : Type u
  casProposal : CASReceipt → Proposal Slot Head Judgment
  casExpectedParent : CASReceipt → Head
  CASAccepted : CASReceipt → Prop
  appendProposal : AppendReceipt → Proposal Slot Head Judgment
  appendExpectedParent : AppendReceipt → Head
  appendPostState : AppendReceipt → State
  AppendAccepted : AppendReceipt → Prop

/--
Actual CAS and append receipts bound to one proposal and one exact state basis.
Both operations therefore consume the same pre-state root.  The append result
is additionally tied to the semantic `surface.apply` transition.
-/
structure BasisBoundMutation
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    (preState : State)
    (basis : StateBasis surface preState)
    (proposal : Proposal Slot Head Judgment) where
  casReceipt : adapter.CASReceipt
  casAccepted : adapter.CASAccepted casReceipt
  casProposalBound : adapter.casProposal casReceipt = proposal
  casBasisBound : adapter.casExpectedParent casReceipt = basis.root
  appendReceipt : adapter.AppendReceipt
  appendAccepted : adapter.AppendAccepted appendReceipt
  appendProposalBound : adapter.appendProposal appendReceipt = proposal
  appendBasisBound : adapter.appendExpectedParent appendReceipt = basis.root
  appendPostStateBound :
    adapter.appendPostState appendReceipt = surface.apply preState proposal

/--
The complete RCC-47 realization bridge for one actual finalized transition.

`globalFinality` is the RCC-42 cross-snapshot certificate for the exact local
finalizer computation retained by the RCC-45 event.  `globalMatchesRCC45`
prevents a different successful computation from being spliced into this
event.  The basis and both mutation receipts then bind that same proposal to
the actual pre-state and finalized successor head.
-/
structure FinalizedStateMutation
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (version : Version)
    (preState : State)
    (finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence) where
  basis : StateBasis surface preState
  basisParentBound : basis.root = finalized.parent
  globalFinality :
    GloballySuccessfulFinalize
      linearizer
      version finalized.environment.writerState
      finalized.certificate.admission.finalizeRequest
  globalMatchesRCC45 :
    globalFinality.localSuccess =
      finalized.certificate.admission.finalizeSuccess
  mutation :
    BasisBoundMutation
      surface adapter preState basis finalized.proposal
  postHeadBound :
    surface.stateRoot (adapter.appendPostState mutation.appendReceipt) =
      finalized.certificate.head

/--
The strengthened adapter refines the original RCC-47 semantic carrier.  This
is the explicit bridge missing from the projection-only theorem: the old two
equalities are now derived from actual accepted CAS/append evidence that shares
one state basis.
-/
def FinalizedStateMutation.toSemanticBinding
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (certified :
      FinalizedStateMutation
        surface adapter version preState finalized linearizer) :
    GlobalSerializability.StateBasisBinding surface preState finalized where
  basisRootBound :=
    certified.basis.rootBound.symm.trans certified.basisParentBound
  postRootBound :=
    (congrArg surface.stateRoot
      certified.mutation.appendPostStateBound).symm.trans
        certified.postHeadBound

/--
RCC-47 state-basis law: the parent certified by RCC-42/RCC-45 is exactly the
root of the concrete state consumed by the mutation.
-/
theorem finalized_proposal_expected_parent_eq_pre_state_root
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (certified :
      FinalizedStateMutation
        surface adapter version preState finalized linearizer) :
    finalized.proposal.expectedParent = surface.stateRoot preState := by
  exact finalized.certificate.parentBound.trans
    (certified.basisParentBound.symm.trans certified.basis.rootBound)

/--
The CAS and append receipts consume one basis and one finalized proposal.
Their expected-parent observations therefore coincide with each other, with
the finalized proposal parent, and with the actual pre-state root.
-/
theorem cas_append_and_proposal_share_basis
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (certified :
      FinalizedStateMutation
        surface adapter version preState finalized linearizer) :
    adapter.casProposal certified.mutation.casReceipt = finalized.proposal ∧
      adapter.appendProposal certified.mutation.appendReceipt =
        finalized.proposal ∧
      adapter.casExpectedParent certified.mutation.casReceipt =
        surface.stateRoot preState ∧
      adapter.appendExpectedParent certified.mutation.appendReceipt =
        surface.stateRoot preState := by
  exact
    ⟨certified.mutation.casProposalBound,
      certified.mutation.appendProposalBound,
      certified.mutation.casBasisBound.trans certified.basis.rootBound,
      certified.mutation.appendBasisBound.trans certified.basis.rootBound⟩

/--
The durable append result is the semantic transition from that same pre-state,
and its observed root is the actual RCC-45 finalized successor head.
-/
theorem append_realizes_finalized_transition
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (certified :
      FinalizedStateMutation
        surface adapter version preState finalized linearizer) :
    adapter.appendPostState certified.mutation.appendReceipt =
        surface.apply preState finalized.proposal ∧
      surface.stateRoot (surface.apply preState finalized.proposal) =
        finalized.certificate.head := by
  constructor
  · exact certified.mutation.appendPostStateBound
  · exact
      (congrArg surface.stateRoot
        certified.mutation.appendPostStateBound).symm.trans
          certified.postHeadBound

/--
A stale concrete pre-state cannot receive a complete RCC-47 certificate.  This
is independent of proposal slot: the contradiction is between the observed
state root and the actual RCC-45 finalized parent.
-/
theorem stale_pre_state_root_cannot_bind
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (stale : surface.stateRoot preState ≠ finalized.parent) :
    ¬ Nonempty
      (FinalizedStateMutation
        surface adapter version preState finalized linearizer) := by
  rintro ⟨certified⟩
  exact stale
    (certified.basis.rootBound.symm.trans certified.basisParentBound)

/-- Every adapter certificate consumes the exact RCC-42 success held by RCC-45. -/
theorem global_finality_matches_rcc45
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {version : Version} {preState : State}
    {finalized :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          finalized.environment.writerSpec
          finalized.environment.equivalence}
    (certified :
      FinalizedStateMutation
        surface adapter version preState finalized linearizer) :
    certified.globalFinality.localSuccess =
      finalized.certificate.admission.finalizeSuccess :=
  certified.globalMatchesRCC45

end Residua.RCC.StateBasisBinding

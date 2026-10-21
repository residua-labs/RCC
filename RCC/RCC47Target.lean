import RCCTests.StateBasisBinding

/-!
# RCC-47 target package

This candidate binds one finalized proposal, CAS receipt, durable append, and
semantic state root to the same pre-state basis.  The stale-host mutation is
kept as an explicit refusal countermodel.
-/

namespace Residua.RCC.RCC47Target

open Residua.RCC.StateBasisBinding
open Residua.RCC.StateBasisBinding.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.FinalizedHeadWindow.Tests

structure Certificate : Prop where
  semanticRefinement :
    Nonempty
      (GlobalSerializability.StateBasisBinding
        surface .genesis actualFinalizedEvent)
  proposalBindsRoot :
    actualFinalizedEvent.proposal.expectedParent =
      surface.stateRoot .genesis
  casAppendShareBasis :
    mutationAdapter.casProposal actualMutation.casReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.appendProposal actualMutation.appendReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.casExpectedParent actualMutation.casReceipt =
        surface.stateRoot .genesis ∧
      mutationAdapter.appendExpectedParent actualMutation.appendReceipt =
        surface.stateRoot .genesis
  appendRealizesSuccessor :
    mutationAdapter.appendPostState actualMutation.appendReceipt =
        surface.apply .genesis actualFinalizedEvent.proposal
  staleHostRefused :
    ¬ Nonempty
      (FinalizedStateMutation
        surface mutationAdapter 0 .headA actualFinalizedEvent
          globalLinearizer)

def certificate : Certificate where
  semanticRefinement := actual_adapter_refines_original_rcc47
  proposalBindsRoot := actual_proposal_parent_is_actual_pre_state_root
  casAppendShareBasis := actual_cas_and_append_consume_one_basis
  appendRealizesSuccessor := actual_append_realizes_finalized_successor |>.1
  staleHostRefused := stale_host_pre_state_cannot_receive_finalized_binding

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC47Target

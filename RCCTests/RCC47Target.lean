import RCC.RCC47Target

/-! Thin admission checks for RCC-47 state-basis binding. -/

namespace Residua.RCC.RCC47Target.Tests

open Residua.RCC.StateBasisBinding
open Residua.RCC.StateBasisBinding.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.FinalizedHeadWindow.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_proposal_binds_pre_state_root :
    actualFinalizedEvent.proposal.expectedParent =
      surface.stateRoot .genesis :=
  certificate.proposalBindsRoot

theorem target_cas_and_append_share_basis :
    mutationAdapter.casProposal actualMutation.casReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.appendProposal actualMutation.appendReceipt =
        actualFinalizedEvent.proposal ∧
      mutationAdapter.casExpectedParent actualMutation.casReceipt =
        surface.stateRoot .genesis ∧
      mutationAdapter.appendExpectedParent actualMutation.appendReceipt =
        surface.stateRoot .genesis :=
  certificate.casAppendShareBasis

theorem target_stale_host_refused :
    ¬ Nonempty
      (FinalizedStateMutation
        surface mutationAdapter 0 .headA actualFinalizedEvent
          globalLinearizer) :=
  certificate.staleHostRefused

#print axioms target_certificate_nonempty
#print axioms target_proposal_binds_pre_state_root
#print axioms target_cas_and_append_share_basis
#print axioms target_stale_host_refused

end Residua.RCC.RCC47Target.Tests

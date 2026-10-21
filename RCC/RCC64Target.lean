import RCCTests.CandidateWindowDeterminism

/-! RCC-64 candidate: sealed candidate-window determinism and seed refusal. -/

namespace Residua.RCC.RCC64Target

universe uEpoch uHead uAssumption uAddress uSource uFailure uProposal uBundle

open Residua.RCC.CandidateWindowDeterminism.Tests
open Residua.RCC.CandidateWindowDeterminism
open Residua.RCC.FacetSnapshot

structure Certificate where
  sameSnapshotTraceGeneral :
    ∀ {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type uEpoch}
      {sealSpec :
        SnapshotSeal
          Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
            ProposalWindow ImplementationBundle}
      {K :
        CandidateWindowKernel
          Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
            ProposalWindow ImplementationBundle}
      {left right : SealedSnapshot sealSpec}
      (leftSeal : SealedCandidateWindowAt K left)
      (rightSeal : SealedCandidateWindowAt K right)
      (coordinatesExact : left.coordinates = right.coordinates),
      candidateOrderAt K left = candidateOrderAt K right ∧
        judgmentTraceAt K left = judgmentTraceAt K right ∧
        candidateResultAt K left = candidateResultAt K right
  sameSnapshotTrace :
    candidateOrderAt kernel leftSnapshot =
        candidateOrderAt kernel rightSnapshot ∧
      judgmentTraceAt kernel leftSnapshot =
        judgmentTraceAt kernel rightSnapshot ∧
      candidateResultAt kernel leftSnapshot =
        candidateResultAt kernel rightSnapshot
  detachedPoolRefused :
    [Candidate.first].map verify ≠ [Candidate.second].map verify
  hiddenSeedRefused :
    [Candidate.first].map (hiddenSeedVerify false) ≠
      [Candidate.first].map (hiddenSeedVerify true)

def certificate : Certificate where
  sameSnapshotTraceGeneral := sealed_candidate_window_deterministic
  sameSnapshotTrace := exact_snapshot_has_same_instance_candidate_trace
  detachedPoolRefused := detached_pool_breaks_determinism
  hiddenSeedRefused := hidden_seed_breaks_unsealed_verification

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC64Target

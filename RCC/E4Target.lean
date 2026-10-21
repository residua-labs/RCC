import RCCTests.CandidateWindowDeterminism

/-! E4 candidate: stochastic discovery is outside the sealed proposal window;
    one fixed snapshot and pure kernel give one ordered candidate trace and
    one result, while detached pools and hidden seeds are rejected mutants. -/

namespace Residua.RCC.E4Target

open Residua.RCC.CandidateWindowDeterminism
open Residua.RCC.CandidateWindowDeterminism.Tests

structure Certificate where
  exactSnapshotTrace :
    candidateOrderAt kernel leftSnapshot = candidateOrderAt kernel rightSnapshot ∧
      judgmentTraceAt kernel leftSnapshot = judgmentTraceAt kernel rightSnapshot ∧
      candidateResultAt kernel leftSnapshot = candidateResultAt kernel rightSnapshot
  detachedPoolRejected :
    [Candidate.first].map verify ≠ [Candidate.second].map verify
  hiddenSeedRejected :
    [Candidate.first].map (hiddenSeedVerify false) ≠
      [Candidate.first].map (hiddenSeedVerify true)

def certificate : Certificate where
  exactSnapshotTrace := exact_snapshot_has_same_instance_candidate_trace
  detachedPoolRejected := detached_pool_breaks_determinism
  hiddenSeedRejected := hidden_seed_breaks_unsealed_verification

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.E4Target

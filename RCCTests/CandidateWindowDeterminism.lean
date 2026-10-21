import RCC.CandidateWindowDeterminism

namespace Residua.RCC.CandidateWindowDeterminism.Tests

open Residua.RCC.FacetSnapshot

inductive Candidate
  | first
  | second
  deriving DecidableEq, Repr

inductive ProposalWindow
  | sealed
  deriving DecidableEq, Repr

abbrev Epoch := Unit
abbrev HistoryHead := Unit
abbrev AssumptionRoot := Unit
abbrev AddressRegistry := Unit
abbrev SourceWindow := Unit
abbrev FailureModel := Unit
abbrev ImplementationBundle := Unit

def sealSpec :
    SnapshotSeal
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle where
  IsSealed := fun _ => True

def coordinates :
    SnapshotCoordinates
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle where
  epoch := ()
  historyHead := ()
  assumptionRoot := ()
  addressRegistry := ()
  sourceWindow := ()
  failureModel := ()
  proposalWindow := .sealed
  implementationBundle := ()

def leftSnapshot : SealedSnapshot sealSpec where
  coordinates := coordinates
  sealed := trivial

def rightSnapshot : SealedSnapshot sealSpec where
  coordinates := coordinates
  sealed := trivial

def candidateQ : Candidate → Nat
  | .first => 0
  | .second => 1

def verify : Candidate → Bool
  | .first => false
  | .second => true

def finish : List Bool → Bool
  | [] => false
  | judgment :: _ => judgment

def kernel :
    CandidateWindowKernel
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle where
  Candidate := Candidate
  CandidateQ := Nat
  Judgment := Bool
  Result := Bool
  candidateQ := candidateQ
  QBefore := Nat.lt
  qBeforeIrreflexive := Nat.lt_irrefl
  qBeforeTransitive := Nat.lt_trans
  qBeforeTotal := by
    intro left right different
    exact Nat.lt_or_gt_of_ne different
  candidatesAt := fun _ => [.first, .second]
  verifyAt := fun _ candidate => verify candidate
  finishAt := fun _ judgments => finish judgments

def leftSeal : SealedCandidateWindowAt kernel leftSnapshot where
  qOrdered := by
    simp [candidateOrderAt, kernel, leftSnapshot, coordinates, candidateQ]
  qNoDuplicates := by
    simp [candidateOrderAt, kernel, leftSnapshot, coordinates, candidateQ]

def rightSeal : SealedCandidateWindowAt kernel rightSnapshot where
  qOrdered := by
    simp [candidateOrderAt, kernel, rightSnapshot, coordinates, candidateQ]
  qNoDuplicates := by
    simp [candidateOrderAt, kernel, rightSnapshot, coordinates, candidateQ]

theorem exact_snapshot_has_same_instance_candidate_trace :
    candidateOrderAt kernel leftSnapshot =
        candidateOrderAt kernel rightSnapshot ∧
      judgmentTraceAt kernel leftSnapshot =
        judgmentTraceAt kernel rightSnapshot ∧
      candidateResultAt kernel leftSnapshot =
        candidateResultAt kernel rightSnapshot :=
  sealed_candidate_window_deterministic leftSeal rightSeal rfl

/--
Mutant: if a caller may detach the pool from the sealed proposal window, two
individually ordered singleton pools at the same snapshot produce different
traces.
-/
theorem detached_pool_breaks_determinism :
    [Candidate.first].map verify ≠ [Candidate.second].map verify := by
  decide

/--
Mutant: a hidden random seed can reverse the judgment for the same candidate.
Such a seed must enter the snapshot or implementation bundle before sealing.
-/
def hiddenSeedVerify (seed : Bool) (_candidate : Candidate) : Bool :=
  seed

theorem hidden_seed_breaks_unsealed_verification :
    [Candidate.first].map (hiddenSeedVerify false) ≠
      [Candidate.first].map (hiddenSeedVerify true) := by
  decide

end Residua.RCC.CandidateWindowDeterminism.Tests

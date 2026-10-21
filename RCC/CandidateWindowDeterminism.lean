import RCC.FacetSnapshot

/-!
# E4 parametric candidate-window determinism

Candidate discovery may be stochastic, but normalization consumes only the
ordered finite pool selected by the proposal-window coordinate of one exact
FC-1 snapshot. A fixed kernel maps that pool to judgments and one folded
result; callers cannot inject a detached candidate list into these functions.

This kernel does not prove candidate-universe completeness, a no-solution
claim, proposal-window address injectivity, verifier implementation binding,
or global normalization uniqueness.
-/

namespace Residua.RCC.CandidateWindowDeterminism

open Residua.RCC.FacetSnapshot

universe u

/--
Executable candidate semantics over every declared snapshot coordinate.
Anything that can affect verification must be represented in these coordinates
or justified by the separate runtime-binding and hermeticity layers.
-/
structure CandidateWindowKernel
    (Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u) where
  Candidate : Type u
  CandidateQ : Type u
  Judgment : Type u
  Result : Type u
  candidateQ : Candidate → CandidateQ
  QBefore : CandidateQ → CandidateQ → Prop
  qBeforeIrreflexive : ∀ candidateQ, ¬ QBefore candidateQ candidateQ
  qBeforeTransitive :
    ∀ {first second third},
      QBefore first second →
      QBefore second third →
      QBefore first third
  qBeforeTotal :
    ∀ {left right},
      left ≠ right →
        QBefore left right ∨ QBefore right left
  candidatesAt : ProposalWindow → List Candidate
  verifyAt :
    SnapshotCoordinates
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle →
      Candidate → Judgment
  finishAt :
    SnapshotCoordinates
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle →
      List Judgment → Result

/-- The sole candidate order consumed at one exact sealed snapshot. -/
def candidateOrderAt
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (K :
      CandidateWindowKernel
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec) :
    List K.Candidate :=
  K.candidatesAt snapshot.coordinates.proposalWindow

/-- Deterministic judgment trace over the snapshot-derived candidate order. -/
def judgmentTraceAt
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (K :
      CandidateWindowKernel
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec) :
    List K.Judgment :=
  (candidateOrderAt K snapshot).map (K.verifyAt snapshot.coordinates)

/-- The fixed fold result for the exact snapshot and its judgment trace. -/
def candidateResultAt
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (K :
      CandidateWindowKernel
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec) :
    K.Result :=
  K.finishAt snapshot.coordinates (judgmentTraceAt K snapshot)

/--
An eligible proposal window resolves to a finite, duplicate-free list in the
instance-declared strict total q order. This is a law over the
snapshot-derived list, not a caller-supplied pool. Address realization of that
window remains an outer RCC-0 obligation.
-/
structure SealedCandidateWindowAt
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (K :
      CandidateWindowKernel
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec) : Prop where
  qOrdered :
    List.Pairwise
      (fun left right => K.QBefore (K.candidateQ left) (K.candidateQ right))
      (candidateOrderAt K snapshot)
  qNoDuplicates :
    (candidateOrderAt K snapshot).map K.candidateQ |>.Nodup

/--
Parametric E4 core: equal complete snapshot coordinates under one fixed pure
kernel yield the same structurally equal ordered pool, judgment trace, and
folded result. The seal premises establish eligibility; functional equality
comes from the fixed kernel and exact coordinates.
-/
theorem sealed_candidate_window_deterministic
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {K :
      CandidateWindowKernel
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {left right : SealedSnapshot sealSpec}
    (_leftSeal : SealedCandidateWindowAt K left)
    (_rightSeal : SealedCandidateWindowAt K right)
    (coordinatesExact : left.coordinates = right.coordinates) :
    candidateOrderAt K left = candidateOrderAt K right ∧
      judgmentTraceAt K left = judgmentTraceAt K right ∧
      candidateResultAt K left = candidateResultAt K right := by
  have windowExact :
      left.coordinates.proposalWindow =
        right.coordinates.proposalWindow :=
    congrArg SnapshotCoordinates.proposalWindow coordinatesExact
  have orderExact :
      candidateOrderAt K left = candidateOrderAt K right :=
    congrArg K.candidatesAt windowExact
  have verifierExact :
      K.verifyAt left.coordinates = K.verifyAt right.coordinates :=
    congrArg K.verifyAt coordinatesExact
  have traceExact :
      judgmentTraceAt K left = judgmentTraceAt K right := by
    calc
      judgmentTraceAt K left =
          (candidateOrderAt K right).map
            (K.verifyAt left.coordinates) :=
        congrArg
          (fun candidates =>
            candidates.map (K.verifyAt left.coordinates))
          orderExact
      _ = judgmentTraceAt K right :=
        congrArg
          (fun verifier => (candidateOrderAt K right).map verifier)
          verifierExact
  have finishExact :
      K.finishAt left.coordinates = K.finishAt right.coordinates :=
    congrArg K.finishAt coordinatesExact
  have resultExact :
      candidateResultAt K left = candidateResultAt K right := by
    calc
      candidateResultAt K left =
          K.finishAt right.coordinates (judgmentTraceAt K left) :=
        congrArg
          (fun finish => finish (judgmentTraceAt K left))
          finishExact
      _ = candidateResultAt K right :=
        congrArg (K.finishAt right.coordinates) traceExact
  exact ⟨orderExact, traceExact, resultExact⟩

end Residua.RCC.CandidateWindowDeterminism

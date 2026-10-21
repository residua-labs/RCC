import RCC.StateBasisBinding
import RCC.TransactionFootprint

/-!
# RCC-50 Proof-Carrying Executable Commutative Join

The original `ExactCommutativeJoin` records two caller-supplied serial traces
and two operation-list equalities.  This module strengthens that projection
into an executable admission check whose trace steps carry:

* an actual RCC-45 finalized event;
* the RCC-47 CAS/append/state-basis realization of that event; and
* an RCC-48 universe-complete four-dimensional footprint.

Operation identity and occurrence identity remain separate.  The same
operation may be replayed in the opposite serial order only through fresh,
parent-bound occurrences; no durable occurrence may be reused between the
two alternative traces.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, declared axioms,
unsafe definitions, or noncomputable choice.
-/

namespace Residua.RCC.CommutativeJoin

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability
open Residua.RCC.StateBasisBinding
open Residua.RCC.TransactionFootprint

universe u

/--
Existential packaging of the RCC-42 version/linearizer coordinates retained
by one strengthened RCC-47 certificate.  Different finalized events may come
from different writer snapshots without erasing any of their proofs.
-/
structure PackedFinalizedStateMutation
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
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
        history ConfigLawful) where
  Version : Type u
  version : Version
  linearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Version
        finalized.environment.writerSpec
        finalized.environment.equivalence
  certificate :
    FinalizedStateMutation
      surface adapter version preState finalized linearizer

/--
One executable join step.  No caller may supply the weaker RCC-47 or RCC-48
projection directly: both are derived below from the stronger runtime-facing
certificates.
-/
structure ProofCarryingJoinStep
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (preState : State) where
  finalized :
    RCC45FinalizedEvent
      (Judgment := Judgment)
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      history ConfigLawful
  stateMutation :
    PackedFinalizedStateMutation
      surface adapter preState finalized
  universes :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain
  footprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain
  footprintSeal :
    UniverseCompleteFootprint
      surface preState finalized.proposal universes footprint

/-- Forget only the strengthened certificates, retaining their derived laws. -/
def ProofCarryingJoinStep.toCertifiedFinalizedStep
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {preState : State}
    (step :
      ProofCarryingJoinStep
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        (history := history)
        (ConfigLawful := ConfigLawful)
        surface adapter preState) :
    CertifiedFinalizedStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      (history := history)
      (ConfigLawful := ConfigLawful)
      surface preState where
  finalized := step.finalized
  footprint := step.footprint
  footprintComplete := step.footprintSeal.toCompleteFootprint
  basis := step.stateMutation.certificate.toSemanticBinding

/--
Two actual finalized steps.  The second step is indexed by the exact semantic
post-state of the first, and the two durable occurrences are distinct.
-/
structure ActualTwoStepExecution
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State) where
  first :
    ProofCarryingJoinStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      (history := history)
      (ConfigLawful := ConfigLawful)
      surface adapter initial
  second :
    ProofCarryingJoinStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      (history := history)
      (ConfigLawful := ConfigLawful)
      surface adapter
        (surface.apply initial first.finalized.proposal)
  occurrencesDistinct :
    first.finalized.occurrenceId ≠ second.finalized.occurrenceId

/-- The two durable occurrence identities, in actual execution order. -/
def ActualTwoStepExecution.occurrences
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (execution :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) :
    List OccurrenceId :=
  [execution.first.finalized.occurrenceId,
    execution.second.finalized.occurrenceId]

/-- Operation projection deliberately erases durable occurrence identity. -/
def ActualTwoStepExecution.operations
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (execution :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) :
    List OperationId :=
  [surface.operationOf execution.first.finalized.proposal,
    surface.operationOf execution.second.finalized.proposal]

/-- Final state mechanically obtained by applying both actual proposals. -/
def ActualTwoStepExecution.finalState
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (execution :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) :
    State :=
  surface.apply
    (surface.apply initial execution.first.finalized.proposal)
    execution.second.finalized.proposal

/-- The proof-carrying pair refines the existing actual serial trace type. -/
def ActualTwoStepExecution.toSerialExecution
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (execution :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful initial execution.occurrences
        execution.finalState :=
  .cons execution.first.toCertifiedFinalizedStep
    (.cons execution.second.toCertifiedFinalizedStep (.nil _) (by simp))
    (by simpa [ActualTwoStepExecution.occurrences] using
      execution.occurrencesDistinct)

/--
An untrusted exact-join candidate.  Its two traces are already
proof-carrying, but it is not admitted until the uniform checker validates
operation order, occurrence rebasing, and the common final state.
-/
structure ExactJoinCandidate
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (adapter : MutationAdapter State Slot Head Judgment)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State)
    (leftOperation rightOperation : OperationId) where
  leftThenRight :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface adapter history ConfigLawful initial
  rightThenLeft :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface adapter history ConfigLawful initial

/-- Alternative serializations must not reuse any durable occurrence. -/
def OccurrencesRebased
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (left right :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) : Prop :=
  left.first.finalized.occurrenceId ≠ right.first.finalized.occurrenceId ∧
    left.first.finalized.occurrenceId ≠
      right.second.finalized.occurrenceId ∧
    left.second.finalized.occurrenceId ≠
      right.first.finalized.occurrenceId ∧
    left.second.finalized.occurrenceId ≠
      right.second.finalized.occurrenceId

/-- The finite two-by-two occurrence comparison is executable. -/
instance decidableOccurrencesRebased
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation] [DecidableEq OccurrenceId]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (left right :
      ActualTwoStepExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful initial) :
    Decidable (OccurrencesRebased left right) := by
  unfold OccurrencesRebased
  infer_instance

/-- Proof object generated only by the uniform exact-join checker. -/
structure ExactJoinCertificate
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    (candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation) : Prop where
  occurrencesRebased :
    OccurrencesRebased candidate.leftThenRight candidate.rightThenLeft
  leftOperations :
    candidate.leftThenRight.operations = [leftOperation, rightOperation]
  rightOperations :
    candidate.rightThenLeft.operations = [rightOperation, leftOperation]
  joinedState :
    candidate.leftThenRight.finalState =
      candidate.rightThenLeft.finalState

/-- Exhaustive RCC-50 rejection classes. -/
inductive JoinResidue
  | occurrenceNotRebased
  | leftOperationOrderMismatch
  | rightOperationOrderMismatch
  | finalStateMismatch
  deriving DecidableEq, Repr

/-- Dependent result retains the exact candidate admitted by the checker. -/
inductive JoinVerdict
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    (candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation) where
  | admit : ExactJoinCertificate candidate → JoinVerdict candidate
  | refuse : JoinResidue → JoinVerdict candidate

/--
The single executable RCC-50 classifier.  It validates occurrence rebasing
separately from operation identity, then checks that the two actual serial
executions share one derived final state.
-/
def verifyExactJoin
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    [DecidableEq State] [DecidableEq OperationId] [DecidableEq OccurrenceId]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    (candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation) :
    JoinVerdict candidate :=
  if occurrencesRebased :
      OccurrencesRebased candidate.leftThenRight candidate.rightThenLeft then
    if leftOperations :
        candidate.leftThenRight.operations =
          [leftOperation, rightOperation] then
      if rightOperations :
          candidate.rightThenLeft.operations =
            [rightOperation, leftOperation] then
        if joinedState :
            candidate.leftThenRight.finalState =
              candidate.rightThenLeft.finalState then
          .admit {
            occurrencesRebased := occurrencesRebased
            leftOperations := leftOperations
            rightOperations := rightOperations
            joinedState := joinedState
          }
        else
          .refuse .finalStateMismatch
      else
        .refuse .rightOperationOrderMismatch
    else
      .refuse .leftOperationOrderMismatch
  else
    .refuse .occurrenceNotRebased

/-- Transport only the final-state index of an actual serial execution. -/
def transportSerialFinal
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial fromState toState : State}
    {occurrences : List OccurrenceId}
    (sameFinal : fromState = toState)
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful initial occurrences fromState) :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful initial occurrences toState :=
  sameFinal ▸ execution

/-- Final-index transport cannot change the operation projection. -/
theorem transportSerialFinal_operations
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial fromState toState : State}
    {occurrences : List OccurrenceId}
    (sameFinal : fromState = toState)
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful initial occurrences fromState) :
    (transportSerialFinal sameFinal execution).operations =
      execution.operations := by
  cases sameFinal
  rfl

/--
An admitted executable certificate refines the old RCC-50 projection.  The
dependent final-state equality is eliminated only after both actual traces
have already been constructed.
-/
def ExactJoinCertificate.toExactCommutativeJoin
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    {candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation}
    (certificate : ExactJoinCertificate candidate) :
    ExactCommutativeJoin
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface history ConfigLawful initial leftOperation rightOperation
        candidate.leftThenRight.finalState := by
  let rightExecution :=
    transportSerialFinal certificate.joinedState.symm
      candidate.rightThenLeft.toSerialExecution
  exact {
    leftOccurrences := candidate.leftThenRight.occurrences
    rightOccurrences := candidate.rightThenLeft.occurrences
    leftThenRight := candidate.leftThenRight.toSerialExecution
    rightThenLeft := rightExecution
    leftOperations := certificate.leftOperations
    rightOperations :=
      (transportSerialFinal_operations certificate.joinedState.symm
        candidate.rightThenLeft.toSerialExecution).trans
          certificate.rightOperations
  }

/-- The admitted object exposes two actual legal traces and one shared state. -/
theorem exact_join_is_two_actual_serial_executions
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    {candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation}
    (certificate : ExactJoinCertificate candidate) :
    Nonempty
        (SerialExecution
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (FailureName := FailureName)
          surface history ConfigLawful initial
            candidate.leftThenRight.occurrences
            candidate.leftThenRight.finalState) ∧
      Nonempty
        (SerialExecution
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (FailureName := FailureName)
          surface history ConfigLawful initial
            candidate.rightThenLeft.occurrences
            candidate.rightThenLeft.finalState) ∧
      candidate.leftThenRight.finalState =
        candidate.rightThenLeft.finalState :=
  ⟨⟨candidate.leftThenRight.toSerialExecution⟩,
    ⟨candidate.rightThenLeft.toSerialExecution⟩,
    certificate.joinedState⟩

/-- Operation equality and fresh occurrence realization are separate laws. -/
theorem exact_join_separates_operation_and_occurrence_identity
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {adapter : MutationAdapter State Slot Head Judgment}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {leftOperation rightOperation : OperationId}
    {candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface adapter history ConfigLawful
        initial leftOperation rightOperation}
    (certificate : ExactJoinCertificate candidate) :
    candidate.leftThenRight.operations = [leftOperation, rightOperation] ∧
      candidate.rightThenLeft.operations = [rightOperation, leftOperation] ∧
      OccurrencesRebased
        candidate.leftThenRight candidate.rightThenLeft :=
  ⟨certificate.leftOperations, certificate.rightOperations,
    certificate.occurrencesRebased⟩

end Residua.RCC.CommutativeJoin

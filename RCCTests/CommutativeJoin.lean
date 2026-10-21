import RCC.CommutativeJoin
import RCCTests.GlobalSerializability

/-!
# RCC-50 Executable Commutative-Join Witnesses and Mutants

The positive witness uses four actual RCC-45 events.  Every step additionally
contains the strengthened RCC-47 CAS/append/state-basis certificate and the
RCC-48 sealed-footprint certificate.

The three load-bearing mutants are:

* a checker that observes only the left serial execution;
* reuse of durable occurrences across the two alternative executions; and
* reverse operation orders whose actual final states disagree.
-/

namespace Residua.RCC.CommutativeJoin.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.CommutativeJoin
open Residua.RCC.GlobalSerializability
open Residua.RCC.StateBasisBinding
open Residua.RCC.TransactionFootprint
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.GlobalSerializability.Tests.Concrete

/-- Runtime-facing CAS and append observations for every concrete event. -/
def mutationAdapter : MutationAdapter Head Slot Head Judgment where
  CASReceipt := EventQ
  AppendReceipt := EventQ
  casProposal := proposalOf
  casExpectedParent := parentOf
  CASAccepted := fun _ => True
  appendProposal := proposalOf
  appendExpectedParent := parentOf
  appendPostState := headOf
  AppendAccepted := fun _ => True

/-- One total RCC-42 linearizer for one exact concrete writer snapshot. -/
def eventLinearizer (event : EventQ) :
    AdmissionLinearizer
      Slot Head Judgment Generation Unit writerSpec judgmentEq where
  Precedes := fun _ _ => True
  precedesRefl := by
    intro _
    exact True.intro
  precedesTrans := by
    intro _ _ _ _ _
    exact True.intro
  comparable := by
    intro _ _
    exact Or.inl True.intro
  activeGeneration := fun _ _ => .current
  canonicalDecision := fun _ _ => (writerState event).decisions
  decisionPreserved := by
    intro _ _ _ _ _ _ committed
    exact committed

def eventWriterSnapshot (event : EventQ) :
    CanonicalWriterSnapshot
      (eventLinearizer event) () (writerState event) where
  generationBound := rfl
  decisionBound := by
    intro _
    rfl

def eventGlobalFinality (event : EventQ) :
    GloballySuccessfulFinalize
      (eventLinearizer event) () (writerState event)
        (finalizeRequest event) where
  snapshot := eventWriterSnapshot event
  localSuccess := finalizeSuccess event

/-- Build an RCC-47 state basis for any surface with the supplied root law. -/
def stateBasisFor
    (surface :
      TransactionSurface
        Head Slot Head Judgment OperationId
          ReadDomain WriteDomain EffectDomain InvariantDomain)
    (event : EventQ)
    (rootBound :
      parentOf event = surface.stateRoot (parentOf event)) :
    StateBasis surface (parentOf event) where
  root := parentOf event
  rootBound := rootBound

/-- Bind actual CAS/append observations to one proposal and one pre-state. -/
def boundMutationFor
    (surface :
      TransactionSurface
        Head Slot Head Judgment OperationId
          ReadDomain WriteDomain EffectDomain InvariantDomain)
    (event : EventQ)
    (rootBound :
      parentOf event = surface.stateRoot (parentOf event))
    (applyBound :
      headOf event =
        surface.apply (parentOf event) (proposalOf event)) :
    BasisBoundMutation
      surface mutationAdapter (parentOf event)
        (stateBasisFor surface event rootBound) (proposalOf event) where
  casReceipt := event
  casAccepted := True.intro
  casProposalBound := rfl
  casBasisBound := rfl
  appendReceipt := event
  appendAccepted := True.intro
  appendProposalBound := rfl
  appendBasisBound := rfl
  appendPostStateBound := applyBound

/-- Complete RCC-42/RCC-45/RCC-47 binding for one concrete event. -/
def finalizedMutationFor
    (surface :
      TransactionSurface
        Head Slot Head Judgment OperationId
          ReadDomain WriteDomain EffectDomain InvariantDomain)
    (event : EventQ)
    (rootBound :
      parentOf event = surface.stateRoot (parentOf event))
    (applyBound :
      headOf event =
        surface.apply (parentOf event) (proposalOf event))
    (postRootBound :
      surface.stateRoot (headOf event) = headOf event) :
    FinalizedStateMutation
      surface mutationAdapter () (parentOf event)
        (finalizedEvent event) (eventLinearizer event) where
  basis := stateBasisFor surface event rootBound
  basisParentBound := rfl
  globalFinality := eventGlobalFinality event
  globalMatchesRCC45 := rfl
  mutation := boundMutationFor surface event rootBound applyBound
  postHeadBound := postRootBound

def packedMutationFor
    (surface :
      TransactionSurface
        Head Slot Head Judgment OperationId
          ReadDomain WriteDomain EffectDomain InvariantDomain)
    (event : EventQ)
    (rootBound :
      parentOf event = surface.stateRoot (parentOf event))
    (applyBound :
      headOf event =
        surface.apply (parentOf event) (proposalOf event))
    (postRootBound :
      surface.stateRoot (headOf event) = headOf event) :
    PackedFinalizedStateMutation
      surface mutationAdapter (parentOf event) (finalizedEvent event) where
  Version := Unit
  version := ()
  linearizer := eventLinearizer event
  certificate :=
    finalizedMutationFor
      surface event rootBound applyBound postRootBound

/-- A finite sealed coordinate universe. -/
def singletonUniverse {Domain : Type} (coordinate : Domain) :
    SealedDomainUniverse Domain where
  InUniverse := fun domain => domain = coordinate
  coordinates := [coordinate]
  coverage := {
    sound := by
      intro domain member
      simpa using member
    complete := by
      intro domain inUniverse
      simp [inUniverse]
  }

def transactionUniverses :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := singletonUniverse .source
  writes := singletonUniverse .target
  effects := singletonUniverse .store
  invariantDomains := singletonUniverse .balance

/--
Derive RCC-48 exactness from the four sealed universes when all semantic
footprints are empty.
-/
def sealedEmptyFootprint
    (surface :
      TransactionSurface
        Head Slot Head Judgment OperationId
          ReadDomain WriteDomain EffectDomain InvariantDomain)
    (state : Head)
    (event : EventQ)
    (readsEmpty :
      ∀ domain, surface.Reads state (proposalOf event) domain → False)
    (writesEmpty :
      ∀ domain, surface.Writes state (proposalOf event) domain → False)
    (effectsEmpty :
      ∀ domain, surface.Effects state (proposalOf event) domain → False)
    (invariantsEmpty :
      ∀ domain,
        surface.InvariantDomains state (proposalOf event) domain → False) :
    UniverseCompleteFootprint
      surface state (proposalOf event) transactionUniverses emptyFootprint where
  reads := {
    semanticInUniverse := by
      intro domain semantic
      exact False.elim (readsEmpty domain semantic)
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro domain _
      constructor
      · intro impossible
        cases impossible
      · intro semantic
        exact False.elim (readsEmpty domain semantic)
  }
  writes := {
    semanticInUniverse := by
      intro domain semantic
      exact False.elim (writesEmpty domain semantic)
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro domain _
      constructor
      · intro impossible
        cases impossible
      · intro semantic
        exact False.elim (writesEmpty domain semantic)
  }
  effects := {
    semanticInUniverse := by
      intro domain semantic
      exact False.elim (effectsEmpty domain semantic)
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro domain _
      constructor
      · intro impossible
        cases impossible
      · intro semantic
        exact False.elim (effectsEmpty domain semantic)
  }
  invariantDomains := {
    semanticInUniverse := by
      intro domain semantic
      exact False.elim (invariantsEmpty domain semantic)
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro domain _
      constructor
      · intro impossible
        cases impossible
      · intro semantic
        exact False.elim (invariantsEmpty domain semantic)
  }

def concretePackedMutation (event : EventQ) :
    PackedFinalizedStateMutation
      concreteSurface mutationAdapter (parentOf event) (finalizedEvent event) :=
  packedMutationFor concreteSurface event
    (by cases event <;> rfl)
    (by cases event <;> rfl)
    (by cases event <;> rfl)

def concreteFootprintSeal (event : EventQ) :
    UniverseCompleteFootprint
      concreteSurface (parentOf event) (proposalOf event)
        transactionUniverses emptyFootprint :=
  sealedEmptyFootprint concreteSurface (parentOf event) event
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)

def concreteJoinStep (event : EventQ) :
    ProofCarryingJoinStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      concreteSurface mutationAdapter (parentOf event) where
  finalized := finalizedEvent event
  stateMutation := concretePackedMutation event
  universes := transactionUniverses
  footprint := emptyFootprint
  footprintSeal := concreteFootprintSeal event

def concreteLeftThenRight :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful .root0 where
  first := concreteJoinStep .leftAtRoot0
  second := concreteJoinStep .rightAfterLeft
  occurrencesDistinct := by decide

def concreteRightThenLeft :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful .root0 where
  first := concreteJoinStep .rightAtRoot0
  second := concreteJoinStep .leftAfterRight
  occurrencesDistinct := by decide

def concreteCandidate :
    ExactJoinCandidate
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful
        .root0 .left .right where
  leftThenRight := concreteLeftThenRight
  rightThenLeft := concreteRightThenLeft

def concreteCertificate : ExactJoinCertificate concreteCandidate where
  occurrencesRebased := by decide
  leftOperations := rfl
  rightOperations := rfl
  joinedState := rfl

theorem executable_checker_admits_the_actual_exact_join :
    verifyExactJoin concreteCandidate = .admit concreteCertificate := by
  rfl

theorem admitted_join_contains_both_actual_rcc45_rcc47_rcc48_traces :
    Nonempty
        (SerialExecution
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (FailureName := FailureName)
          concreteSurface finalizedHistory configLawful .root0
            concreteLeftThenRight.occurrences
            concreteLeftThenRight.finalState) ∧
      Nonempty
        (SerialExecution
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (FailureName := FailureName)
          concreteSurface finalizedHistory configLawful .root0
            concreteRightThenLeft.occurrences
            concreteRightThenLeft.finalState) ∧
      concreteLeftThenRight.finalState =
        concreteRightThenLeft.finalState :=
  exact_join_is_two_actual_serial_executions concreteCertificate

theorem admitted_join_refines_the_original_rcc50_projection :
    Nonempty
      (ExactCommutativeJoin
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := Occurrence)
        (FailureName := FailureName)
        concreteSurface finalizedHistory configLawful
          .root0 .left .right concreteLeftThenRight.finalState) :=
  ⟨concreteCertificate.toExactCommutativeJoin⟩

/-! ## Mutant 1: observing only the left serialization -/

def concreteSetThenIncrement :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful .root0 where
  first := concreteJoinStep .setAtRoot0
  second := concreteJoinStep .incrementAfterSet
  occurrencesDistinct := by decide

def oneSidedCandidate :
    ExactJoinCandidate
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful
        .root0 .left .right where
  leftThenRight := concreteLeftThenRight
  rightThenLeft := concreteSetThenIncrement

/-- The unsound mutant accepts solely because the left operation order fits. -/
def leftOnlyAccepts
    (candidate :
      ExactJoinCandidate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := Occurrence)
        (FailureName := FailureName)
        concreteSurface mutationAdapter finalizedHistory configLawful
          .root0 .left .right) : Bool :=
  decide (candidate.leftThenRight.operations = [.left, .right])

theorem one_sided_mutant_accepts :
    leftOnlyAccepts oneSidedCandidate = true := by
  rfl

theorem exact_checker_rejects_one_sided_join :
    verifyExactJoin oneSidedCandidate =
      .refuse .rightOperationOrderMismatch := by
  rfl

/-! ## Mutant 2: reusing durable occurrences in both alternatives -/

def reusedOccurrenceCandidate :
    ExactJoinCandidate
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface mutationAdapter finalizedHistory configLawful
        .root0 .left .right where
  leftThenRight := concreteLeftThenRight
  rightThenLeft := concreteLeftThenRight

theorem exact_checker_rejects_reused_occurrence :
    verifyExactJoin reusedOccurrenceCandidate =
      .refuse .occurrenceNotRebased := by
  rfl

/-! ## Mutant 3: reverse operation orders with different final states -/

/--
Relabel the already finalized right/left events as increment/set operations.
State transition semantics are unchanged, so every strengthened step remains
RCC-45/RCC-47/RCC-48 certified while the reverse traces end in different
states.
-/
def noncommutingSurface :
    TransactionSurface
      Head Slot Head Judgment OperationId
        ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { concreteSurface with
    operationOf := fun proposal =>
      match proposal.judgment with
      | .set => .set
      | .increment => .increment
      | .left => .set
      | .right => .increment }

def noncommutingPackedMutation (event : EventQ) :
    PackedFinalizedStateMutation
      noncommutingSurface mutationAdapter (parentOf event)
        (finalizedEvent event) :=
  packedMutationFor noncommutingSurface event
    (by cases event <;> rfl)
    (by cases event <;> rfl)
    (by cases event <;> rfl)

def noncommutingFootprintSeal (event : EventQ) :
    UniverseCompleteFootprint
      noncommutingSurface (parentOf event) (proposalOf event)
        transactionUniverses emptyFootprint :=
  sealedEmptyFootprint noncommutingSurface (parentOf event) event
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)
    (by intro _ impossible; exact impossible)

def noncommutingJoinStep (event : EventQ) :
    ProofCarryingJoinStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      noncommutingSurface mutationAdapter (parentOf event) where
  finalized := finalizedEvent event
  stateMutation := noncommutingPackedMutation event
  universes := transactionUniverses
  footprint := emptyFootprint
  footprintSeal := noncommutingFootprintSeal event

def noncommutingLeftThenRight :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      noncommutingSurface mutationAdapter finalizedHistory configLawful
        .root0 where
  first := noncommutingJoinStep .setAtRoot0
  second := noncommutingJoinStep .incrementAfterSet
  occurrencesDistinct := by decide

def noncommutingRightThenLeft :
    ActualTwoStepExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      noncommutingSurface mutationAdapter finalizedHistory configLawful
        .root0 where
  first := noncommutingJoinStep .rightAtRoot0
  second := noncommutingJoinStep .leftAfterRight
  occurrencesDistinct := by decide

def noncommutingCandidate :
    ExactJoinCandidate
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      noncommutingSurface mutationAdapter finalizedHistory configLawful
        .root0 .set .increment where
  leftThenRight := noncommutingLeftThenRight
  rightThenLeft := noncommutingRightThenLeft

theorem noncommuting_candidate_has_reverse_operation_orders :
    noncommutingLeftThenRight.operations = [.set, .increment] ∧
      noncommutingRightThenLeft.operations = [.increment, .set] := by
  exact ⟨rfl, rfl⟩

theorem noncommuting_candidate_has_distinct_final_states :
    noncommutingLeftThenRight.finalState ≠
      noncommutingRightThenLeft.finalState := by
  decide

theorem exact_checker_rejects_noncommuting_false_join :
    verifyExactJoin noncommutingCandidate =
      .refuse .finalStateMismatch := by
  rfl

#print axioms ProofCarryingJoinStep.toCertifiedFinalizedStep
#print axioms ActualTwoStepExecution.toSerialExecution
#print axioms verifyExactJoin
#print axioms ExactJoinCertificate.toExactCommutativeJoin
#print axioms exact_join_is_two_actual_serial_executions
#print axioms exact_join_separates_operation_and_occurrence_identity
#print axioms executable_checker_admits_the_actual_exact_join
#print axioms admitted_join_contains_both_actual_rcc45_rcc47_rcc48_traces
#print axioms admitted_join_refines_the_original_rcc50_projection
#print axioms one_sided_mutant_accepts
#print axioms exact_checker_rejects_one_sided_join
#print axioms exact_checker_rejects_reused_occurrence
#print axioms noncommuting_candidate_has_reverse_operation_orders
#print axioms noncommuting_candidate_has_distinct_final_states
#print axioms exact_checker_rejects_noncommuting_false_join

end Residua.RCC.CommutativeJoin.Tests

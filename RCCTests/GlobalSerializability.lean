import RCCTests.FinalizedHeadWindow
import RCC.FinalityLiveness
import RCC.GlobalSerializability

/-!
# RCC-47..RCC-51 Global Serializability Countermodels

The fixtures consume the concrete RCC-45 finalized-head witness, whose
admission contains the actual RCC-42 `SuccessfulFinalize` computation.

The two frozen countermodels are load-bearing:

* CM-SER-01: a second finalized event bound to the same stale state root cannot
  follow a first event that changed that root;
* CM-SER-02: an empty caller footprint cannot hide a semantic invariant domain.

Ordering is over occurrence identity.  Commutative join exactness is over
operation identity: reverse serial executions may, and normally do, carry
different RCC-45 event/occurrence identities.
-/

namespace Residua.RCC.GlobalSerializability.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability
open Residua.RCC.FinalizedHeadWindow.Tests

inductive OperationId
  | deploy
  | set
  | increment
  | left
  | right
  deriving DecidableEq

inductive ReadDomain
  | source
  deriving DecidableEq

inductive WriteDomain
  | target
  deriving DecidableEq

inductive EffectDomain
  | store
  deriving DecidableEq

inductive InvariantDomain
  | balance
  deriving DecidableEq

def surface :
    TransactionSurface
      Head
      Slot Head Judgment
      OperationId ReadDomain WriteDomain EffectDomain InvariantDomain where
  stateRoot := fun state => state
  apply := fun _ _ => .headA
  operationOf := fun _ => .deploy
  Reads := fun _ _ _ => False
  Writes := fun _ _ _ => False
  Effects := fun _ _ _ => False
  InvariantDomains := fun _ _ _ => False

def emptyFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := []
  writes := []
  effects := []
  invariantDomains := []

abbrev ActualFinalizedEvent :=
  RCC45FinalizedEvent
    (Judgment := Judgment)
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    finalizedHistory configLawful

abbrev ActualStep (state : Head) :=
  CertifiedFinalizedStep
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    (history := finalizedHistory)
    (ConfigLawful := configLawful)
    surface state

abbrev ActualSerialExecution
    (initial : Head) (occurrences : List Occurrence) (final : Head) :=
  SerialExecution
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (FailureName := FailureName)
    surface finalizedHistory configLawful initial occurrences final

def emptyFootprintComplete :
    CompleteFootprint surface .genesis proposalA emptyFootprint where
  readsExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  writesExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  effectsExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  invariantDomainsExact := by
    intro domain
    constructor <;> intro impossible <;> cases impossible

/--
The RCC-47 carrier contains the real RCC-45 certificate.  That certificate
contains the RCC-43 settled admission and RCC-42 successful finalizer.
-/
def actualFinalizedEvent :
    ActualFinalizedEvent where
  environment := admissionEnvironment
  config := .v1
  parent := .genesis
  proposal := proposalA
  certificate := headCertificate

theorem actual_event_consumes_rcc42_and_rcc45 :
    actualFinalizedEvent.certificate.admission.finalizeSuccess.accepted =
      finalizeSuccess.accepted := by
  rfl

def actualBasis :
    StateBasisBinding surface .genesis actualFinalizedEvent where
  basisRootBound := rfl
  postRootBound := rfl

def actualStep :
    ActualStep .genesis where
  finalized := actualFinalizedEvent
  footprint := emptyFootprint
  footprintComplete := emptyFootprintComplete
  basis := actualBasis

theorem proposal_is_bound_to_mutated_state_root :
    actualFinalizedEvent.proposal.expectedParent =
      surface.stateRoot .genesis :=
  finalized_step_basis_bound actualStep

/-! ## CM-SER-01 — cross-slot stale-basis double spend -/

/--
Any second concrete RCC-45 event still bound to the old root is rejected as a
successor after the first finalized event changes that root.  The second event
may have another slot and occurrence; no same-slot premise is used.
-/
theorem cm_ser_01_cross_slot_same_stale_basis_rejected
    (second : ActualFinalizedEvent)
    (sameOldBasis : second.parent = actualFinalizedEvent.parent) :
    ¬ Nonempty
      (StateBasisBinding surface
        (surface.apply .genesis actualFinalizedEvent.proposal) second) := by
  exact stale_basis_cannot_follow_root_change
    actualBasis second sameOldBasis Head.noConfusion

/-! ## CM-SER-02 — undeclared invariant domain -/

def hiddenInvariantSurface :
    TransactionSurface
      Head
      Slot Head Judgment
      OperationId ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { surface with
    InvariantDomains := fun _ _ domain => domain = .balance }

theorem cm_ser_02_empty_footprint_cannot_hide_invariant_domain :
    ¬ Nonempty
      (CompleteFootprint
        hiddenInvariantSurface .genesis proposalA emptyFootprint) := by
  rintro ⟨complete⟩
  have hiddenWasEnumerated :
      InvariantDomain.balance ∈ emptyFootprint.invariantDomains :=
    (complete.invariantDomainsExact .balance).mpr rfl
  cases hiddenWasEnumerated

/-! ## RCC-49 — ordering belongs to occurrences -/

def actualSerialHistory :
    ActualSerialExecution .genesis [.deployment] .headA :=
  .cons actualStep (.nil _) (by intro impossible; cases impossible)

theorem actual_serial_history_uses_durable_occurrence :
    actualSerialHistory.occurrences = [.deployment] := by
  rfl

theorem noncommuting_occurrences_are_history_ordered
    {initial final : Head}
    {occurrences : List Occurrence}
    (execution : ActualSerialExecution initial occurrences final)
    (left right : ActualFinalizedEvent)
    (leftMember : left.occurrenceId ∈ occurrences)
    (rightMember : right.occurrenceId ∈ occurrences)
    (distinct : left.occurrenceId ≠ right.occurrenceId)
    (conflict : ¬ OperationsCommuteAt surface initial left right) :
    OccursBefore left.occurrenceId right.occurrenceId occurrences ∧
        ¬ OccursBefore right.occurrenceId left.occurrenceId occurrences
      ∨
      OccursBefore right.occurrenceId left.occurrenceId occurrences ∧
        ¬ OccursBefore left.occurrenceId right.occurrenceId occurrences :=
  noncommuting_finalized_events_ordered
    execution left right leftMember rightMember distinct conflict

/-! ## RCC-50 — operation commutativity is not occurrence identity -/

theorem exact_join_projects_reverse_operation_orders
    {initial joined : Head}
    {leftOp rightOp : OperationId}
    (join :
      ExactCommutativeJoin
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := Occurrence)
        (FailureName := FailureName)
        surface finalizedHistory configLawful
        initial leftOp rightOp joined) :
    join.leftThenRight.operations = [leftOp, rightOp] ∧
      join.rightThenLeft.operations = [rightOp, leftOp] :=
  commutative_join_exact join

/-!
No theorem equates `join.leftThenRight.occurrences` with
`join.rightThenLeft.occurrences`: actual RCC-45 event identities remain bound
to their own parent/head snapshots.
-/

/-! ## RCC-51 — global invariant follows the actual serial trace -/

def reachableInvariant (state : Head) : Prop :=
  state = .genesis ∨ state = .headA

def reachableInvariantLaw :
    GlobalInvariantLaw
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      surface finalizedHistory configLawful reachableInvariant where
  preserves := by
    intro pre step invariant
    exact Or.inr rfl

theorem actual_serial_history_preserves_global_invariant :
    reachableInvariant .headA :=
  serial_history_preserves_global_invariant
    reachableInvariantLaw actualSerialHistory (Or.inl rfl)

/-!
## Concrete multi-event RCC-42/RCC-45 fixture

Every event below owns its own writer/effect/history snapshot and actual
`fencedFinalize = Ok` witness.  The shared `FinalizedHistoryView` supplies the
durable cross-slot history surface.
-/

namespace Concrete

open Residua.RCC
open Residua.RCC.AuthorizationFinality
open Residua.RCC.EffectSettlement
open Residua.RCC.FinalityLiveness

inductive Slot
  | setAtRoot0
  | incrementAtRoot0
  | incrementAfterSet
  | leftAtRoot0
  | rightAfterLeft
  | rightAtRoot0
  | leftAfterRight
  deriving DecidableEq

inductive Head
  | root0
  | afterSet
  | afterIncrement
  | setThenIncrement
  | incrementThenSet
  | afterLeft
  | afterRight
  | joined
  deriving DecidableEq

inductive Judgment
  | set
  | increment
  | left
  | right
  deriving DecidableEq

inductive Generation
  | current
  deriving DecidableEq

inductive Epoch
  | current
  deriving DecidableEq

inductive EffectSlot
  | store
  deriving DecidableEq

inductive Occurrence
  | setAtRoot0
  | incrementAtRoot0
  | incrementAfterSet
  | leftAtRoot0
  | rightAfterLeft
  | rightAtRoot0
  | leftAfterRight
  deriving DecidableEq

inductive FailureName
  | receiverRejected
  deriving DecidableEq

inductive EventQ
  | setAtRoot0
  | incrementAtRoot0
  | incrementAfterSet
  | leftAtRoot0
  | rightAfterLeft
  | rightAtRoot0
  | leftAfterRight
  deriving DecidableEq

def slotOf : EventQ → Slot
  | .setAtRoot0 => .setAtRoot0
  | .incrementAtRoot0 => .incrementAtRoot0
  | .incrementAfterSet => .incrementAfterSet
  | .leftAtRoot0 => .leftAtRoot0
  | .rightAfterLeft => .rightAfterLeft
  | .rightAtRoot0 => .rightAtRoot0
  | .leftAfterRight => .leftAfterRight

def parentOf : EventQ → Head
  | .setAtRoot0 => .root0
  | .incrementAtRoot0 => .root0
  | .incrementAfterSet => .afterSet
  | .leftAtRoot0 => .root0
  | .rightAfterLeft => .afterLeft
  | .rightAtRoot0 => .root0
  | .leftAfterRight => .afterRight

def headOf : EventQ → Head
  | .setAtRoot0 => .afterSet
  | .incrementAtRoot0 => .afterIncrement
  | .incrementAfterSet => .setThenIncrement
  | .leftAtRoot0 => .afterLeft
  | .rightAfterLeft => .joined
  | .rightAtRoot0 => .afterRight
  | .leftAfterRight => .joined

def judgmentOf : EventQ → Judgment
  | .setAtRoot0 => .set
  | .incrementAtRoot0 => .increment
  | .incrementAfterSet => .increment
  | .leftAtRoot0 => .left
  | .rightAfterLeft => .right
  | .rightAtRoot0 => .right
  | .leftAfterRight => .left

def occurrenceOfEvent : EventQ → Occurrence
  | .setAtRoot0 => .setAtRoot0
  | .incrementAtRoot0 => .incrementAtRoot0
  | .incrementAfterSet => .incrementAfterSet
  | .leftAtRoot0 => .leftAtRoot0
  | .rightAfterLeft => .rightAfterLeft
  | .rightAtRoot0 => .rightAtRoot0
  | .leftAfterRight => .leftAfterRight

def occurrenceOfSlot : Slot → Occurrence
  | .setAtRoot0 => .setAtRoot0
  | .incrementAtRoot0 => .incrementAtRoot0
  | .incrementAfterSet => .incrementAfterSet
  | .leftAtRoot0 => .leftAtRoot0
  | .rightAfterLeft => .rightAfterLeft
  | .rightAtRoot0 => .rightAtRoot0
  | .leftAfterRight => .leftAfterRight

def slotParent : Slot → Head
  | .setAtRoot0 => .root0
  | .incrementAtRoot0 => .root0
  | .incrementAfterSet => .afterSet
  | .leftAtRoot0 => .root0
  | .rightAfterLeft => .afterLeft
  | .rightAtRoot0 => .root0
  | .leftAfterRight => .afterRight

def proposalOf (event : EventQ) : Proposal Slot Head Judgment :=
  ⟨slotOf event, parentOf event, judgmentOf event⟩

/--
The concrete authority language is indexed by the exact event proposal.
Unlike a constant receipt type, this witness cannot authorize another slot,
parent, or judgment.
-/
inductive AuthorityEvidence : Proposal Slot Head Judgment → Type
  | quorum (event : EventQ) : AuthorityEvidence (proposalOf event)

def writerSpec : FencedWriterSpec Slot Head where
  slotParent := slotParent

def judgmentEq : JudgmentEquivalence Judgment where
  Equivalent := Eq
  refl := by intro _; rfl
  symm := by intro _ _ equality; exact equality.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide := fun first second => inferInstanceAs (Decidable (first = second))

def authorization (event : EventQ) :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨proposalOf event, .quorum event⟩

def writerState (event : EventQ) :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := parentOf event
  decisions := fun _ => some (judgmentOf event)

def finalizeRequest (event : EventQ) :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨authorization event, .current⟩

def canonicalReady (event : EventQ) :
    CanonicalFinalizeReady writerSpec (writerState event)
      (finalizeRequest event) := by
  cases event <;>
    exact {
      slotBound := rfl
      parentBound := rfl
      generationBound := rfl
      decisionCommitted := rfl
    }

def finalizeSuccess (event : EventQ) :
    SuccessfulFinalize writerSpec judgmentEq (writerState event)
      (finalizeRequest event) :=
  successfulFinalizeOfReady
    writerSpec judgmentEq (writerState event) (finalizeRequest event)
      (canonicalReady event)

def externalEffect (event : EventQ) :
    ExternalEffect Occurrence Head EffectSlot :=
  ⟨occurrenceOfEvent event, parentOf event, .store⟩

def effectReceipt (event : EventQ) :
    EffectReceipt
      Epoch Head EffectSlot Generation Occurrence FailureName where
  occurrence := occurrenceOfEvent event
  fence := {
    epoch := .current
    head := parentOf event
    effectSlot := .store
    generation := .current
  }
  phase := .recorded

def effectObservation (event : EventQ) :
    EffectObservation
      Epoch Head EffectSlot Generation Occurrence FailureName where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some (effectReceipt event)

def effectSnapshot (event : EventQ) :
    EffectSnapshot
      Epoch Head EffectSlot Generation Occurrence FailureName where
  epoch := .current
  head := parentOf event
  currentGeneration := fun _ => .current
  policyTerminalFailure := fun _ => False
  externalEffects := [externalEffect event]
  observe := fun _ => some (effectObservation event)

def historyEventView :
    HistoryEventView EventQ Slot Head Judgment Occurrence where
  preHead := parentOf
  slot := slotOf
  judgment := judgmentOf
  occurrence := occurrenceOfEvent

def canonicalHistory (event : EventQ) :
    CanonicalHistorySnapshot EventQ Head where
  canonicalHead := parentOf event
  contains := fun _ => true
  durableContains := fun _ => True
  containsSound := by intro _ _; trivial

def admissionEnvironment (event : EventQ) :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ where
  writerSpec := writerSpec
  equivalence := judgmentEq
  writerState := writerState event
  effectSnapshot := effectSnapshot event
  historyView := historyEventView
  historySnapshot := canonicalHistory event
  occurrenceOf := fun proposal => occurrenceOfSlot proposal.slot
  effectSlotOf := fun _ => .store
  effectHeadBound := rfl
  historyHeadBound := rfl
  generationCoherent := by intro _; rfl

def settledAdmission (event : EventQ) :
    SettledAdmission (admissionEnvironment event) (proposalOf event) where
  finalizeRequest := finalizeRequest event
  proposalBound := rfl
  finalizeSuccess := finalizeSuccess event
  effect := externalEffect event
  effectDeclared := List.Mem.head _
  effectOccurrenceBound := by cases event <;> rfl
  effectParentBound := rfl
  effectSlotBound := rfl
  effectObservation := effectObservation event
  effectReceipt := effectReceipt event
  settled := {
    observed := rfl
    receiptPresent := rfl
    epochBound := rfl
    expectedParentBound := rfl
    canonicalHeadBound := rfl
    slotBound := rfl
    generationBound := rfl
    occurrenceBound := rfl
    coherent := ⟨rfl, rfl, rfl⟩
  }
  history := {
    event := event
    recorded := rfl
    durablyRecorded := True.intro
    canonicalHeadBound := rfl
    preHeadBound := rfl
    slotBound := rfl
    judgmentBound := rfl
    occurrenceBound := by cases event <;> rfl
  }

def finalizedHistory :
    FinalizedHistoryView EventQ Slot Head Unit where
  slot := slotOf
  successorHead := headOf
  config := fun _ => ()
  finalized := fun _ => True
  sameSlotUnique := by
    intro first second _ _ sameSlot
    cases first <;> cases second <;> cases sameSlot <;> exact ⟨rfl, rfl⟩

def configLawful (_ : Unit) : Prop :=
  True

abbrev ConcreteFinalizedEvent :=
  RCC45FinalizedEvent
    (Judgment := Judgment)
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    finalizedHistory configLawful

def headCertificate (event : EventQ) :
    FinalizedHeadCert
      (admissionEnvironment event) finalizedHistory configLawful ()
        (parentOf event) (proposalOf event) where
  admission := settledAdmission event
  head := headOf event
  configLawful := True.intro
  parentBound := rfl
  historyFinalized := True.intro
  historySlotBound := rfl
  historyHeadBound := rfl
  historyConfigBound := rfl

def finalizedEvent (event : EventQ) :
    ConcreteFinalizedEvent where
  environment := admissionEnvironment event
  config := ()
  parent := parentOf event
  proposal := proposalOf event
  certificate := headCertificate event

def concreteSurface :
    TransactionSurface
      Head Slot Head Judgment OperationId
        ReadDomain WriteDomain EffectDomain InvariantDomain where
  stateRoot := fun state => state
  apply := fun state proposal =>
    match state, proposal.judgment with
    | .root0, .set => .afterSet
    | .root0, .increment => .afterIncrement
    | .afterSet, .increment => .setThenIncrement
    | .afterIncrement, .set => .incrementThenSet
    | .root0, .left => .afterLeft
    | .afterLeft, .right => .joined
    | .root0, .right => .afterRight
    | .afterRight, .left => .joined
    | state, _ => state
  operationOf := fun proposal =>
    match proposal.judgment with
    | .set => .set
    | .increment => .increment
    | .left => .left
    | .right => .right
  Reads := fun _ _ _ => False
  Writes := fun _ _ _ => False
  Effects := fun _ _ _ => False
  InvariantDomains := fun _ _ _ => False

abbrev ConcreteStep (state : Head) :=
  CertifiedFinalizedStep
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    (history := finalizedHistory)
    (ConfigLawful := configLawful)
    concreteSurface state

abbrev ConcreteSerialExecution
    (initial : Head) (occurrences : List Occurrence) (final : Head) :=
  SerialExecution
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (FailureName := FailureName)
    concreteSurface finalizedHistory configLawful initial occurrences final

def completeFootprint (state : Head) (event : EventQ) :
    CompleteFootprint
      concreteSurface state (proposalOf event) emptyFootprint where
  readsExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  writesExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  effectsExact := by intro domain; constructor <;> intro impossible <;> cases impossible
  invariantDomainsExact := by
    intro domain
    constructor <;> intro impossible <;> cases impossible

def basisForEvent (event : EventQ) :
    StateBasisBinding concreteSurface (parentOf event)
      (finalizedEvent event) := by
  cases event <;>
    exact {
      basisRootBound := rfl
      postRootBound := rfl
    }

def stepForEvent (event : EventQ) :
    ConcreteStep (parentOf event) where
  finalized := finalizedEvent event
  footprint := emptyFootprint
  footprintComplete := completeFootprint (parentOf event) event
  basis := basisForEvent event

theorem all_fixture_events_are_actual_rcc42_successes
    (event : EventQ) :
    fencedFinalize writerSpec judgmentEq (writerState event)
        (finalizeRequest event) =
      .Ok (finalizeSuccess event).output :=
  (finalizeSuccess event).accepted

theorem cm_ser_01_two_slots_finalize_but_stale_pair_cannot_serialize :
    fencedFinalize writerSpec judgmentEq (writerState .setAtRoot0)
        (finalizeRequest .setAtRoot0) =
        .Ok (finalizeSuccess .setAtRoot0).output ∧
      fencedFinalize writerSpec judgmentEq (writerState .incrementAtRoot0)
        (finalizeRequest .incrementAtRoot0) =
        .Ok (finalizeSuccess .incrementAtRoot0).output ∧
      slotOf .setAtRoot0 ≠ slotOf .incrementAtRoot0 ∧
      occurrenceOfEvent .setAtRoot0 ≠
        occurrenceOfEvent .incrementAtRoot0 ∧
      ¬ Nonempty
        (StateBasisBinding concreteSurface .afterSet
          (finalizedEvent .incrementAtRoot0)) := by
  refine
    ⟨(finalizeSuccess .setAtRoot0).accepted,
      (finalizeSuccess .incrementAtRoot0).accepted,
      by decide, by decide, ?_⟩
  exact stale_basis_cannot_follow_root_change
    (basisForEvent .setAtRoot0) (finalizedEvent .incrementAtRoot0)
      rfl Head.noConfusion

def setThenIncrementTrace :
    ConcreteSerialExecution
      .root0 [.setAtRoot0, .incrementAfterSet] .setThenIncrement :=
  .cons (stepForEvent .setAtRoot0)
    (.cons (stepForEvent .incrementAfterSet) (.nil _) (by decide))
    (by decide)

theorem set_and_increment_do_not_commute :
    ¬ OperationsCommuteAt concreteSurface .root0
      (finalizedEvent .setAtRoot0)
      (finalizedEvent .incrementAfterSet) := by
  intro impossible
  cases impossible

theorem concrete_noncommuting_actual_trace_has_unique_order :
    OccursBefore
        Occurrence.setAtRoot0 Occurrence.incrementAfterSet
        setThenIncrementTrace.occurrences ∧
      ¬ OccursBefore
        Occurrence.incrementAfterSet Occurrence.setAtRoot0
        setThenIncrementTrace.occurrences :=
  by
    rcases
        noncommuting_finalized_events_ordered
          setThenIncrementTrace
          (finalizedEvent .setAtRoot0)
          (finalizedEvent .incrementAfterSet)
          (by exact List.Mem.head _)
          (by exact List.Mem.tail _ (List.Mem.head _))
          (by decide)
          set_and_increment_do_not_commute with
      ordered | reverse
    · exact ordered
    · have forward :
          OccursBefore
            Occurrence.setAtRoot0 Occurrence.incrementAfterSet
            setThenIncrementTrace.occurrences :=
        OccursBefore.here (List.Mem.head _)
      exact False.elim (reverse.2 forward)

def leftThenRightTrace :
    ConcreteSerialExecution
      .root0 [.leftAtRoot0, .rightAfterLeft] .joined :=
  .cons (stepForEvent .leftAtRoot0)
    (.cons (stepForEvent .rightAfterLeft) (.nil _) (by decide))
    (by decide)

def rightThenLeftTrace :
    ConcreteSerialExecution
      .root0 [.rightAtRoot0, .leftAfterRight] .joined :=
  .cons (stepForEvent .rightAtRoot0)
    (.cons (stepForEvent .leftAfterRight) (.nil _) (by decide))
    (by decide)

def concreteExactJoin :
    ExactCommutativeJoin
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface finalizedHistory configLawful
      .root0 .left .right .joined where
  leftOccurrences := [.leftAtRoot0, .rightAfterLeft]
  rightOccurrences := [.rightAtRoot0, .leftAfterRight]
  leftThenRight := leftThenRightTrace
  rightThenLeft := rightThenLeftTrace
  leftOperations := rfl
  rightOperations := rfl

theorem concrete_join_has_reverse_operations_distinct_occurrences_same_result :
    concreteExactJoin.leftThenRight.operations = [.left, .right] ∧
      concreteExactJoin.rightThenLeft.operations = [.right, .left] ∧
      concreteExactJoin.leftThenRight.occurrences ≠
        concreteExactJoin.rightThenLeft.occurrences :=
  ⟨(commutative_join_exact concreteExactJoin).1,
    (commutative_join_exact concreteExactJoin).2,
    by decide⟩

theorem reverse_join_occurrences_rebind_parent :
    (finalizedEvent .leftAtRoot0).parent ≠
        (finalizedEvent .leftAfterRight).parent ∧
      (finalizedEvent .leftAtRoot0).occurrenceId ≠
        (finalizedEvent .leftAfterRight).occurrenceId ∧
      (finalizedEvent .rightAtRoot0).parent ≠
        (finalizedEvent .rightAfterLeft).parent ∧
      (finalizedEvent .rightAtRoot0).occurrenceId ≠
        (finalizedEvent .rightAfterLeft).occurrenceId := by
  decide

def noUncertifiedIncrementThenSet (state : Head) : Prop :=
  state ≠ .incrementThenSet

def concreteInvariantLaw :
    GlobalInvariantLaw
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      concreteSurface finalizedHistory configLawful
        noUncertifiedIncrementThenSet where
  preserves := by
    intro pre step invariant
    intro postIsUncertified
    have certificateIsUncertified :
        step.finalized.certificate.head = .incrementThenSet :=
      step.basis.postRootBound.symm.trans postIsUncertified
    have historyIsUncertified :
        finalizedHistory.successorHead
            step.finalized.certificate.admission.history.event =
          .incrementThenSet :=
      step.finalized.certificate.historyHeadBound.trans
        certificateIsUncertified
    generalize eventEquation :
      step.finalized.certificate.admission.history.event = event at historyIsUncertified
    cases event <;>
      cases historyIsUncertified

theorem concrete_two_step_history_preserves_global_invariant :
    noUncertifiedIncrementThenSet .setThenIncrement :=
  serial_history_preserves_global_invariant
    concreteInvariantLaw setThenIncrementTrace Head.noConfusion

#print axioms all_fixture_events_are_actual_rcc42_successes
#print axioms cm_ser_01_two_slots_finalize_but_stale_pair_cannot_serialize
#print axioms set_and_increment_do_not_commute
#print axioms concrete_noncommuting_actual_trace_has_unique_order
#print axioms concrete_join_has_reverse_operations_distinct_occurrences_same_result
#print axioms reverse_join_occurrences_rebind_parent
#print axioms concrete_two_step_history_preserves_global_invariant

end Concrete

#print axioms actual_event_consumes_rcc42_and_rcc45
#print axioms proposal_is_bound_to_mutated_state_root
#print axioms finalized_step_basis_bound
#print axioms stale_basis_cannot_follow_root_change
#print axioms cm_ser_01_cross_slot_same_stale_basis_rejected
#print axioms cm_ser_02_empty_footprint_cannot_hide_invariant_domain
#print axioms occursBefore_total
#print axioms occursBefore_asymmetric
#print axioms noncommuting_finalized_events_ordered
#print axioms commutative_join_exact
#print axioms exact_join_projects_reverse_operation_orders
#print axioms serial_history_preserves_global_invariant
#print axioms actual_serial_history_preserves_global_invariant

end Residua.RCC.GlobalSerializability.Tests

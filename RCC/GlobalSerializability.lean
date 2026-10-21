import RCC.FinalizedHeadWindow

/-!
# RCC-47..RCC-51 Global Serializability

This finite safety kernel connects state-root validation, exact transaction
footprints, occurrence ordering, exact commutative joins, and global invariant
preservation to the actual RCC-45 finalized-history surface.  Every event
contains a concrete `FinalizedHeadCert`; transitively, that certificate
contains the RCC-43 settled admission and RCC-42 successful finalizer
computation.

Identity roles remain separate:

* serial order is over concrete occurrence identity;
* commutativity is over operation identity;
* reverse serial executions may use different parent-bound occurrences.

The kernel does not infer footprints, discover commutativity, schedule a
distributed runtime, prove liveness, construct RCC-45 certificates, or model
infinite histories.  It proves only finite, proof-carrying safety statements
relative to the supplied domain semantics and actual finalized events.

Prelude-only Lean 4.14; no Mathlib, admitted proof gaps, declared assumptions,
or kernel-evaluation shortcuts.
-/

namespace Residua.RCC.GlobalSerializability

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow

universe u

/--
Existential environment packaging for one actual RCC-45 finalized event.
Successive history events may use different writer/effect snapshots while
remaining members of one durable finalized-history view.
-/
structure RCC45FinalizedEvent
    {Slot Head Judgment Generation Epoch EffectSlot OccurrenceId FailureName
      EventQ Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop) where
  environment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
        OccurrenceId FailureName EventQ
  config : Config
  parent : Head
  proposal : Proposal Slot Head Judgment
  certificate :
    FinalizedHeadCert
      environment history ConfigLawful config parent proposal

/-- Concrete durable occurrence identity carried by the RCC-43 history edge. -/
def RCC45FinalizedEvent.occurrenceId
    {Slot Head Judgment Generation Epoch EffectSlot OccurrenceId FailureName
      EventQ Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (event :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful) : OccurrenceId :=
  event.environment.historyView.occurrence
    event.certificate.admission.history.event

/--
Domain semantics used by the serializability kernel.  Access relations are
semantic predicates; callers do not supply a `serializable` Boolean.
-/
structure TransactionSurface
    (State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u) where
  stateRoot : State → Head
  apply : State → Proposal Slot Head Judgment → State
  operationOf : Proposal Slot Head Judgment → OperationId
  Reads : State → Proposal Slot Head Judgment → ReadDomain → Prop
  Writes : State → Proposal Slot Head Judgment → WriteDomain → Prop
  Effects : State → Proposal Slot Head Judgment → EffectDomain → Prop
  InvariantDomains :
    State → Proposal Slot Head Judgment → InvariantDomain → Prop

/-- A finite claimed transaction footprint, prior to exactness proof. -/
structure TransactionFootprint
    (ReadDomain WriteDomain EffectDomain InvariantDomain : Type u) where
  reads : List ReadDomain
  writes : List WriteDomain
  effects : List EffectDomain
  invariantDomains : List InvariantDomain

/--
RCC-48 footprint exactness.  Every listed coordinate is semantic and every
semantic coordinate is listed, across all four load-bearing dimensions.
-/
structure CompleteFootprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (state : State)
    (proposal : Proposal Slot Head Judgment)
    (footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain) : Prop where
  readsExact :
    ∀ domain,
      domain ∈ footprint.reads ↔ surface.Reads state proposal domain
  writesExact :
    ∀ domain,
      domain ∈ footprint.writes ↔ surface.Writes state proposal domain
  effectsExact :
    ∀ domain,
      domain ∈ footprint.effects ↔ surface.Effects state proposal domain
  invariantDomainsExact :
    ∀ domain,
      domain ∈ footprint.invariantDomains ↔
        surface.InvariantDomains state proposal domain

/--
RCC-47 binds the proposal's certified parent to the state root it mutates and
binds the resulting state root to the actual RCC-45 successor head.
-/
structure StateBasisBinding
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
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
        history ConfigLawful) : Prop where
  basisRootBound : surface.stateRoot preState = finalized.parent
  postRootBound :
    surface.stateRoot (surface.apply preState finalized.proposal) =
      finalized.certificate.head

/-- One actual finalized transition with an exact four-dimensional footprint. -/
structure CertifiedFinalizedStep
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
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
  footprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain
  footprintComplete :
    CompleteFootprint surface preState finalized.proposal footprint
  basis : StateBasisBinding surface preState finalized

/--
RCC-47: the concrete proposal parent is exactly the root of the state being
mutated.  The first equality is retained by RCC-45, not reconstructed here.
-/
theorem finalized_step_basis_bound
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
    {preState : State}
    (step :
      CertifiedFinalizedStep
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        (history := history)
        (ConfigLawful := ConfigLawful)
        surface preState) :
    step.finalized.proposal.expectedParent = surface.stateRoot preState := by
  exact step.finalized.certificate.parentBound.trans
    step.basis.basisRootBound.symm

/--
CM-SER-01 kernel: after an event changes the root, another actual finalized
event bound to the old root cannot acquire a successor state-basis proof.
No same-slot premise is used.
-/
theorem stale_basis_cannot_follow_root_change
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
    {preState : State}
    {first :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful}
    (firstBasis : StateBasisBinding surface preState first)
    (second :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (sameOldBasis : second.parent = first.parent)
    (rootChanged : first.certificate.head ≠ first.parent) :
    ¬ Nonempty
      (StateBasisBinding
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface
        (surface.apply preState first.proposal) second) := by
  intro successor
  obtain ⟨secondBasis⟩ := successor
  apply rootChanged
  exact firstBasis.postRootBound.symm.trans
    (secondBasis.basisRootBound.trans sameOldBasis)

/--
A finite actual serial execution.  The state index of each tail is the exact
post-state of its preceding certified step.  Occurrence freshness prevents
one durable event from occupying two schedule positions.
-/
inductive SerialExecution
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop) :
    State → List OccurrenceId → State → Type u
  | nil (state : State) :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful state [] state
  | cons
      {preState finalState : State}
      {tailOccurrences : List OccurrenceId}
      (step :
        CertifiedFinalizedStep
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (OccurrenceId := OccurrenceId)
          (FailureName := FailureName)
          (history := history)
          (ConfigLawful := ConfigLawful)
          surface preState)
      (tail :
        SerialExecution
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (FailureName := FailureName)
          surface history ConfigLawful
          (surface.apply preState step.finalized.proposal)
          tailOccurrences finalState)
      (fresh : step.finalized.occurrenceId ∉ tailOccurrences) :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        preState (step.finalized.occurrenceId :: tailOccurrences) finalState

/-- The occurrence schedule is the execution's type index. -/
def SerialExecution.occurrences
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
    {initial final : State} {occurrences : List OccurrenceId}
    (_execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial occurrences final) :
    List OccurrenceId :=
  occurrences

/-- Operation projection deliberately erases occurrence/parent identity. -/
def SerialExecution.operations
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
    {initial final : State} {occurrences : List OccurrenceId}
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial occurrences final) :
    List OperationId :=
  match execution with
  | .nil _ => []
  | .cons step tail _ =>
      surface.operationOf step.finalized.proposal :: tail.operations

/-- A left occurrence is before a right occurrence in one concrete schedule. -/
inductive OccursBefore {OccurrenceId : Type u}
    (left right : OccurrenceId) : List OccurrenceId → Prop
  | here {tail : List OccurrenceId} :
      right ∈ tail →
      OccursBefore left right (left :: tail)
  | there {head : OccurrenceId} {tail : List OccurrenceId} :
      OccursBefore left right tail →
      OccursBefore left right (head :: tail)

/-- Every ordered occurrence is present at the left endpoint. -/
theorem OccursBefore.left_mem
    {OccurrenceId : Type u}
    {left right : OccurrenceId} {schedule : List OccurrenceId}
    (ordered : OccursBefore left right schedule) :
    left ∈ schedule := by
  induction ordered with
  | here _ => exact List.Mem.head _
  | there prior inductionHypothesis =>
      exact List.Mem.tail _ inductionHypothesis

/-- Every ordered occurrence is present at the right endpoint. -/
theorem OccursBefore.right_mem
    {OccurrenceId : Type u}
    {left right : OccurrenceId} {schedule : List OccurrenceId}
    (ordered : OccursBefore left right schedule) :
    right ∈ schedule := by
  induction ordered with
  | here member => exact List.Mem.tail _ member
  | there prior inductionHypothesis =>
      exact List.Mem.tail _ inductionHypothesis

/-- Distinct members of a finite list have a schedule order. -/
theorem occursBefore_total
    {OccurrenceId : Type u}
    {left right : OccurrenceId} {schedule : List OccurrenceId}
    (leftMember : left ∈ schedule)
    (rightMember : right ∈ schedule)
    (distinct : left ≠ right) :
    OccursBefore left right schedule ∨
      OccursBefore right left schedule := by
  induction schedule with
  | nil => cases leftMember
  | cons head tail inductionHypothesis =>
      cases leftMember with
      | head =>
          cases rightMember with
          | head => exact False.elim (distinct rfl)
          | tail _ rightTail =>
              exact Or.inl (OccursBefore.here rightTail)
      | tail _ leftTail =>
          cases rightMember with
          | head => exact Or.inr (OccursBefore.here leftTail)
          | tail _ rightTail =>
              cases inductionHypothesis leftTail rightTail with
              | inl ordered =>
                  exact Or.inl (OccursBefore.there ordered)
              | inr ordered =>
                  exact Or.inr (OccursBefore.there ordered)

/-- Occurrence freshness makes every serial schedule duplicate-free. -/
theorem SerialExecution.occurrences_nodup
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
    {initial final : State} {occurrences : List OccurrenceId}
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial occurrences final) :
    occurrences.Nodup := by
  induction execution with
  | nil => exact List.Pairwise.nil
  | cons step tail fresh inductionHypothesis =>
      exact List.Pairwise.cons
        (by
          intro other member equal
          apply fresh
          rw [equal]
          exact member)
        inductionHypothesis

/-- A duplicate-free schedule cannot order one pair in both directions. -/
theorem occursBefore_asymmetric
    {OccurrenceId : Type u}
    {left right : OccurrenceId} {schedule : List OccurrenceId}
    (nodup : schedule.Nodup)
    (ordered : OccursBefore left right schedule) :
    ¬ OccursBefore right left schedule := by
  induction ordered with
  | @here tail rightMember =>
      intro reverse
      cases nodup with
      | cons leftAbsent tailNodup =>
          cases reverse with
          | here leftMember =>
              exact leftAbsent _ rightMember rfl
          | there reverseTail =>
              exact leftAbsent _ reverseTail.right_mem rfl
  | @there head tail prior inductionHypothesis =>
      intro reverse
      cases nodup with
      | cons headAbsent tailNodup =>
          cases reverse with
          | here leftMember =>
              exact headAbsent _ prior.right_mem rfl
          | there reverseTail =>
              exact
                (inductionHypothesis tailNodup) reverseTail

/-- Semantic commutativity is equality of the two operation executions. -/
def OperationsCommuteAt
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (state : State)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (left right :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful) : Prop :=
  surface.apply (surface.apply state left.proposal) right.proposal =
    surface.apply (surface.apply state right.proposal) left.proposal

/--
RCC-49: every distinct, semantically noncommuting pair in an actual finalized
serial execution has exactly one occurrence order.
-/
theorem noncommuting_finalized_events_ordered
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
    {initial final : State} {occurrences : List OccurrenceId}
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial occurrences final)
    (left right :
      RCC45FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (leftMember : left.occurrenceId ∈ occurrences)
    (rightMember : right.occurrenceId ∈ occurrences)
    (distinct : left.occurrenceId ≠ right.occurrenceId)
    (_noncommuting :
      ¬ OperationsCommuteAt
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface initial left right) :
    OccursBefore left.occurrenceId right.occurrenceId occurrences ∧
        ¬ OccursBefore right.occurrenceId left.occurrenceId occurrences
      ∨
      OccursBefore right.occurrenceId left.occurrenceId occurrences ∧
        ¬ OccursBefore left.occurrenceId right.occurrenceId occurrences := by
  cases occursBefore_total leftMember rightMember distinct with
  | inl ordered =>
      exact Or.inl
        ⟨ordered,
          occursBefore_asymmetric execution.occurrences_nodup ordered⟩
  | inr ordered =>
      exact Or.inr
        ⟨ordered,
          occursBefore_asymmetric execution.occurrences_nodup ordered⟩

/--
RCC-50 exact join: two actual RCC-45-certified serial traces project to
opposite operation orders and share one final state.  Their occurrence lists
are deliberately unconstrained and may differ.
-/
structure ExactCommutativeJoin
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State) (leftOperation rightOperation : OperationId)
    (joined : State) where
  leftOccurrences : List OccurrenceId
  rightOccurrences : List OccurrenceId
  leftThenRight :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful
      initial leftOccurrences joined
  rightThenLeft :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful
      initial rightOccurrences joined
  leftOperations :
    leftThenRight.operations = [leftOperation, rightOperation]
  rightOperations :
    rightThenLeft.operations = [rightOperation, leftOperation]

/-- RCC-50 exposes both exact legal serial operation projections. -/
theorem commutative_join_exact
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
    {initial joined : State}
    {leftOperation rightOperation : OperationId}
    (join :
      ExactCommutativeJoin
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial leftOperation rightOperation joined) :
    join.leftThenRight.operations = [leftOperation, rightOperation] ∧
      join.rightThenLeft.operations = [rightOperation, leftOperation] :=
  ⟨join.leftOperations, join.rightOperations⟩

/-- Per-step global invariant law over actual finalized, exact-footprint steps. -/
structure GlobalInvariantLaw
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (GlobalInvariant : State → Prop) : Prop where
  preserves :
    ∀ preState
      (step :
        CertifiedFinalizedStep
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (OccurrenceId := OccurrenceId)
          (FailureName := FailureName)
          (history := history)
          (ConfigLawful := ConfigLawful)
          surface preState),
      GlobalInvariant preState →
      GlobalInvariant
        (surface.apply preState step.finalized.proposal)

/--
RCC-51: induction over the actual serial execution preserves the global
invariant from the initial state to the finalized end state.
-/
theorem serial_history_preserves_global_invariant
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
    {GlobalInvariant : State → Prop}
    (law :
      GlobalInvariantLaw
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface history ConfigLawful GlobalInvariant)
    {initial final : State} {occurrences : List OccurrenceId}
    (execution :
      SerialExecution
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface history ConfigLawful
        initial occurrences final)
    (initialInvariant : GlobalInvariant initial) :
    GlobalInvariant final := by
  induction execution with
  | nil => exact initialInvariant
  | cons step tail fresh inductionHypothesis =>
      exact inductionHypothesis (law.preserves _ step initialInvariant)

end Residua.RCC.GlobalSerializability

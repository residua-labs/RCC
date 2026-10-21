import RCC.MetaFailureExhaustion

/-!
# RCC closure exhaustion

Closure is stronger than an empty ready frontier.  This module derives three
state-indexed negative projections from sealed universes and proof-carrying raw
evidence:

* every nonterminal workflow state, including blocked/runtime/stuck;
* every mandatory ME-1 failure lacking a terminal disposition certificate; and
* every pending reepoch candidate.

Instances provide universes, evidence readers, certificate checkers, and exact
coverage proofs.  They never provide an `active := []`, `quiescent := true`, or
packet-local status field.  Unknown or inconsistent evidence is conservatively
kept active.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.ClosureExhaustion

open Residua.RCC.EffectClassification
open Residua.RCC.FailureCoverage
open Residua.RCC.MetaFailureExhaustion

universe u v w x

/-! ## 1. Orthogonal semantic/workflow derivation -/

inductive OpenMode
  | ordinary
  | disputed
  deriving DecidableEq, Repr

inductive WorkflowState
  | ready
  | blocked
  | runtime
  | stuck
  deriving DecidableEq, Repr

inductive GoalDispositionTag
  | terminal
  | open (mode : OpenMode) (workflow : WorkflowState)
  deriving DecidableEq, Repr

inductive DispositionResidue
  | evidenceGap
  | inconsistentEvidence
  deriving DecidableEq, Repr

/--
Raw proof coordinates for one live goal.  `disputed` is orthogonal to the four
workflow coordinates; it is not a competing fifth workflow status.
-/
structure WorkflowFacts
    (Terminal Disputed Ready Blocked Runtime Stuck : Prop) where
  terminal : EvidenceState Terminal
  disputed : EvidenceState Disputed
  ready : EvidenceState Ready
  blocked : EvidenceState Blocked
  runtime : EvidenceState Runtime
  stuck : EvidenceState Stuck

def WorkflowFacts.hasUnknown
    {Terminal Disputed Ready Blocked Runtime Stuck : Prop}
    (facts : WorkflowFacts Terminal Disputed Ready Blocked Runtime Stuck) : Bool :=
  facts.terminal.isUnknown ||
    facts.disputed.isUnknown ||
    facts.ready.isUnknown ||
    facts.blocked.isUnknown ||
    facts.runtime.isUnknown ||
    facts.stuck.isUnknown

inductive OpenModeEvidence (Disputed : Prop)
  | ordinary (refuted : ¬ Disputed)
  | disputed (supported : Disputed)

inductive WorkflowEvidence
    (Ready Blocked Runtime Stuck : Prop)
  | ready
      (supported : Ready)
      (notBlocked : ¬ Blocked)
      (notRuntime : ¬ Runtime)
      (notStuck : ¬ Stuck)
  | blocked
      (notReady : ¬ Ready)
      (supported : Blocked)
      (notRuntime : ¬ Runtime)
      (notStuck : ¬ Stuck)
  | runtime
      (notReady : ¬ Ready)
      (notBlocked : ¬ Blocked)
      (supported : Runtime)
      (notStuck : ¬ Stuck)
  | stuck
      (notReady : ¬ Ready)
      (notBlocked : ¬ Blocked)
      (notRuntime : ¬ Runtime)
      (supported : Stuck)

inductive CertifiedGoalDisposition
    (Terminal Disputed Ready Blocked Runtime Stuck : Prop)
  | terminal
      (supported : Terminal)
      (notDisputed : ¬ Disputed)
      (notReady : ¬ Ready)
      (notBlocked : ¬ Blocked)
      (notRuntime : ¬ Runtime)
      (notStuck : ¬ Stuck)
  | open
      (notTerminal : ¬ Terminal)
      (mode : OpenModeEvidence Disputed)
      (workflow : WorkflowEvidence Ready Blocked Runtime Stuck)

def OpenModeEvidence.tag {Disputed : Prop} :
    OpenModeEvidence Disputed → OpenMode
  | .ordinary _ => .ordinary
  | .disputed _ => .disputed

def WorkflowEvidence.tag {Ready Blocked Runtime Stuck : Prop} :
    WorkflowEvidence Ready Blocked Runtime Stuck → WorkflowState
  | .ready .. => .ready
  | .blocked .. => .blocked
  | .runtime .. => .runtime
  | .stuck .. => .stuck

def CertifiedGoalDisposition.tag
    {Terminal Disputed Ready Blocked Runtime Stuck : Prop} :
    CertifiedGoalDisposition Terminal Disputed Ready Blocked Runtime Stuck →
      GoalDispositionTag
  | .terminal .. => .terminal
  | .open _ mode workflow => .open mode.tag workflow.tag

inductive GoalDispositionResult
    (Terminal Disputed Ready Blocked Runtime Stuck : Prop)
  | classified
      (disposition :
        CertifiedGoalDisposition
          Terminal Disputed Ready Blocked Runtime Stuck)
  | refuse (residue : DispositionResidue)

/-- The sole goal-state classifier.  No priority silently hides overlap. -/
def deriveGoalDisposition
    {Terminal Disputed Ready Blocked Runtime Stuck : Prop}
    (facts : WorkflowFacts Terminal Disputed Ready Blocked Runtime Stuck) :
    GoalDispositionResult Terminal Disputed Ready Blocked Runtime Stuck :=
  if facts.hasUnknown then
    .refuse .evidenceGap
  else
    match facts.terminal, facts.disputed, facts.ready, facts.blocked,
        facts.runtime, facts.stuck with
    | .supported terminal, .refuted notDisputed, .refuted notReady,
        .refuted notBlocked, .refuted notRuntime, .refuted notStuck =>
        .classified
          (.terminal terminal notDisputed notReady notBlocked notRuntime notStuck)
    | .refuted notTerminal, .refuted notDisputed, .supported ready,
        .refuted notBlocked, .refuted notRuntime, .refuted notStuck =>
        .classified
          (.open notTerminal (.ordinary notDisputed)
            (.ready ready notBlocked notRuntime notStuck))
    | .refuted notTerminal, .supported disputed, .supported ready,
        .refuted notBlocked, .refuted notRuntime, .refuted notStuck =>
        .classified
          (.open notTerminal (.disputed disputed)
            (.ready ready notBlocked notRuntime notStuck))
    | .refuted notTerminal, .refuted notDisputed, .refuted notReady,
        .supported blocked, .refuted notRuntime, .refuted notStuck =>
        .classified
          (.open notTerminal (.ordinary notDisputed)
            (.blocked notReady blocked notRuntime notStuck))
    | .refuted notTerminal, .supported disputed, .refuted notReady,
        .supported blocked, .refuted notRuntime, .refuted notStuck =>
        .classified
          (.open notTerminal (.disputed disputed)
            (.blocked notReady blocked notRuntime notStuck))
    | .refuted notTerminal, .refuted notDisputed, .refuted notReady,
        .refuted notBlocked, .supported runtime, .refuted notStuck =>
        .classified
          (.open notTerminal (.ordinary notDisputed)
            (.runtime notReady notBlocked runtime notStuck))
    | .refuted notTerminal, .supported disputed, .refuted notReady,
        .refuted notBlocked, .supported runtime, .refuted notStuck =>
        .classified
          (.open notTerminal (.disputed disputed)
            (.runtime notReady notBlocked runtime notStuck))
    | .refuted notTerminal, .refuted notDisputed, .refuted notReady,
        .refuted notBlocked, .refuted notRuntime, .supported stuck =>
        .classified
          (.open notTerminal (.ordinary notDisputed)
            (.stuck notReady notBlocked notRuntime stuck))
    | .refuted notTerminal, .supported disputed, .refuted notReady,
        .refuted notBlocked, .refuted notRuntime, .supported stuck =>
        .classified
          (.open notTerminal (.disputed disputed)
            (.stuck notReady notBlocked notRuntime stuck))
    | _, _, _, _, _, _ =>
        .refuse .inconsistentEvidence

/--
The erased orthogonal state is uniquely determined by one complete evidence
packet. Instances supply facts, not a competing status decision.
-/
theorem derived_goal_disposition_unique_tag
    {Terminal Disputed Ready Blocked Runtime Stuck : Prop}
    (facts : WorkflowFacts Terminal Disputed Ready Blocked Runtime Stuck)
    (left right :
      CertifiedGoalDisposition
        Terminal Disputed Ready Blocked Runtime Stuck)
    (leftDerived : deriveGoalDisposition facts = .classified left)
    (rightDerived : deriveGoalDisposition facts = .classified right) :
    left.tag = right.tag := by
  have sameResult :
      GoalDispositionResult.classified left =
        GoalDispositionResult.classified right :=
    leftDerived.symm.trans rightDerived
  have sameDisposition : left = right :=
    GoalDispositionResult.classified.inj sameResult
  exact congrArg CertifiedGoalDisposition.tag sameDisposition

/-! ## 2. State-indexed workflow and migration universes -/

structure ClosureStateSystem where
  State : Type u
  Goal : Type v
  WorkItem : Type w
  Migration : Type w
  goalDecidableEq : DecidableEq Goal
  migrationDecidableEq : DecidableEq Migration

  liveGoalAt : State → Goal → Prop
  goalsAt : State → List Goal
  MandatoryGoalAt : State → Goal → Prop
  GoalSatisfiedAt : State → Goal → Prop
  targetGoal : WorkItem → Goal
  InvalidWorkItemAt : State → WorkItem → Prop
  TerminalAt : State → Goal → Prop
  mandatoryTerminalSound :
    ∀ state goal,
      MandatoryGoalAt state goal →
        TerminalAt state goal →
          GoalSatisfiedAt state goal
  DisputedAt : State → Goal → Prop
  ReadyAt : State → Goal → Prop
  BlockedAt : State → Goal → Prop
  RuntimeAt : State → Goal → Prop
  StuckAt : State → Goal → Prop
  workflowFactsAt :
    (state : State) → (goal : Goal) →
      WorkflowFacts
        (TerminalAt state goal)
        (DisputedAt state goal)
        (ReadyAt state goal)
        (BlockedAt state goal)
        (RuntimeAt state goal)
        (StuckAt state goal)

  migrationInScopeAt : State → Migration → Prop
  migrationsAt : State → List Migration
  PendingMigrationAt : State → Migration → Prop
  migrationEvidenceAt :
    (state : State) → (migration : Migration) →
      EvidenceState (PendingMigrationAt state migration)

structure GoalUniverseSeal
    (K : ClosureStateSystem) (state : K.State) : Prop where
  liveExists : ∃ goal, K.liveGoalAt state goal
  sound :
    ∀ goal, goal ∈ K.goalsAt state → K.liveGoalAt state goal
  complete :
    ∀ goal, K.liveGoalAt state goal → goal ∈ K.goalsAt state

structure ExhaustiveWorkflowWindow
    (K : ClosureStateSystem) (state : K.State) where
  universeSeal : GoalUniverseSeal K state
  classified :
    ∀ goal, K.liveGoalAt state goal →
      ∃ disposition,
        deriveGoalDisposition (K.workflowFactsAt state goal) =
          .classified disposition

structure MigrationUniverseSeal
    (K : ClosureStateSystem) (state : K.State) : Prop where
  sound :
    ∀ migration,
      migration ∈ K.migrationsAt state →
        K.migrationInScopeAt state migration
  complete :
    ∀ migration,
      K.migrationInScopeAt state migration →
        migration ∈ K.migrationsAt state

def goalIsActive (K : ClosureStateSystem)
    (state : K.State) (goal : K.Goal) : Bool :=
  match deriveGoalDisposition (K.workflowFactsAt state goal) with
  | .classified disposition =>
      match disposition.tag with
      | .terminal => false
      | .open _ _ => true
  | .refuse _ => true

def goalIsReady (K : ClosureStateSystem)
    (state : K.State) (goal : K.Goal) : Bool :=
  match deriveGoalDisposition (K.workflowFactsAt state goal) with
  | .classified disposition =>
      match disposition.tag with
      | .open _ .ready => true
      | _ => false
  | .refuse _ => false

def deriveActiveGoals (K : ClosureStateSystem) (state : K.State) :
    List K.Goal :=
  (K.goalsAt state).filter (goalIsActive K state)

def deriveFrontierGoals (K : ClosureStateSystem) (state : K.State) :
    List K.Goal :=
  (K.goalsAt state).filter (goalIsReady K state)

def migrationIsPending (K : ClosureStateSystem)
    (state : K.State) (migration : K.Migration) : Bool :=
  match K.migrationEvidenceAt state migration with
  | .supported _ => true
  | .refuted _ => false
  | .unknown => true

def derivePendingMigrations (K : ClosureStateSystem) (state : K.State) :
    List K.Migration :=
  (K.migrationsAt state).filter (migrationIsPending K state)

/--
An invalid work item cannot discharge its mandatory target.  Work-item
invalidity is deliberately absent from the premises: only the goal's own
terminal evidence, checked by `mandatoryTerminalSound`, can establish the
semantic goal claim.
-/
theorem invalid_work_item_does_not_close_mandatory_goal
    (K : ClosureStateSystem)
    (state : K.State)
    (work : K.WorkItem)
    (mandatory : K.MandatoryGoalAt state (K.targetGoal work))
    (_invalid : K.InvalidWorkItemAt state work)
    (unsatisfied : ¬ K.GoalSatisfiedAt state (K.targetGoal work)) :
    ¬ K.TerminalAt state (K.targetGoal work) := by
  intro terminal
  exact
    unsatisfied
      (K.mandatoryTerminalSound
        state (K.targetGoal work) mandatory terminal)

/-! ## 3. ME-1 classification plus terminal disposition -/

inductive FailureTerminalKind
  | resolved
  | boundary
  | invalid
  deriving DecidableEq, Repr

/--
One named terminal receipt bound to the exact failure, ME-1 class, admitted
context, and mandatory coverage slot.  This proposition is fixed by the
kernel; instances cannot replace it with `TerminalDispositionAt := True`.
-/
structure TerminalReceiptBinding
    (M : MetaFailureSemantics.{v, w, x})
    (context : FailureContext M.Snapshot M.FailureModel)
    (failure : M.Failure)
    (tag : FailureClassTag)
    (Receipt : Type u)
    (receiptAt : M.Failure → Option Receipt)
    (receiptName : Receipt → String)
    (receiptContext :
      Receipt → FailureContext M.Snapshot M.FailureModel)
    (receiptFailure : Receipt → M.Failure)
    (receiptClass : Receipt → FailureClassTag)
    (receiptKind : Receipt → FailureTerminalKind)
    (ResolvedAt BoundaryAt InvalidAt : Receipt → Prop) :
    Type (max u v w x) where
  receipt : Receipt
  found : receiptAt failure = some receipt
  nameNonempty : receiptName receipt ≠ ""
  contextBound : receiptContext receipt = context
  failureBound : receiptFailure receipt = failure
  classBound : receiptClass receipt = tag
  mandatory : (M.coverage.modelAt context).mandatory failure
  admitted : M.AdmittedAt context failure
  selectedClass : M.ClassHolds context failure tag
  terminalKind : FailureTerminalKind
  kindBound : receiptKind receipt = terminalKind
  terminalEvidence :
    match receiptKind receipt with
    | .resolved => ResolvedAt receipt
    | .boundary => BoundaryAt receipt
    | .invalid => InvalidAt receipt

theorem TerminalReceiptBinding.resolvedEvidence
    {M : MetaFailureSemantics.{v, w, x}}
    {context : FailureContext M.Snapshot M.FailureModel}
    {failure : M.Failure}
    {tag : FailureClassTag}
    {Receipt : Type u}
    {receiptAt : M.Failure → Option Receipt}
    {receiptName : Receipt → String}
    {receiptContext :
      Receipt → FailureContext M.Snapshot M.FailureModel}
    {receiptFailure : Receipt → M.Failure}
    {receiptClass : Receipt → FailureClassTag}
    {receiptKind : Receipt → FailureTerminalKind}
    {ResolvedAt BoundaryAt InvalidAt : Receipt → Prop}
    (binding :
      TerminalReceiptBinding M context failure tag Receipt receiptAt
        receiptName receiptContext receiptFailure receiptClass receiptKind
        ResolvedAt BoundaryAt InvalidAt)
    (resolved : binding.terminalKind = .resolved) :
    ResolvedAt binding.receipt := by
  simpa [binding.kindBound, resolved] using binding.terminalEvidence

theorem TerminalReceiptBinding.boundaryEvidence
    {M : MetaFailureSemantics.{v, w, x}}
    {context : FailureContext M.Snapshot M.FailureModel}
    {failure : M.Failure}
    {tag : FailureClassTag}
    {Receipt : Type u}
    {receiptAt : M.Failure → Option Receipt}
    {receiptName : Receipt → String}
    {receiptContext :
      Receipt → FailureContext M.Snapshot M.FailureModel}
    {receiptFailure : Receipt → M.Failure}
    {receiptClass : Receipt → FailureClassTag}
    {receiptKind : Receipt → FailureTerminalKind}
    {ResolvedAt BoundaryAt InvalidAt : Receipt → Prop}
    (binding :
      TerminalReceiptBinding M context failure tag Receipt receiptAt
        receiptName receiptContext receiptFailure receiptClass receiptKind
        ResolvedAt BoundaryAt InvalidAt)
    (boundary : binding.terminalKind = .boundary) :
    BoundaryAt binding.receipt := by
  simpa [binding.kindBound, boundary] using binding.terminalEvidence

theorem TerminalReceiptBinding.invalidEvidence
    {M : MetaFailureSemantics.{v, w, x}}
    {context : FailureContext M.Snapshot M.FailureModel}
    {failure : M.Failure}
    {tag : FailureClassTag}
    {Receipt : Type u}
    {receiptAt : M.Failure → Option Receipt}
    {receiptName : Receipt → String}
    {receiptContext :
      Receipt → FailureContext M.Snapshot M.FailureModel}
    {receiptFailure : Receipt → M.Failure}
    {receiptClass : Receipt → FailureClassTag}
    {receiptKind : Receipt → FailureTerminalKind}
    {ResolvedAt BoundaryAt InvalidAt : Receipt → Prop}
    (binding :
      TerminalReceiptBinding M context failure tag Receipt receiptAt
        receiptName receiptContext receiptFailure receiptClass receiptKind
        ResolvedAt BoundaryAt InvalidAt)
    (invalid : binding.terminalKind = .invalid) :
    InvalidAt binding.receipt := by
  simpa [binding.kindBound, invalid] using binding.terminalEvidence

structure FailureTerminalSystem
    (State : Type u)
    (M : MetaFailureSemantics.{v, w, x}) where
  Receipt : Type u
  contextAt :
    State → FailureContext M.Snapshot M.FailureModel
  mandatoryFailuresAt : State → List M.Failure
  receiptAt : State → M.Failure → Option Receipt
  receiptName : Receipt → String
  receiptContext :
    Receipt → FailureContext M.Snapshot M.FailureModel
  receiptFailure : Receipt → M.Failure
  receiptClass : Receipt → FailureClassTag
  receiptKind : Receipt → FailureTerminalKind
  ResolvedAt : State → M.Failure → Receipt → Prop
  BoundaryAt : State → M.Failure → Receipt → Prop
  InvalidAt : State → M.Failure → Receipt → Prop
  terminalCertificateAt :
    (state : State) → (failure : M.Failure) → (tag : FailureClassTag) →
      Option
        (TerminalReceiptBinding M (contextAt state) failure tag Receipt
          (receiptAt state) receiptName receiptContext receiptFailure
          receiptClass receiptKind
          (ResolvedAt state failure)
          (BoundaryAt state failure)
          (InvalidAt state failure))

structure MandatoryFailureUniverseSeal
    {State : Type u}
    {M : MetaFailureSemantics.{v, w, x}}
    (F : FailureTerminalSystem State M)
    (state : State) : Prop where
  sound :
    ∀ failure,
      failure ∈ F.mandatoryFailuresAt state →
        (M.coverage.modelAt (F.contextAt state)).mandatory failure
  complete :
    ∀ failure,
      (M.coverage.modelAt (F.contextAt state)).mandatory failure →
        failure ∈ F.mandatoryFailuresAt state

def failureIsActive
    {State : Type u}
    {M : MetaFailureSemantics.{v, w, x}}
    (F : FailureTerminalSystem State M)
    (state : State)
    (window : ExhaustiveFailureWindow M (F.contextAt state))
    (failure : M.Failure) : Bool :=
  match window.admitted.factsAt failure with
  | none => true
  | some facts =>
      match deriveFailureClass facts with
      | .refuse _ => true
      | .classified classification =>
          match
              F.terminalCertificateAt
                state failure classification.tag with
          | none => true
          | some _certificate => false

def deriveActiveFailures
    {State : Type u}
    {M : MetaFailureSemantics.{v, w, x}}
    (F : FailureTerminalSystem State M)
    (state : State)
    (window : ExhaustiveFailureWindow M (F.contextAt state)) :
    List M.Failure :=
  (F.mandatoryFailuresAt state).filter
    (failureIsActive F state window)

/-! ## 4. Exact closure-exhaustion packet -/

structure ClosureExhaustionAt
    (K : ClosureStateSystem)
    (M : MetaFailureSemantics.{u, v, w})
    (F : FailureTerminalSystem K.State M)
    (state : K.State) where
  workflowWindow : ExhaustiveWorkflowWindow K state
  migrationSeal : MigrationUniverseSeal K state
  failureWindow : ExhaustiveFailureWindow M (F.contextAt state)
  mandatoryFailureSeal : MandatoryFailureUniverseSeal F state
  activeGoalsEmpty : deriveActiveGoals K state = []
  activeFailuresEmpty :
    deriveActiveFailures F state failureWindow = []
  pendingMigrationsEmpty : derivePendingMigrations K state = []

/-- Closure exhaustion is strictly stronger than an empty ready frontier. -/
theorem ClosureExhaustionAt.frontierEmpty
    {K : ClosureStateSystem}
    {M : MetaFailureSemantics.{u, v, w}}
    {F : FailureTerminalSystem K.State M}
    {state : K.State}
    (closed : ClosureExhaustionAt K M F state) :
    deriveFrontierGoals K state = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro goal readyMember
  have activeMember : goal ∈ deriveActiveGoals K state := by
    simp only [deriveFrontierGoals, List.mem_filter] at readyMember
    rcases readyMember with ⟨declared, ready⟩
    simp only [deriveActiveGoals, List.mem_filter]
    refine ⟨declared, ?_⟩
    unfold goalIsReady at ready
    unfold goalIsActive
    split at ready <;> rename_i derived
    · split at ready <;> simp_all
    · simp at ready
  rw [closed.activeGoalsEmpty] at activeMember
  exact nomatch activeMember

/--
Every mandatory ME-1 failure in a closure-exhaustion packet has an accepted
named terminal receipt bound to the exact context, failure, derived class,
mandatory coverage slot, and admitted evidence.  Classification alone is
insufficient: missing facts, refused classification, or a missing bound receipt
all remain in `deriveActiveFailures`.
-/
theorem ClosureExhaustionAt.mandatoryFailureTerminal
    {K : ClosureStateSystem}
    {M : MetaFailureSemantics.{u, v, w}}
    {F : FailureTerminalSystem K.State M}
    {state : K.State}
    (closed : ClosureExhaustionAt K M F state)
    (failure : M.Failure)
    (mandatory :
      (M.coverage.modelAt (F.contextAt state)).mandatory failure) :
    ∃ facts classification certificate,
      closed.failureWindow.admitted.factsAt failure = some facts ∧
      deriveFailureClass facts = .classified classification ∧
      F.terminalCertificateAt
          state failure classification.tag = some certificate ∧
      F.receiptName certificate.receipt ≠ "" ∧
      F.receiptContext certificate.receipt = F.contextAt state ∧
      F.receiptFailure certificate.receipt = failure ∧
      F.receiptClass certificate.receipt = classification.tag ∧
      F.receiptKind certificate.receipt = certificate.terminalKind := by
  have declared :
      failure ∈ F.mandatoryFailuresAt state :=
    closed.mandatoryFailureSeal.complete failure mandatory
  have inactive :
      failureIsActive F state closed.failureWindow failure = false := by
    cases active :
        failureIsActive F state closed.failureWindow failure with
    | false => rfl
    | true =>
        have activeMember :
            failure ∈
              deriveActiveFailures F state closed.failureWindow := by
          simp only [deriveActiveFailures, List.mem_filter]
          exact ⟨declared, active⟩
        rw [closed.activeFailuresEmpty] at activeMember
        exact nomatch activeMember
  have inScope :
      (M.coverage.modelAt (F.contextAt state)).inScope failure :=
    (M.coverage.modelAt (F.contextAt state)).mandatoryInScope
      failure mandatory
  rcases closed.failureWindow.packetClassified failure inScope with
    ⟨facts, classification, factsFound, classified⟩
  cases certificateFound :
      F.terminalCertificateAt state failure classification.tag with
  | none =>
      unfold failureIsActive at inactive
      simp only [factsFound, classified, certificateFound] at inactive
      exact Bool.noConfusion inactive
  | some certificate =>
      exact
        ⟨facts, classification, certificate,
          factsFound, classified, certificateFound,
          certificate.nameNonempty,
          certificate.contextBound,
          certificate.failureBound,
          certificate.classBound,
          certificate.kindBound⟩

end Residua.RCC.ClosureExhaustion

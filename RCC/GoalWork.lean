/-!
# RCC Goal / Work-Item Separation Kernel

A `WorkItem` is one route toward a semantic `Goal`. Work-item disposition may update
only the work ledger. Goal presence and semantic status are changed only by separate,
certificate-bearing goal operations outside this slice.

Prelude-only Lean 4.14; no Mathlib, no `sorry`, no custom axioms (some theorems use the standard `propext` and `Quot.sound`).
-/

namespace Residua.RCC

universe u v

/-- Semantic state of a Goal. Work-item operations cannot construct these transitions. -/
inductive GoalStatus where
  | open
  | satisfied
  | waived
  deriving DecidableEq

/-- Operational state of one route toward a Goal. -/
inductive WorkStatus where
  | active
  | invalid
  | rejected
  | superseded
  deriving DecidableEq

/-- The only work-ledger actions in the RCC-13 slice. -/
inductive WorkAction where
  | invalidate
  | reject
  | supersede
  deriving DecidableEq

/-- Named reasons why a proposed work-only transition is not admissible. -/
inductive GoalWorkTransitionResidue where
  | goalPresenceChanged
  | goalStatusChanged
  | workDispositionMismatch
  deriving DecidableEq

/-- Mechanical verdict for one proposed work-only transition. -/
inductive GoalWorkTransitionAssessment where
  | admitted
  | refuse (residue : GoalWorkTransitionResidue)
  deriving DecidableEq

/-- Goal and WorkItem are distinct carriers connected only by an explicit target map. -/
structure GoalWorkSystem where
  Goal : Type u
  WorkItem : Type v
  workDecidableEq : DecidableEq WorkItem
  target : WorkItem → Goal

/-- One snapshot keeps semantic Goal state orthogonal to operational WorkItem state. -/
structure GoalWorkSnapshot (S : GoalWorkSystem) where
  goalPresent : S.Goal → Bool
  goalStatus : S.Goal → GoalStatus
  workStatus : S.WorkItem → WorkStatus

/-- Canonical terminal WorkItem disposition for each work action. -/
def WorkAction.status : WorkAction → WorkStatus
  | .invalidate => .invalid
  | .reject => .rejected
  | .supersede => .superseded

/--
Apply one WorkItem action. The definition updates only `workStatus`; both Goal fields are
copied definitionally from the pre-state.
-/
def applyWorkAction (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction) :
    GoalWorkSnapshot S :=
  letI : DecidableEq S.WorkItem := S.workDecidableEq
  {
    goalPresent := snapshot.goalPresent
    goalStatus := snapshot.goalStatus
    workStatus := fun candidate =>
      if candidate = work then action.status else snapshot.workStatus candidate
  }

/--
Check the three load-bearing laws of a work-only transition at the acted-on target:
Goal presence and semantic status are preserved, while the WorkItem receives exactly
the requested disposition.
-/
def assessWorkTransition (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction)
    (post : GoalWorkSnapshot S) : GoalWorkTransitionAssessment :=
  if _hPresence : post.goalPresent (S.target work) =
      snapshot.goalPresent (S.target work) then
    if _hStatus : post.goalStatus (S.target work) =
        snapshot.goalStatus (S.target work) then
      if _hWork : post.workStatus work = action.status then
        .admitted
      else
        .refuse .workDispositionMismatch
    else
      .refuse .goalStatusChanged
  else
    .refuse .goalPresenceChanged

/--
Countermodel implementation: it performs the requested WorkItem disposition but also
erases the target Goal's presence bit. The result depends on the actual target and
pre-state; it is not a constant refusal fixture.
-/
def applyErasingTargetMutant (S : GoalWorkSystem) [DecidableEq S.Goal]
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction) :
    GoalWorkSnapshot S :=
  let applied := applyWorkAction S snapshot work action
  {
    goalPresent := fun goal =>
      if goal = S.target work then false else applied.goalPresent goal
    goalStatus := applied.goalStatus
    workStatus := applied.workStatus
  }

/-- Work-item disposition preserves every Goal-presence bit, not only the target Goal. -/
theorem work_action_preserves_goal_presence (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction)
    (goal : S.Goal) :
    (applyWorkAction S snapshot work action).goalPresent goal = snapshot.goalPresent goal := by
  rfl

/-- Work-item disposition preserves every semantic Goal status. -/
theorem work_action_preserves_goal_status (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction)
    (goal : S.Goal) :
    (applyWorkAction S snapshot work action).goalStatus goal = snapshot.goalStatus goal := by
  rfl

/--
RCC-13 target theorem: if the target Goal was present and open, any work-only action
leaves it present and open.
-/
theorem target_goal_remains_open_after_work_action
    (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction)
    (hpresent : snapshot.goalPresent (S.target work) = true)
    (hopen : snapshot.goalStatus (S.target work) = .open) :
    (applyWorkAction S snapshot work action).goalPresent (S.target work) = true ∧
      (applyWorkAction S snapshot work action).goalStatus (S.target work) = .open := by
  exact ⟨hpresent, hopen⟩

/-- The acted-on WorkItem receives exactly the requested disposition. -/
theorem acted_work_receives_status (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction) :
    (applyWorkAction S snapshot work action).workStatus work = action.status := by
  letI : DecidableEq S.WorkItem := S.workDecidableEq
  simp [applyWorkAction]

/-- Every other WorkItem retains its prior operational status. -/
theorem other_work_status_preserved (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work other : S.WorkItem) (action : WorkAction)
    (hne : other ≠ work) :
    (applyWorkAction S snapshot work action).workStatus other = snapshot.workStatus other := by
  letI : DecidableEq S.WorkItem := S.workDecidableEq
  simp [applyWorkAction, hne]

/-- The assessor admits the real work-only implementation. -/
theorem applied_work_transition_is_admitted (S : GoalWorkSystem)
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction) :
    assessWorkTransition S snapshot work action
        (applyWorkAction S snapshot work action) = .admitted := by
  simp [assessWorkTransition, work_action_preserves_goal_presence,
    work_action_preserves_goal_status, acted_work_receives_status]

/-- The mutant remains a near miss: it still performs the requested work disposition. -/
theorem erasing_target_mutant_applies_work_disposition
    (S : GoalWorkSystem) [DecidableEq S.Goal]
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction) :
    (applyErasingTargetMutant S snapshot work action).workStatus work = action.status := by
  simp [applyErasingTargetMutant, acted_work_receives_status]

/--
If the target Goal is present, the assessor rejects the near-miss mutant for the exact
semantic breach: it erased Goal presence while disposing only a WorkItem.
-/
theorem erasing_target_mutant_is_refused
    (S : GoalWorkSystem) [DecidableEq S.Goal]
    (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction)
    (hpresent : snapshot.goalPresent (S.target work) = true) :
    assessWorkTransition S snapshot work action
        (applyErasingTargetMutant S snapshot work action) =
      .refuse .goalPresenceChanged := by
  simp [assessWorkTransition, applyErasingTargetMutant, hpresent]

end Residua.RCC

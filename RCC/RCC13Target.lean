import RCC.GoalWork

/-! RCC-13 candidate: work-item terminality cannot erase a semantic goal. -/

namespace Residua.RCC.RCC13Target

open Residua.RCC

structure Certificate where
  goalPresencePreserved :
    ∀ (S : GoalWorkSystem.{0,0}) (snapshot : GoalWorkSnapshot S)
      (work : S.WorkItem) (action : WorkAction) (goal : S.Goal),
      (applyWorkAction S snapshot work action).goalPresent goal =
        snapshot.goalPresent goal
  goalStatusPreserved :
    ∀ (S : GoalWorkSystem.{0,0}) (snapshot : GoalWorkSnapshot S)
      (work : S.WorkItem) (action : WorkAction) (goal : S.Goal),
      (applyWorkAction S snapshot work action).goalStatus goal =
        snapshot.goalStatus goal
  targetGoalRemainsOpen :
    ∀ (S : GoalWorkSystem.{0,0}) (snapshot : GoalWorkSnapshot S)
      (work : S.WorkItem) (action : WorkAction),
      snapshot.goalPresent (S.target work) = true →
      snapshot.goalStatus (S.target work) = .open →
      (applyWorkAction S snapshot work action).goalPresent (S.target work) = true ∧
        (applyWorkAction S snapshot work action).goalStatus (S.target work) = .open
  actedWorkGetsDisposition :
    ∀ (S : GoalWorkSystem.{0,0}) (snapshot : GoalWorkSnapshot S)
      (work : S.WorkItem) (action : WorkAction),
      (applyWorkAction S snapshot work action).workStatus work = action.status
  appliedTransitionAdmitted :
    ∀ (S : GoalWorkSystem.{0,0}) (snapshot : GoalWorkSnapshot S)
      (work : S.WorkItem) (action : WorkAction),
      assessWorkTransition S snapshot work action
          (applyWorkAction S snapshot work action) = .admitted
  mutantStillAppliesDisposition :
    ∀ (S : GoalWorkSystem.{0,0}) [DecidableEq S.Goal]
      (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction),
      (applyErasingTargetMutant S snapshot work action).workStatus work = action.status
  mutantGoalPresenceRefused :
    ∀ (S : GoalWorkSystem.{0,0}) [DecidableEq S.Goal]
      (snapshot : GoalWorkSnapshot S) (work : S.WorkItem) (action : WorkAction),
      snapshot.goalPresent (S.target work) = true →
      assessWorkTransition S snapshot work action
          (applyErasingTargetMutant S snapshot work action) =
        .refuse .goalPresenceChanged

def certificate : Certificate where
  goalPresencePreserved := work_action_preserves_goal_presence
  goalStatusPreserved := work_action_preserves_goal_status
  targetGoalRemainsOpen := target_goal_remains_open_after_work_action
  actedWorkGetsDisposition := acted_work_receives_status
  appliedTransitionAdmitted := applied_work_transition_is_admitted
  mutantStillAppliesDisposition := erasing_target_mutant_applies_work_disposition
  mutantGoalPresenceRefused := erasing_target_mutant_is_refused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC13Target

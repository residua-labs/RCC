import RCC.GoalWork
import RCCTests.RC1StepMSTBinding

/-! RCC-R1 candidate: goals, work items, step candidates, judgments, and events
    remain distinct and only a bound settled representative mutates history. -/

namespace Residua.RCC.R1Target

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RC1StepMSTBinding.Tests

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
  existingAdvanceHasSettledEvent :
    ∀ {State : Type} {C : ClosureContext State}
      {before after : State},
      AdvancePacket C before after →
      HistoryEdge (demoSurface C) before after
  nonadmittedAdvanceCannotBind :
    ∀ {State : Type} {C : ClosureContext State}
      {surface : StepSurface C} {before after : State}
      {packet : AdvancePacket C before after},
      surface.admitted (surface.classOf packet) = false →
      ¬ Nonempty (BoundAdvance surface packet)
  emptyEventCannotAppend :
    ∀ {State : Type} {C : ClosureContext State} {before after : State},
      ¬ HistoryEdge (emptyEventSurface C) before after

def certificate : Certificate where
  goalPresencePreserved := work_action_preserves_goal_presence
  goalStatusPreserved := work_action_preserves_goal_status
  targetGoalRemainsOpen := target_goal_remains_open_after_work_action
  actedWorkGetsDisposition := acted_work_receives_status
  existingAdvanceHasSettledEvent := existing_advance_resolves_to_history_edge
  nonadmittedAdvanceCannotBind := nonadmitted_advance_cannot_resolve_to_history
  emptyEventCannotAppend := empty_event_mutant_cannot_append_history

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.R1Target

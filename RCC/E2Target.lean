import RCC.ClosureExhaustion

/-! E2 candidate: negative closure claims consume sealed universes and typed
    evidence; the derived disposition is orthogonal and no invalid work item
    can discharge its mandatory Goal. -/

namespace Residua.RCC.E2Target

open Residua.RCC.ClosureExhaustion
open Residua.RCC.MetaFailureExhaustion

structure Certificate where
  dispositionUnique :
    ∀ {Terminal Disputed Ready Blocked Runtime Stuck : Prop}
      (facts : WorkflowFacts Terminal Disputed Ready Blocked Runtime Stuck)
      (left right : CertifiedGoalDisposition
        Terminal Disputed Ready Blocked Runtime Stuck),
      deriveGoalDisposition facts = .classified left →
      deriveGoalDisposition facts = .classified right →
      left.tag = right.tag
  invalidWorkDoesNotClose :
    ∀ (K : ClosureStateSystem.{0, 0, 0}) (state : K.State) (work : K.WorkItem)
      (mandatory : K.MandatoryGoalAt state (K.targetGoal work))
      (invalid : K.InvalidWorkItemAt state work)
      (unsatisfied : ¬ K.GoalSatisfiedAt state (K.targetGoal work)),
      ¬ K.TerminalAt state (K.targetGoal work)
  frontierProjection :
    ∀ {K : ClosureStateSystem.{0, 0, 0}}
      {M : MetaFailureSemantics.{0, 0, 0, 0}}
      {F : FailureTerminalSystem K.State M} {state : K.State},
      ClosureExhaustionAt K M F state →
      deriveFrontierGoals K state = []

def certificate : Certificate where
  dispositionUnique := derived_goal_disposition_unique_tag
  invalidWorkDoesNotClose := invalid_work_item_does_not_close_mandatory_goal
  frontierProjection := ClosureExhaustionAt.frontierEmpty

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.E2Target

import RCC.GoalRefinement
import RCC.Reepoch

/-!
# RCC-20 Goal-Refinement / Reepoch Bridge

`RefinementCert` and `GoalMigration` quantify over different histories: a
refinement certificate compares goals in one history, while a migration
compares the old goal at the parent epoch with the replacement at the
successor epoch.  The bridge therefore uses a tagged edge carrier, rather
than silently identifying those histories.  The reverse direction remains
intentionally absent: one edge does not establish a history-uniform law.

Prelude-only Lean 4.14; all proofs are kernel-checked.
-/

namespace Residua.RCC

universe u v w x y

/-- The Goal/Work carrier used to view a reepoch system through RCC-20. -/
inductive EdgeRole where
  | old
  | new
  deriving DecidableEq

def edgeGoalWorkSystem
    (S : ReepochSystem.{u, v, w, x, y}) : GoalWorkSystem where
  Goal := EdgeRole × S.Goal
  WorkItem := Empty
  workDecidableEq := inferInstance
  target := fun work => nomatch work

/-- Edge satisfaction tags old and successor goals with their respective epochs. -/
def edgeGoalSemantics
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch) :
    GoalSemantics (edgeGoalWorkSystem S) where
  History := S.Epoch
  satisfied := fun _ goal => match goal with
    | (.old, oldGoal) => S.goalSatisfied parent oldGoal
    | (.new, newGoal) => S.goalSatisfied successor newGoal

/-!
Specializing a history-uniform split certificate at the successor history
produces exactly the semantic implication required by a reepoch migration.
-/
theorem refinement_cert_implies_reepoch_refinement
    {S : ReepochSystem.{u, v, w, x, y}}
    {parentEpoch successorEpoch : S.Epoch}
    {oldGoal newGoal : S.Goal}
    (certificate :
      SplitRefinementCert
        (edgeGoalSemantics S parentEpoch successorEpoch)
        (.old, oldGoal) [(.new, newGoal)]) :
    SemanticallyRefines S parentEpoch successorEpoch oldGoal newGoal := by
  intro successorSatisfied
  have replacementsSatisfied :
      GoalsSatisfied (edgeGoalSemantics S parentEpoch successorEpoch)
        parentEpoch [(.new, newGoal)] := by
    intro goal hgoal
    have hgoalEq : goal = (.new, newGoal) := by simpa using hgoal
    subst goal
    exact successorSatisfied
  have originalsSatisfied :
      GoalsSatisfied (edgeGoalSemantics S parentEpoch successorEpoch)
        parentEpoch [(.old, oldGoal)] :=
    certificate.forwardSufficient parentEpoch replacementsSatisfied
  have oldSatisfied :
      (edgeGoalSemantics S parentEpoch successorEpoch).satisfied parentEpoch
        (.old, oldGoal) :=
    originalsSatisfied (.old, oldGoal) (by simp)
  exact oldSatisfied

/-!
The bridge is intentionally one-way.  An edge-local migration can be valid
without yielding a uniform refinement certificate over every history.
-/
theorem reepoch_refinement_is_edge_local
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    {oldGoal : S.Goal}
    (migration : GoalMigration S parent successor oldGoal) :
    SemanticallyRefines S parent successor oldGoal migration.newGoal := by
  change SemanticallyRefines S parent successor oldGoal migration.newGoal
  exact migration.semanticRefinement

end Residua.RCC


import RCC.GoalRefinementReepoch
import RCCTests.Reepoch

/-!
# RCC-20 Goal-Refinement / Reepoch Bridge Witnesses

The positive theorem specializes the existing all-history refinement certificate
to the concrete reepoch edge.  The negative control uses a successor-only
certificate and a counter-history to show why the reverse implication is not
lawful.
-/

open Residua.RCC

namespace Residua.RCC.GoalRefinementReepochTests

open Residua.RCC.ReepochTests

def bridgeSemantics :
    GoalSemantics (edgeGoalWorkSystem demoSystem) :=
  edgeGoalSemantics demoSystem .base .child

def bridgeCertificate :
    SplitRefinementCert bridgeSemantics (.old, .debt) [(.new, .replacement)] where
  originalsNonempty := by simp
  replacementsNonempty := by simp
  forwardSufficient := by
    intro history hchildren goal hgoal
    have hgoalEq : goal = (.old, .debt) := by simpa using hgoal
    subst goal
    have hchild := hchildren (.new, .replacement) (by simp)
    simp [bridgeSemantics, edgeGoalSemantics, demoSystem] at hchild ⊢

theorem bridge_specializes_uniform_refinement :
    SemanticallyRefines demoSystem DemoEpoch.base DemoEpoch.child
      DemoGoal.debt DemoGoal.replacement := by
  exact refinement_cert_implies_reepoch_refinement
    (S := demoSystem) (parentEpoch := DemoEpoch.base)
    (successorEpoch := DemoEpoch.child) bridgeCertificate

/-! A successor-only contract can be true while a different history refutes it. -/

inductive CounterEpoch
  | parent
  | successor
  | other
  deriving DecidableEq

inductive CounterGoal
  | old
  | replacement
  deriving DecidableEq

def counterSatisfied : CounterEpoch → CounterGoal → Prop
  | .parent, .old => True
  | .successor, .replacement => True
  | .other, .replacement => True
  | _, _ => False

def counterSystem : ReepochSystem where
  Epoch := CounterEpoch
  Goal := CounterGoal
  Occurrence := Unit
  SemanticValue := Nat
  GoalOrigin := Unit
  semanticValue := fun _ _ => 0
  parentEpoch := fun | .successor => some .parent | _ => none
  goalOrigin := fun _ => ()
  goalSatisfied := counterSatisfied
  nonterminal := fun _ _ => False
  terminalAtMigration := fun _ _ => False
  triggerOccurrence := fun _ => none
  migrationForOccurrence := fun _ => none
  newObservationAdmitted := fun _ _ => False
  policyDecisionAdmitted := fun _ _ => False
  kernelReplacementAdmitted := fun _ _ => False
  stableObstructionAdmitted := fun _ _ => False
  epochMeasure := fun _ => 0

def edgeOnlyMigration :
    GoalMigration counterSystem .parent .successor .old where
  newGoal := .replacement
  originBound := rfl
  semanticRefinement := by
    intro hsuccessor
    exact hsuccessor

def counterUniformSemantics : GoalSemantics (edgeGoalWorkSystem counterSystem) where
  History := CounterEpoch
  satisfied := fun history goal => match goal with
    | (.old, oldGoal) => counterSatisfied history oldGoal
    | (.new, newGoal) => counterSatisfied history newGoal

theorem edge_only_does_not_imply_uniform_refinement :
    ¬ SplitRefinementCert
      counterUniformSemantics
      (.old, .old) [(.new, .replacement)] := by
  intro certificate
  have replacementAtOther :
      GoalsSatisfied counterUniformSemantics
        .other [(.new, .replacement)] := by
    intro goal hgoal
    have : goal = (.new, .replacement) := by simpa using hgoal
    subst goal
    exact by simp [counterUniformSemantics, counterSatisfied]
  have oldAtOther := certificate.forwardSufficient .other replacementAtOther
  have oldMember := oldAtOther (.old, .old) (by simp)
  simp [counterUniformSemantics, counterSatisfied] at oldMember

theorem edge_only_migration_is_not_a_refinement_certificate :
    SemanticallyRefines counterSystem .parent .successor .old .replacement :=
  reepoch_refinement_is_edge_local edgeOnlyMigration

end Residua.RCC.GoalRefinementReepochTests


import RCC.GoalRefinement

/-!
# RCC-20 Goal Refinement Witnesses

RED-first tests for semantic goal refinement. A split is admissible only when satisfying
every child implies the retained parent, and a merge is admissible only when satisfying
the replacement implies every old goal.
-/

open Residua.RCC

namespace Residua.RCC.GoalRefinementTests

/-- Four independent facts that a concrete history may or may not establish. -/
structure DemoHistory where
  proofSound : Bool
  runtimeBound : Bool
  readmeExists : Bool
  ciRuns : Bool
  deriving DecidableEq

/-- The hard parent, its two real components, and two operationally irrelevant goals. -/
inductive DemoGoal
  | hardParent
  | proofSound
  | runtimeBound
  | readmeExists
  | ciRuns
  deriving DecidableEq

/-- Minimal Goal/Work separation substrate required by the frozen RCC-20 surface. -/
def demoSystem : GoalWorkSystem where
  Goal := DemoGoal
  WorkItem := Unit
  workDecidableEq := inferInstance
  target := fun _ => .hardParent

/-- The parent means the conjunction, rather than merely naming a work item. -/
def demoSatisfied (history : DemoHistory) : DemoGoal → Prop
  | .hardParent => history.proofSound = true ∧ history.runtimeBound = true
  | .proofSound => history.proofSound = true
  | .runtimeBound => history.runtimeBound = true
  | .readmeExists => history.readmeExists = true
  | .ciRuns => history.ciRuns = true

def demoSemantics : GoalSemantics demoSystem where
  History := DemoHistory
  satisfied := demoSatisfied

/-- The lawful split exposes exactly the two conjuncts of the hard parent. -/
def legalChildren : List DemoGoal :=
  [.proofSound, .runtimeBound]

/-- CM-GOAL-02: easy but unrelated children cannot replace the hard parent meaning. -/
def irrelevantChildren : List DemoGoal :=
  [.readmeExists, .ciRuns]

/-- Both real children together establish the retained parent. -/
theorem legal_children_imply_hard_parent (history : DemoHistory)
    (hchildren : GoalsSatisfied demoSemantics history legalChildren) :
    demoSemantics.satisfied history .hardParent := by
  exact ⟨
    hchildren .proofSound (List.Mem.head _),
    hchildren .runtimeBound (List.Mem.tail _ (List.Mem.head _))
  ⟩

/-- Positive control: the intended split can carry a semantic certificate. -/
def legalSplitCertificate :
    SplitRefinementCert demoSemantics .hardParent legalChildren where
  originalsNonempty := by simp
  replacementsNonempty := by simp [legalChildren]
  forwardSufficient := by
    intro history hchildren goal hgoal
    simp at hgoal
    subst goal
    exact legal_children_imply_hard_parent history hchildren

/-- Countermodel history: the easy children are true while both hard obligations fail. -/
def irrelevantHistory : DemoHistory where
  proofSound := false
  runtimeBound := false
  readmeExists := true
  ciRuns := true

theorem irrelevant_history_satisfies_irrelevant_children :
    GoalsSatisfied demoSemantics irrelevantHistory irrelevantChildren := by
  intro goal hgoal
  cases hgoal with
  | head =>
      rfl
  | tail _ htail =>
      cases htail with
      | head =>
          rfl
      | tail _ hnil =>
          cases hnil

theorem irrelevant_history_refutes_hard_parent :
    ¬ demoSemantics.satisfied irrelevantHistory .hardParent := by
  simp [demoSemantics, demoSatisfied, irrelevantHistory]

/--
Split mutant refusal: no certificate can claim that README/CI success preserves the
meaning of proof soundness plus a runtime bound.
-/
theorem irrelevant_children_have_no_split_certificate :
    ¬ SplitRefinementCert demoSemantics .hardParent irrelevantChildren := by
  intro certificate
  have horiginals := certificate.forwardSufficient
    irrelevantHistory irrelevant_history_satisfies_irrelevant_children
  exact irrelevant_history_refutes_hard_parent
    (horiginals .hardParent (by simp))

/-- The merge starts with the two obligations that formerly appeared as split children. -/
def oldGoals : List DemoGoal :=
  [.proofSound, .runtimeBound]

/-- Requiring the conjunction is strong enough to discharge both old goals. -/
theorem hard_parent_implies_old_goals (history : DemoHistory)
    (hparent : demoSemantics.satisfied history .hardParent) :
    GoalsSatisfied demoSemantics history oldGoals := by
  intro goal hgoal
  cases hgoal with
  | head =>
      exact hparent.1
  | tail _ htail =>
      cases htail with
      | head =>
          exact hparent.2
      | tail _ hnil =>
          cases hnil

/-- Positive control: the hard parent is a lawful replacement for the two old goals. -/
def hardParentMergeCertificate :
    MergeRefinementCert demoSemantics oldGoals .hardParent where
  originalsNonempty := by simp [oldGoals]
  replacementsNonempty := by simp
  forwardSufficient := by
    intro history hreplacement
    exact hard_parent_implies_old_goals history
      (hreplacement .hardParent (by simp))

/-- The weak merge mutant keeps only proof soundness and drops the runtime obligation. -/
def weakMergeHistory : DemoHistory where
  proofSound := true
  runtimeBound := false
  readmeExists := false
  ciRuns := false

theorem weak_merge_history_satisfies_replacement :
    demoSemantics.satisfied weakMergeHistory .proofSound := by
  rfl

theorem weak_merge_history_satisfies_replacement_goals :
    GoalsSatisfied demoSemantics weakMergeHistory [.proofSound] := by
  intro goal hgoal
  simp at hgoal
  subst goal
  exact weak_merge_history_satisfies_replacement

theorem weak_merge_history_refutes_old_goals :
    ¬ GoalsSatisfied demoSemantics weakMergeHistory oldGoals := by
  intro hold
  have hruntime := hold .runtimeBound (List.Mem.tail _ (List.Mem.head _))
  simp [demoSemantics, demoSatisfied, weakMergeHistory] at hruntime

/--
Merge mutant refusal: a replacement proving only one former goal cannot discharge both.
-/
theorem weak_replacement_has_no_merge_certificate :
    ¬ MergeRefinementCert demoSemantics oldGoals .proofSound := by
  intro certificate
  exact weak_merge_history_refutes_old_goals
    (certificate.forwardSufficient
      weakMergeHistory weak_merge_history_satisfies_replacement_goals)

/-! ## Proof-carrying split/merge registration -/

/-- Every demo goal starts present and open before refinement registration. -/
def openSnapshot : GoalWorkSnapshot demoSystem where
  goalPresent := fun _ => true
  goalStatus := fun _ => .open
  workStatus := fun _ => .active

/-- A lawful split registration retains the original parent snapshot. -/
def legalSplitRegistration :
    SplitRegistration
      demoSemantics openSnapshot openSnapshot .hardParent legalChildren where
  certificate := legalSplitCertificate
  childrenPresent := by
    intro _ _
    rfl
  parentPresencePreserved := rfl
  parentOpenPreserved := fun _ => rfl

/-- RCC-20: registering the lawful split neither deletes nor closes its parent. -/
theorem legal_split_registration_keeps_parent :
    openSnapshot.goalPresent .hardParent = true ∧
      openSnapshot.goalStatus .hardParent = .open := by
  exact split_parent_not_dropped legalSplitRegistration rfl rfl

/-- Presence-dropping split mutant: the parent disappears while children remain. -/
def droppedSplitParentSnapshot : GoalWorkSnapshot demoSystem where
  goalPresent := fun
    | .hardParent => false
    | _ => true
  goalStatus := fun _ => .open
  workStatus := fun _ => .active

theorem dropped_parent_has_no_split_registration :
    ¬ SplitRegistration
      demoSemantics openSnapshot droppedSplitParentSnapshot .hardParent legalChildren := by
  intro registration
  have hparent := split_parent_not_dropped registration rfl rfl
  have hpresent := hparent.1
  simp [droppedSplitParentSnapshot] at hpresent

/--
Premature-close split mutant: child registration alone cannot mark the parent satisfied.
-/
def prematurelySatisfiedSplitSnapshot : GoalWorkSnapshot demoSystem where
  goalPresent := fun _ => true
  goalStatus := fun
    | .hardParent => .satisfied
    | _ => .open
  workStatus := fun _ => .active

theorem prematurely_satisfied_parent_has_no_split_registration :
    ¬ SplitRegistration
      demoSemantics openSnapshot prematurelySatisfiedSplitSnapshot .hardParent legalChildren := by
  intro registration
  have hparent := split_parent_not_dropped registration rfl rfl
  have hopen := hparent.2
  simp [prematurelySatisfiedSplitSnapshot] at hopen

/-- A lawful merge registration retains every original goal while adding its replacement. -/
def legalMergeRegistration :
    MergeRegistration
      demoSemantics openSnapshot openSnapshot oldGoals .hardParent where
  certificate := hardParentMergeCertificate
  replacementPresent := rfl
  originalPresencePreserved := by
    intro _ _
    rfl
  originalOpenPreserved := by
    intro _ _ _
    rfl

/-- RCC-20 applies the not-dropped invariant to any selected original merge parent. -/
theorem legal_merge_registration_keeps_runtime_parent :
    openSnapshot.goalPresent .runtimeBound = true ∧
      openSnapshot.goalStatus .runtimeBound = .open := by
  exact merge_parent_not_dropped
    legalMergeRegistration .runtimeBound
      (List.Mem.tail _ (List.Mem.head _)) rfl rfl

/-- Presence-dropping merge mutant: one of the old goals disappears. -/
def droppedMergeParentSnapshot : GoalWorkSnapshot demoSystem where
  goalPresent := fun
    | .runtimeBound => false
    | _ => true
  goalStatus := fun _ => .open
  workStatus := fun _ => .active

theorem dropped_parent_has_no_merge_registration :
    ¬ MergeRegistration
      demoSemantics openSnapshot droppedMergeParentSnapshot oldGoals .hardParent := by
  intro registration
  have hparent := merge_parent_not_dropped
    registration .runtimeBound
      (List.Mem.tail _ (List.Mem.head _)) rfl rfl
  have hpresent := hparent.1
  simp [droppedMergeParentSnapshot] at hpresent

/-- Premature-close merge mutant: registration cannot silently satisfy an old goal. -/
def prematurelySatisfiedMergeSnapshot : GoalWorkSnapshot demoSystem where
  goalPresent := fun _ => true
  goalStatus := fun
    | .runtimeBound => .satisfied
    | _ => .open
  workStatus := fun _ => .active

theorem prematurely_satisfied_parent_has_no_merge_registration :
    ¬ MergeRegistration
      demoSemantics openSnapshot prematurelySatisfiedMergeSnapshot oldGoals .hardParent := by
  intro registration
  have hparent := merge_parent_not_dropped
    registration .runtimeBound
      (List.Mem.tail _ (List.Mem.head _)) rfl rfl
  have hopen := hparent.2
  simp [prematurelySatisfiedMergeSnapshot] at hopen

end Residua.RCC.GoalRefinementTests


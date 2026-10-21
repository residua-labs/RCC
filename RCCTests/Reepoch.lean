import RCC.Reepoch

/-!
# RCC-23 Reepoch Witnesses and Countermodels

The positive witness carries a semantic policy delta, one admitted obstruction,
semantic debt refinement, an exact parent, a fresh occurrence, and a decreasing
finite-campaign measure. Countermodels pin the forbidden shortcuts:

1. address-only epoch change;
2. missing admitted trigger;
3. dropped old debt;
4. origin-only goal migration;
5. cyclic lineage;
6. reused obstruction occurrence;
7. sibling migration edges reusing one globally reserved occurrence.
-/

open Residua.RCC

namespace Residua.RCC.ReepochTests

inductive DemoEpoch
  | base
  | addressOnly
  | child
  | cyclicChild
  deriving DecidableEq

inductive DemoGoal
  | debt
  | replacement
  deriving DecidableEq

inductive DemoOccurrence
  | observation
  | obstruction
  | reusedObstruction
  deriving DecidableEq

def demoSemanticValue : DemoEpoch → EpochSemanticSlot → Nat
  | .base, _ => 0
  | .addressOnly, _ => 0
  | .child, .policy => 1
  | .child, _ => 0
  | .cyclicChild, .policy => 1
  | .cyclicChild, _ => 0

def demoSystem : ReepochSystem where
  Epoch := DemoEpoch
  Goal := DemoGoal
  Occurrence := DemoOccurrence
  SemanticValue := Nat
  GoalOrigin := Nat
  semanticValue := demoSemanticValue
  parentEpoch := fun
    | .child => some .base
    | .cyclicChild => some .base
    | _ => none
  goalOrigin := fun _ => 7
  goalSatisfied := fun epoch goal =>
    (epoch = .base ∧ goal = .debt) ∨
      (epoch = .child ∧ goal = .replacement)
  nonterminal := fun epoch goal => epoch = .base ∧ goal = .debt
  terminalAtMigration := fun _ _ => False
  triggerOccurrence := fun
    | .child => some .obstruction
    | _ => none
  migrationForOccurrence := fun
    | .obstruction => some (.base, .child)
    | _ => none
  newObservationAdmitted := fun epoch occurrence =>
    epoch = .base ∧ occurrence = .observation
  policyDecisionAdmitted := fun _ _ => False
  kernelReplacementAdmitted := fun _ _ => False
  stableObstructionAdmitted := fun epoch occurrence =>
    (epoch = .base ∨ epoch = .child) ∧
      (occurrence = .obstruction ∨ occurrence = .reusedObstruction)
  epochMeasure := fun
    | .base => 2
    | .child => 1
    | .addressOnly => 2
    | .cyclicChild => 2

theorem demo_base_has_no_consumed_occurrence
    (occurrence : DemoOccurrence) :
    ¬ OccurrenceConsumed demoSystem .base occurrence := by
  intro hconsumed
  rcases hconsumed.current_record_or_parent with hrecorded | ⟨parent, hparent⟩
  · simp [demoSystem] at hrecorded
  · simp [demoSystem] at hparent

theorem demo_has_no_ancestor_to_base
    (earlier : DemoEpoch) :
    ¬ ParentAncestor demoSystem earlier .base := by
  intro hancestor
  rcases hancestor.target_has_parent with ⟨parent, hparent⟩
  simp [demoSystem] at hparent

def legitimateTrigger : AdmittedTrigger demoSystem .base :=
  .stableObstruction .obstruction (by
    simp [demoSystem])

def legitimateDebtPlan : DebtPlan demoSystem .base .child where
  resolve := fun goal hnonterminal => by
    cases goal with
    | debt =>
        exact .migrated {
          newGoal := .replacement
          originBound := rfl
          semanticRefinement := by
            intro _
            exact Or.inl ⟨rfl, rfl⟩
        }
    | replacement =>
        simp [demoSystem] at hnonterminal

def legitimateReepoch : ReepochCert demoSystem .base .child where
  delta := .policyChanged (by
    simp [demoSystem, demoSemanticValue])
  trigger := legitimateTrigger
  triggerFresh :=
    demo_base_has_no_consumed_occurrence .obstruction
  parentBound := rfl
  triggerBound := rfl
  occurrenceReserved := rfl
  debtPlan := legitimateDebtPlan
  lineage := .finiteCampaign (by
    simp [demoSystem])

def legitimateOpenReepoch : ReepochCert demoSystem .base .child where
  delta := legitimateReepoch.delta
  trigger := legitimateReepoch.trigger
  triggerFresh := legitimateReepoch.triggerFresh
  parentBound := legitimateReepoch.parentBound
  triggerBound := legitimateReepoch.triggerBound
  occurrenceReserved := legitimateReepoch.occurrenceReserved
  debtPlan := legitimateReepoch.debtPlan
  lineage := .openLineage
    (demo_has_no_ancestor_to_base .child)

theorem legitimate_reepoch_has_semantic_delta :
    Nonempty (EpochDelta demoSystem .base .child) :=
  ⟨legitimateReepoch.delta⟩

theorem legitimate_reepoch_uses_exact_parent :
    demoSystem.parentEpoch .child = some .base :=
  reepoch_binds_exact_parent legitimateReepoch

theorem legitimate_reepoch_derives_parent_ancestry :
    ParentAncestor demoSystem .base .child :=
  reepoch_parent_is_ancestor legitimateReepoch

theorem legitimate_reepoch_records_consumed_trigger :
    OccurrenceConsumed demoSystem .child .obstruction :=
  reepoch_consumes_trigger legitimateReepoch

theorem legitimate_reepoch_preserves_old_debt :
    demoSystem.terminalAtMigration .base .debt ∨
      ∃ migration : GoalMigration demoSystem .base .child .debt,
        migration.originBound =
          (show demoSystem.goalOrigin migration.newGoal =
            demoSystem.goalOrigin .debt from migration.originBound) ∧
        SemanticallyRefines demoSystem .base .child .debt migration.newGoal := by
  rcases reepoch_preserves_old_debt legitimateReepoch .debt (by
    simp [demoSystem]) with hterminal | ⟨migration, hrefinement⟩
  · exact Or.inl hterminal
  · exact Or.inr ⟨migration, rfl, hrefinement⟩

theorem legitimate_finite_campaign_strictly_decreases :
    demoSystem.epochMeasure .child < demoSystem.epochMeasure .base :=
  finite_campaign_decreases legitimateReepoch trivial

theorem legitimate_open_lineage_has_no_back_edge :
    ¬ ParentAncestor demoSystem .child .base :=
  open_lineage_has_no_back_edge legitimateOpenReepoch trivial

/-! ## Countermodel 1: address-only epoch churn -/

theorem address_only_delta_rejected :
    ¬ Nonempty (EpochDelta demoSystem .base .addressOnly) := by
  intro hdelta
  rcases hdelta with ⟨delta⟩
  cases delta <;> simp [demoSystem, demoSemanticValue] at *

/-! ## Countermodel 2: no admitted trigger -/

def noTriggerSystem : ReepochSystem where
  Epoch := DemoEpoch
  Goal := DemoGoal
  Occurrence := DemoOccurrence
  SemanticValue := Nat
  GoalOrigin := Nat
  semanticValue := demoSemanticValue
  parentEpoch := demoSystem.parentEpoch
  goalOrigin := demoSystem.goalOrigin
  goalSatisfied := demoSystem.goalSatisfied
  nonterminal := demoSystem.nonterminal
  terminalAtMigration := demoSystem.terminalAtMigration
  triggerOccurrence := demoSystem.triggerOccurrence
  migrationForOccurrence := demoSystem.migrationForOccurrence
  newObservationAdmitted := fun _ _ => False
  policyDecisionAdmitted := fun _ _ => False
  kernelReplacementAdmitted := fun _ _ => False
  stableObstructionAdmitted := fun _ _ => False
  epochMeasure := demoSystem.epochMeasure

theorem missing_trigger_rejected :
    ¬ Nonempty (AdmittedTrigger noTriggerSystem .base) := by
  intro htrigger
  rcases htrigger with ⟨trigger⟩
  cases trigger <;> simp [noTriggerSystem] at *

/-! ## Countermodel 3: old debt omitted from a migration table -/

def droppedDebtTable : DemoGoal → Option DemoGoal :=
  fun _ => none

theorem dropped_debt_rejected :
    ¬ (∀ goal, demoSystem.nonterminal .base goal →
      ∃ successorGoal, droppedDebtTable goal = some successorGoal) := by
  intro hdropped
  obtain ⟨successorGoal, hsome⟩ := hdropped .debt (by
    simp [demoSystem])
  simp [droppedDebtTable] at hsome

theorem certified_plan_cannot_drop_debt
    (plan : DebtPlan demoSystem .base .child) :
    Nonempty (GoalDisposition demoSystem .base .child .debt) :=
  ⟨plan.resolve .debt (by simp [demoSystem])⟩

/-! ## Countermodel 4: origin equality without semantic refinement -/

def originOnlySystem : ReepochSystem where
  Epoch := DemoEpoch
  Goal := DemoGoal
  Occurrence := DemoOccurrence
  SemanticValue := Nat
  GoalOrigin := Nat
  semanticValue := demoSemanticValue
  parentEpoch := demoSystem.parentEpoch
  goalOrigin := fun _ => 11
  goalSatisfied := fun epoch goal =>
    epoch = .child ∧ goal = .replacement
  nonterminal := demoSystem.nonterminal
  terminalAtMigration := demoSystem.terminalAtMigration
  triggerOccurrence := demoSystem.triggerOccurrence
  migrationForOccurrence := demoSystem.migrationForOccurrence
  newObservationAdmitted := demoSystem.newObservationAdmitted
  policyDecisionAdmitted := demoSystem.policyDecisionAdmitted
  kernelReplacementAdmitted := demoSystem.kernelReplacementAdmitted
  stableObstructionAdmitted := demoSystem.stableObstructionAdmitted
  epochMeasure := demoSystem.epochMeasure

theorem origin_only_migration_has_same_origin :
    originOnlySystem.goalOrigin .replacement =
      originOnlySystem.goalOrigin .debt := by
  rfl

theorem origin_only_migration_lacks_semantic_refinement :
    ¬ SemanticallyRefines originOnlySystem .base .child .debt .replacement := by
  intro hrefinement
  have hnew : originOnlySystem.goalSatisfied .child .replacement := by
    simp [originOnlySystem]
  have hold := hrefinement hnew
  simp [originOnlySystem] at hold

/-! ## Countermodel 5: a back-edge would create a parent cycle -/

def cyclicSystem : ReepochSystem where
  Epoch := DemoEpoch
  Goal := DemoGoal
  Occurrence := DemoOccurrence
  SemanticValue := Nat
  GoalOrigin := Nat
  semanticValue := demoSemanticValue
  parentEpoch := fun
    | .base => some .cyclicChild
    | .cyclicChild => some .base
    | .child => some .base
    | .addressOnly => none
  goalOrigin := demoSystem.goalOrigin
  goalSatisfied := demoSystem.goalSatisfied
  nonterminal := demoSystem.nonterminal
  terminalAtMigration := demoSystem.terminalAtMigration
  triggerOccurrence := fun _ => none
  migrationForOccurrence := fun _ => none
  newObservationAdmitted := demoSystem.newObservationAdmitted
  policyDecisionAdmitted := demoSystem.policyDecisionAdmitted
  kernelReplacementAdmitted := demoSystem.kernelReplacementAdmitted
  stableObstructionAdmitted := demoSystem.stableObstructionAdmitted
  epochMeasure := fun _ => 1

theorem parent_cycle_rejected :
    ¬ Nonempty (LineageCert cyclicSystem .base .cyclicChild) := by
  intro hlineage
  rcases hlineage with ⟨lineage⟩
  cases lineage with
  | finiteCampaign hdecrease =>
      simp [cyclicSystem] at hdecrease
  | openLineage hacyclic =>
      exact hacyclic (.direct rfl)

/-! ## Countermodel 6: a consumed obstruction occurrence is not fresh -/

def reusedObstructionTrigger : AdmittedTrigger demoSystem .child :=
  .stableObstruction .obstruction (by
    simp [demoSystem])

theorem reused_obstruction_is_not_fresh :
    ¬ TriggerFresh demoSystem .child reusedObstructionTrigger := by
  intro hfresh
  exact hfresh (.here rfl)

theorem reused_obstruction_cannot_certify_reepoch :
    ¬ ∃ cert : ReepochCert demoSystem .child .cyclicChild,
      cert.trigger = reusedObstructionTrigger := by
  intro hcert
  rcases hcert with ⟨cert, htrigger⟩
  have hfresh := cert.triggerFresh
  rw [htrigger] at hfresh
  exact reused_obstruction_is_not_fresh hfresh

/-!
## Reviewer exploit: caller-local `False` cannot hide a cyclic parent graph or reuse

The same two-epoch system contains both parent directions and records the same Unit
occurrence at both epochs. Ancestor and consumption evidence must be derived from those
records; there is no caller-supplied `ancestor := False` or `triggerConsumed := False`.
-/

inductive CycleEpoch
  | a
  | b
  deriving DecidableEq

def cycleReuseSystem : ReepochSystem where
  Epoch := CycleEpoch
  Goal := Unit
  Occurrence := Unit
  SemanticValue := Nat
  GoalOrigin := Unit
  semanticValue := fun
    | .a, _ => 0
    | .b, _ => 1
  parentEpoch := fun
    | .a => some .b
    | .b => some .a
  triggerOccurrence := fun _ => some ()
  migrationForOccurrence := fun _ => some (.a, .b)
  goalOrigin := fun _ => ()
  goalSatisfied := fun _ _ => True
  nonterminal := fun _ _ => False
  terminalAtMigration := fun _ _ => False
  newObservationAdmitted := fun _ _ => False
  policyDecisionAdmitted := fun _ _ => False
  kernelReplacementAdmitted := fun _ _ => False
  stableObstructionAdmitted := fun _ _ => True
  epochMeasure := fun _ => 0

def cycleReuseTriggerA : AdmittedTrigger cycleReuseSystem .a :=
  .stableObstruction () trivial

def cycleReuseTriggerB : AdmittedTrigger cycleReuseSystem .b :=
  .stableObstruction () trivial

theorem parent_graph_derives_b_ancestor_a :
    ParentAncestor cycleReuseSystem .b .a :=
  .direct rfl

theorem parent_graph_derives_a_ancestor_b :
    ParentAncestor cycleReuseSystem .a .b :=
  .direct rfl

theorem cycle_edge_a_to_b_rejected :
    ¬ Nonempty (LineageCert cycleReuseSystem .a .b) := by
  intro hlineage
  rcases hlineage with ⟨lineage⟩
  cases lineage with
  | finiteCampaign hdecrease =>
      exact (Nat.lt_irrefl 0) hdecrease
  | openLineage hback =>
      exact hback parent_graph_derives_b_ancestor_a

theorem cycle_edge_b_to_a_rejected :
    ¬ Nonempty (LineageCert cycleReuseSystem .b .a) := by
  intro hlineage
  rcases hlineage with ⟨lineage⟩
  cases lineage with
  | finiteCampaign hdecrease =>
      exact (Nat.lt_irrefl 0) hdecrease
  | openLineage hback =>
      exact hback parent_graph_derives_a_ancestor_b

theorem reviewer_exploit_a_to_b_cannot_certify :
    ¬ Nonempty (ReepochCert cycleReuseSystem .a .b) := by
  intro hcert
  rcases hcert with ⟨cert⟩
  exact cycle_edge_a_to_b_rejected ⟨cert.lineage⟩

theorem reviewer_exploit_b_to_a_cannot_certify :
    ¬ Nonempty (ReepochCert cycleReuseSystem .b .a) := by
  intro hcert
  rcases hcert with ⟨cert⟩
  exact cycle_edge_b_to_a_rejected ⟨cert.lineage⟩

theorem cumulative_unit_occurrence_is_consumed_at_a :
    OccurrenceConsumed cycleReuseSystem .a () :=
  .here rfl

theorem cumulative_unit_occurrence_is_consumed_at_b :
    OccurrenceConsumed cycleReuseSystem .b () :=
  .here rfl

theorem same_unit_occurrence_reuse_rejected_at_a :
    ¬ TriggerFresh cycleReuseSystem .a cycleReuseTriggerA := by
  intro hfresh
  exact hfresh cumulative_unit_occurrence_is_consumed_at_a

theorem same_unit_occurrence_reuse_rejected_at_b :
    ¬ TriggerFresh cycleReuseSystem .b cycleReuseTriggerB := by
  intro hfresh
  exact hfresh cumulative_unit_occurrence_is_consumed_at_b

/-!
## Reviewer exploit: one occurrence cannot reserve two sibling migration edges

Both children are fresh relative to the root's ancestor chain. The snapshot-global
reservation nevertheless assigns Unit to exactly one migration edge.
-/

inductive SiblingEpoch
  | root
  | left
  | right
  deriving DecidableEq

def siblingSystem : ReepochSystem where
  Epoch := SiblingEpoch
  Goal := Unit
  Occurrence := Unit
  SemanticValue := Nat
  GoalOrigin := Unit
  semanticValue := fun
    | .root, _ => 0
    | .left, _ => 1
    | .right, _ => 2
  parentEpoch := fun
    | .root => none
    | .left => some .root
    | .right => some .root
  triggerOccurrence := fun
    | .root => none
    | .left => some ()
    | .right => some ()
  migrationForOccurrence := fun _ => some (.root, .left)
  goalOrigin := fun _ => ()
  goalSatisfied := fun _ _ => True
  nonterminal := fun _ _ => False
  terminalAtMigration := fun _ _ => False
  newObservationAdmitted := fun _ _ => False
  policyDecisionAdmitted := fun _ _ => False
  kernelReplacementAdmitted := fun _ _ => False
  stableObstructionAdmitted := fun _ _ => True
  epochMeasure := fun
    | .root => 2
    | .left => 1
    | .right => 1

def siblingRootTrigger : AdmittedTrigger siblingSystem .root :=
  .stableObstruction () trivial

theorem sibling_root_occurrence_is_chain_fresh :
    TriggerFresh siblingSystem .root siblingRootTrigger := by
  intro hconsumed
  rcases hconsumed.current_record_or_parent with hrecorded | ⟨parent, hparent⟩
  · simp [siblingSystem] at hrecorded
  · simp [siblingSystem] at hparent

def siblingDebtPlan
    (successor : SiblingEpoch) :
    DebtPlan siblingSystem .root successor where
  resolve := fun goal hnonterminal => by
    simp [siblingSystem] at hnonterminal

def siblingLeftCert : ReepochCert siblingSystem .root .left where
  delta := .policyChanged (by
    simp [siblingSystem])
  trigger := siblingRootTrigger
  triggerFresh := sibling_root_occurrence_is_chain_fresh
  parentBound := rfl
  triggerBound := rfl
  occurrenceReserved := rfl
  debtPlan := siblingDebtPlan .left
  lineage := .finiteCampaign (by
    simp [siblingSystem])

theorem sibling_right_reuse_rejected :
    ¬ Nonempty (ReepochCert siblingSystem .root .right) := by
  intro hcert
  rcases hcert with ⟨rightCert⟩
  have hsameOccurrence :
      siblingLeftCert.trigger.occurrence = rightCert.trigger.occurrence := by
    cases rightCert.trigger.occurrence
    rfl
  have hsameEdge :=
    same_occurrence_reservation_unique
      siblingLeftCert rightCert hsameOccurrence
  simp at hsameEdge

theorem same_occurrence_cannot_certify_both_siblings :
    ¬ (Nonempty (ReepochCert siblingSystem .root .left) ∧
      Nonempty (ReepochCert siblingSystem .root .right)) := by
  intro hboth
  exact sibling_right_reuse_rejected hboth.2

#print axioms legitimate_reepoch_preserves_old_debt
#print axioms address_only_delta_rejected
#print axioms missing_trigger_rejected
#print axioms dropped_debt_rejected
#print axioms origin_only_migration_lacks_semantic_refinement
#print axioms parent_cycle_rejected
#print axioms reused_obstruction_cannot_certify_reepoch
#print axioms cycle_edge_a_to_b_rejected
#print axioms cycle_edge_b_to_a_rejected
#print axioms reviewer_exploit_a_to_b_cannot_certify
#print axioms reviewer_exploit_b_to_a_cannot_certify
#print axioms same_unit_occurrence_reuse_rejected_at_a
#print axioms same_unit_occurrence_reuse_rejected_at_b
#print axioms same_occurrence_reservation_unique
#print axioms sibling_right_reuse_rejected
#print axioms same_occurrence_cannot_certify_both_siblings

end Residua.RCC.ReepochTests


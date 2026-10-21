import RCCTests.Reepoch

/-! RCC-93 candidate: conservative reepoch lineage and debt conservation. -/

namespace Residua.RCC.RCC93Target

open Residua.RCC.ReepochTests
open Residua.RCC

def semanticDeltaExists := legitimate_reepoch_has_semantic_delta
def exactParentBound := legitimate_reepoch_uses_exact_parent
def parentAncestryDerived := legitimate_reepoch_derives_parent_ancestry
def triggerConsumed := legitimate_reepoch_records_consumed_trigger
def oldDebtPreserved := legitimate_reepoch_preserves_old_debt
def finiteCampaignDecreases := legitimate_finite_campaign_strictly_decreases
def openLineageNoBackEdge := legitimate_open_lineage_has_no_back_edge
def addressOnlyRejected := address_only_delta_rejected
def missingTriggerRejected := missing_trigger_rejected
def droppedDebtRejected := dropped_debt_rejected
def certifiedPlanPreservesDebt := certified_plan_cannot_drop_debt
def originOnlyNoRefinement := origin_only_migration_lacks_semantic_refinement
def parentCycleRejected := parent_cycle_rejected
def reusedObstructionNotFresh := reused_obstruction_is_not_fresh
def reusedObstructionRejected := reused_obstruction_cannot_certify_reepoch
def cycleEdgeAToBRejected := cycle_edge_a_to_b_rejected
def cycleEdgeBToARejected := cycle_edge_b_to_a_rejected
def reviewerExploitAToBRejected := reviewer_exploit_a_to_b_cannot_certify
def reviewerExploitBToARejected := reviewer_exploit_b_to_a_cannot_certify
def reusedUnitAtARejected := same_unit_occurrence_reuse_rejected_at_a
def reusedUnitAtBRejected := same_unit_occurrence_reuse_rejected_at_b

abbrev SemanticDeltaExists : Prop :=
  Nonempty (EpochDelta demoSystem .base .child)
abbrev ExactParentBound : Prop :=
  demoSystem.parentEpoch .child = some .base
abbrev ParentAncestryDerived : Prop :=
  ParentAncestor demoSystem .base .child
abbrev TriggerConsumed : Prop :=
  OccurrenceConsumed demoSystem .child .obstruction
abbrev OldDebtPreserved : Prop :=
  demoSystem.terminalAtMigration .base .debt ∨
    ∃ migration : GoalMigration demoSystem .base .child .debt,
      migration.originBound =
          (show demoSystem.goalOrigin migration.newGoal =
            demoSystem.goalOrigin .debt from migration.originBound) ∧
        SemanticallyRefines demoSystem .base .child .debt migration.newGoal
abbrev FiniteCampaignDecreases : Prop :=
  demoSystem.epochMeasure .child < demoSystem.epochMeasure .base
abbrev OpenLineageNoBackEdge : Prop :=
  ¬ ParentAncestor demoSystem .child .base
abbrev AddressOnlyRejected : Prop :=
  ¬ Nonempty (EpochDelta demoSystem .base .addressOnly)
abbrev MissingTriggerRejected : Prop :=
  ¬ Nonempty (AdmittedTrigger noTriggerSystem .base)
abbrev DroppedDebtRejected : Prop :=
  ¬ (∀ goal, demoSystem.nonterminal .base goal →
      ∃ successorGoal, droppedDebtTable goal = some successorGoal)
abbrev CertifiedPlanPreservesDebt : Prop :=
  ∀ (plan : DebtPlan demoSystem .base .child),
    Nonempty (GoalDisposition demoSystem .base .child .debt)
abbrev OriginOnlyNoRefinement : Prop :=
  ¬ SemanticallyRefines originOnlySystem .base .child .debt .replacement
abbrev ParentCycleRejected : Prop :=
  ¬ Nonempty (LineageCert cyclicSystem .base .cyclicChild)
abbrev ReusedObstructionNotFresh : Prop :=
  ¬ TriggerFresh demoSystem .child reusedObstructionTrigger
abbrev ReusedObstructionRejected : Prop :=
  ¬ ∃ cert : ReepochCert demoSystem .child .cyclicChild,
      cert.trigger = reusedObstructionTrigger
abbrev CycleEdgeAToBRejected : Prop :=
  ¬ Nonempty (LineageCert cycleReuseSystem .a .b)
abbrev CycleEdgeBToARejected : Prop :=
  ¬ Nonempty (LineageCert cycleReuseSystem .b .a)
abbrev ReviewerExploitAToBRejected : Prop :=
  ¬ Nonempty (ReepochCert cycleReuseSystem .a .b)
abbrev ReviewerExploitBToARejected : Prop :=
  ¬ Nonempty (ReepochCert cycleReuseSystem .b .a)
abbrev ReusedUnitAtARejected : Prop :=
  ¬ TriggerFresh cycleReuseSystem .a cycleReuseTriggerA
abbrev ReusedUnitAtBRejected : Prop :=
  ¬ TriggerFresh cycleReuseSystem .b cycleReuseTriggerB

structure Certificate where
  semanticDeltaExists : SemanticDeltaExists
  exactParentBound : ExactParentBound
  parentAncestryDerived : ParentAncestryDerived
  triggerConsumed : TriggerConsumed
  oldDebtPreserved : OldDebtPreserved
  finiteCampaignDecreases : FiniteCampaignDecreases
  openLineageNoBackEdge : OpenLineageNoBackEdge
  addressOnlyRejected : AddressOnlyRejected
  missingTriggerRejected : MissingTriggerRejected
  droppedDebtRejected : DroppedDebtRejected
  certifiedPlanPreservesDebt : CertifiedPlanPreservesDebt
  originOnlyNoRefinement : OriginOnlyNoRefinement
  parentCycleRejected : ParentCycleRejected
  reusedObstructionNotFresh : ReusedObstructionNotFresh
  reusedObstructionRejected : ReusedObstructionRejected
  cycleEdgeAToBRejected : CycleEdgeAToBRejected
  cycleEdgeBToARejected : CycleEdgeBToARejected
  reviewerExploitAToBRejected : ReviewerExploitAToBRejected
  reviewerExploitBToARejected : ReviewerExploitBToARejected
  reusedUnitAtARejected : ReusedUnitAtARejected
  reusedUnitAtBRejected : ReusedUnitAtBRejected

def certificate : Certificate where
  semanticDeltaExists := legitimate_reepoch_has_semantic_delta
  exactParentBound := legitimate_reepoch_uses_exact_parent
  parentAncestryDerived := legitimate_reepoch_derives_parent_ancestry
  triggerConsumed := legitimate_reepoch_records_consumed_trigger
  oldDebtPreserved := legitimate_reepoch_preserves_old_debt
  finiteCampaignDecreases := legitimate_finite_campaign_strictly_decreases
  openLineageNoBackEdge := legitimate_open_lineage_has_no_back_edge
  addressOnlyRejected := address_only_delta_rejected
  missingTriggerRejected := missing_trigger_rejected
  droppedDebtRejected := dropped_debt_rejected
  certifiedPlanPreservesDebt := certified_plan_cannot_drop_debt
  originOnlyNoRefinement := origin_only_migration_lacks_semantic_refinement
  parentCycleRejected := parent_cycle_rejected
  reusedObstructionNotFresh := reused_obstruction_is_not_fresh
  reusedObstructionRejected := reused_obstruction_cannot_certify_reepoch
  cycleEdgeAToBRejected := cycle_edge_a_to_b_rejected
  cycleEdgeBToARejected := cycle_edge_b_to_a_rejected
  reviewerExploitAToBRejected := reviewer_exploit_a_to_b_cannot_certify
  reviewerExploitBToARejected := reviewer_exploit_b_to_a_cannot_certify
  reusedUnitAtARejected := same_unit_occurrence_reuse_rejected_at_a
  reusedUnitAtBRejected := same_unit_occurrence_reuse_rejected_at_b

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC93Target

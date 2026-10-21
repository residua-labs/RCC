import RCCTests.CrossEpochFairness94

/-! RCC-94 candidate: cross-epoch fairness and bounded-overtaking obligations. -/

namespace Residua.RCC.RCC94Target

open Residua.RCC.CrossEpochFairness94.Tests
open Residua.RCC.CrossEpochFairness94

def starvationSelectionLegal := starvation_selection_is_legal
def starvationLawfullyCarried := starvation_run_is_lawfully_carried
def starvationContinuouslyReady := starvation_run_continuously_ready
def starvationNeverSelected := starvation_run_never_selects_target
def conservationDoesNotImplyLiveness := lawful_conservation_does_not_imply_liveness
def starvationViolatesOvertakingBound := starvation_violates_every_overtaking_bound
def starvationCoverageNamesFailure := starvation_coverage_yields_named_failure
def blockedAgeResetRejected := blocked_age_reset_is_not_lawful
def missingGoalSelectionRejected := selecting_missing_goal_is_illegal
def nonreadySelectionRejected := selecting_nonready_goal_is_illegal
def nonmandatorySelectionRejected := selecting_nonmandatory_goal_is_illegal
def fairRunContinuouslyReady := fair_run_continuously_ready
def fairRunLawfullyCarried := fair_run_is_lawfully_carried
def fairRunBounded := fair_run_bounded
def fairRunQuota := fair_run_quota
def fairRunAging := fair_run_aging
def fairRunWeakFairFromBound := fair_run_weak_fair_from_bound
def fairRunWeakFairFromQuota := fair_run_weak_fair_from_quota
def fairRunWeakFairFromAging := fair_run_weak_fair_from_aging
def fairRunWeakFairFromDiscipline := fair_run_weak_fair_from_discipline
def fairRunWeakFairFromQuotaDiscipline := fair_run_weak_fair_from_quota_discipline
def fairRunWeakFairFromAgingDiscipline := fair_run_weak_fair_from_aging_discipline
def fairRunSelectionGrounded := fair_run_selection_is_receipt_grounded
def fairRunContractGrounded := fair_run_weak_fair_from_scheduling_contract
def campaignLawfullyCarried := campaign_run_is_lawfully_carried
def campaignWeakFair := campaign_run_weak_fair_from_isolation
def campaignContractWeakFair := campaign_run_weak_fair_from_scheduling_contract
def droppedCampaignRejected := dropped_unselected_campaign_is_not_lawful
def droppedCampaignNoIsolation := dropped_unselected_campaign_has_no_isolation_certificate
def illegalSelectionRunRejected := illegal_selection_run_is_not_lawful
def illegalSelectionNoContract := illegal_selection_run_has_no_scheduling_contract
def starvationNoQuota := starvation_has_no_quota
def starvationNoAging := starvation_has_no_aging_policy
def starvationNoIsolation := starvation_has_no_campaign_isolation
def starvationNoPreemption := starvation_has_no_preemption_discipline
def priorityWithoutDisciplineRejected := priority_preemption_without_discipline_has_no_contract
def finiteInnerNormalizationCloses := every_epoch_inner_normalization_closes
def innerClosureCoexistsWithStarvation := finite_inner_normalization_coexists_with_lineage_starvation

abbrev StarvationSelectionLegal : Prop :=
  ∀ epoch : Nat, SelectionLegal (starvationRun epoch)
abbrev StarvationLawfullyCarried : Prop := LawfulLineageRun starvationRun
abbrev StarvationContinuouslyReady : Prop :=
  ContinuouslyReadyMandatory starvationRun .target 0
abbrev StarvationNeverSelected : Prop := NeverSelected starvationRun .target 0
abbrev ConservationDoesNotImplyLiveness : Prop := ¬ WeakFairness starvationRun
abbrev StarvationViolatesOvertakingBound : Prop :=
  ∀ bound, ¬ BoundedOvertaking starvationRun bound
abbrev StarvationCoverageNamesFailure : Prop :=
  WeakFairness starvationRun ∨
    Nonempty (LineageLivenessResidue starvationRun)
abbrev BlockedAgeResetRejected : Prop :=
  ¬ LawfulCarry blockedResetFrame afterResetFrame
abbrev MissingGoalSelectionRejected : Prop :=
  ¬ SelectionLegal (selectionFrame true true (some .ghost))
abbrev NonreadySelectionRejected : Prop :=
  ¬ SelectionLegal (selectionFrame true false (some .target))
abbrev NonmandatorySelectionRejected : Prop :=
  ¬ SelectionLegal (selectionFrame false true (some .target))
abbrev FairRunContinuouslyReady : Prop :=
  ContinuouslyReadyMandatory fairRun .target 0
abbrev FairRunLawfullyCarried : Prop := LawfulLineageRun fairRun
abbrev FairRunBounded : Prop := BoundedOvertaking fairRun 0
abbrev FairRunQuota : Prop := QuotaDiscipline fairRun 1
abbrev FairRunAging : Prop := AgingDiscipline fairRun 0
abbrev FairRunWeakFairFromBound : Prop := WeakFairness fairRun
abbrev FairRunWeakFairFromQuota : Prop := WeakFairness fairRun
abbrev FairRunWeakFairFromAging : Prop := WeakFairness fairRun
abbrev FairRunWeakFairFromDiscipline : Prop := WeakFairness fairRun
abbrev FairRunWeakFairFromQuotaDiscipline : Prop := WeakFairness fairRun
abbrev FairRunWeakFairFromAgingDiscipline : Prop := WeakFairness fairRun
abbrev FairRunSelectionGrounded : Prop :=
  ∃ receipt,
    fairRunSchedulingContract.selectionBinding.receiptEpoch receipt = 0 ∧
      fairRunSchedulingContract.selectionBinding.receiptLineage receipt =
        .target ∧
      fairRunSchedulingContract.selectionBinding.admittedAtCanonicalHead
        receipt
abbrev FairRunContractGrounded : Prop := WeakFairness fairRun
abbrev CampaignLawfullyCarried : Prop := LawfulLineageRun campaignRun
abbrev CampaignWeakFair : Prop := WeakFairness campaignRun
abbrev CampaignContractWeakFair : Prop := WeakFairness campaignRun
abbrev DroppedCampaignRejected : Prop :=
  ¬ LawfulLineageRun droppedUnselectedCampaignRun
abbrev DroppedCampaignNoIsolation : Prop :=
  ¬ Nonempty (CampaignIsolation droppedUnselectedCampaignRun)
abbrev IllegalSelectionRunRejected : Prop :=
  ¬ LawfulLineageRun illegalSelectionRun
abbrev IllegalSelectionNoContract : Prop :=
  ¬ Nonempty (SchedulingContract illegalSelectionRun)
abbrev StarvationNoQuota : Prop :=
  ∀ window, ¬ QuotaDiscipline starvationRun window
abbrev StarvationNoAging : Prop :=
  ∀ threshold, ¬ AgingDiscipline starvationRun threshold
abbrev StarvationNoIsolation : Prop :=
  ¬ Nonempty (CampaignIsolation starvationRun)
abbrev StarvationNoPreemption : Prop :=
  ¬ Nonempty (PreemptionDiscipline starvationRun)
abbrev PriorityWithoutDisciplineRejected : Prop :=
  ¬ Nonempty (SchedulingContract starvationRun)
abbrev FiniteInnerNormalizationCloses : Prop :=
  ∀ _epoch : Nat,
    (Residua.RCC.normalize innerCountdownExec (3 : Nat)).state? =
      some (0 : Nat)
abbrev InnerClosureCoexistsWithStarvation : Prop :=
  (∀ _epoch : Nat,
    (Residua.RCC.normalize innerCountdownExec (3 : Nat)).state? =
      some (0 : Nat)) ∧
    ¬ WeakFairness starvationRun

structure Certificate where
  starvationSelectionLegal : StarvationSelectionLegal
  starvationLawfullyCarried : StarvationLawfullyCarried
  starvationContinuouslyReady : StarvationContinuouslyReady
  starvationNeverSelected : StarvationNeverSelected
  conservationDoesNotImplyLiveness : ConservationDoesNotImplyLiveness
  starvationViolatesOvertakingBound : StarvationViolatesOvertakingBound
  starvationCoverageNamesFailure : StarvationCoverageNamesFailure
  blockedAgeResetRejected : BlockedAgeResetRejected
  missingGoalSelectionRejected : MissingGoalSelectionRejected
  nonreadySelectionRejected : NonreadySelectionRejected
  nonmandatorySelectionRejected : NonmandatorySelectionRejected
  fairRunContinuouslyReady : FairRunContinuouslyReady
  fairRunLawfullyCarried : FairRunLawfullyCarried
  fairRunBounded : FairRunBounded
  fairRunQuota : FairRunQuota
  fairRunAging : FairRunAging
  fairRunWeakFairFromBound : FairRunWeakFairFromBound
  fairRunWeakFairFromQuota : FairRunWeakFairFromQuota
  fairRunWeakFairFromAging : FairRunWeakFairFromAging
  fairRunWeakFairFromDiscipline : FairRunWeakFairFromDiscipline
  fairRunWeakFairFromQuotaDiscipline : FairRunWeakFairFromQuotaDiscipline
  fairRunWeakFairFromAgingDiscipline : FairRunWeakFairFromAgingDiscipline
  fairRunSelectionGrounded : FairRunSelectionGrounded
  fairRunContractGrounded : FairRunContractGrounded
  campaignLawfullyCarried : CampaignLawfullyCarried
  campaignWeakFair : CampaignWeakFair
  campaignContractWeakFair : CampaignContractWeakFair
  droppedCampaignRejected : DroppedCampaignRejected
  droppedCampaignNoIsolation : DroppedCampaignNoIsolation
  illegalSelectionRunRejected : IllegalSelectionRunRejected
  illegalSelectionNoContract : IllegalSelectionNoContract
  starvationNoQuota : StarvationNoQuota
  starvationNoAging : StarvationNoAging
  starvationNoIsolation : StarvationNoIsolation
  starvationNoPreemption : StarvationNoPreemption
  priorityWithoutDisciplineRejected : PriorityWithoutDisciplineRejected
  finiteInnerNormalizationCloses : FiniteInnerNormalizationCloses
  innerClosureCoexistsWithStarvation : InnerClosureCoexistsWithStarvation

def certificate : Certificate where
  starvationSelectionLegal := starvation_selection_is_legal
  starvationLawfullyCarried := starvation_run_is_lawfully_carried
  starvationContinuouslyReady := starvation_run_continuously_ready
  starvationNeverSelected := starvation_run_never_selects_target
  conservationDoesNotImplyLiveness := lawful_conservation_does_not_imply_liveness
  starvationViolatesOvertakingBound := starvation_violates_every_overtaking_bound
  starvationCoverageNamesFailure := starvation_coverage_yields_named_failure
  blockedAgeResetRejected := blocked_age_reset_is_not_lawful
  missingGoalSelectionRejected := selecting_missing_goal_is_illegal
  nonreadySelectionRejected := selecting_nonready_goal_is_illegal
  nonmandatorySelectionRejected := selecting_nonmandatory_goal_is_illegal
  fairRunContinuouslyReady := fair_run_continuously_ready
  fairRunLawfullyCarried := fair_run_is_lawfully_carried
  fairRunBounded := fair_run_bounded
  fairRunQuota := fair_run_quota
  fairRunAging := fair_run_aging
  fairRunWeakFairFromBound := fair_run_weak_fair_from_bound
  fairRunWeakFairFromQuota := fair_run_weak_fair_from_quota
  fairRunWeakFairFromAging := fair_run_weak_fair_from_aging
  fairRunWeakFairFromDiscipline := fair_run_weak_fair_from_discipline
  fairRunWeakFairFromQuotaDiscipline := fair_run_weak_fair_from_quota_discipline
  fairRunWeakFairFromAgingDiscipline := fair_run_weak_fair_from_aging_discipline
  fairRunSelectionGrounded := fair_run_selection_is_receipt_grounded
  fairRunContractGrounded := fair_run_weak_fair_from_scheduling_contract
  campaignLawfullyCarried := campaign_run_is_lawfully_carried
  campaignWeakFair := campaign_run_weak_fair_from_isolation
  campaignContractWeakFair := campaign_run_weak_fair_from_scheduling_contract
  droppedCampaignRejected := dropped_unselected_campaign_is_not_lawful
  droppedCampaignNoIsolation := dropped_unselected_campaign_has_no_isolation_certificate
  illegalSelectionRunRejected := illegal_selection_run_is_not_lawful
  illegalSelectionNoContract := illegal_selection_run_has_no_scheduling_contract
  starvationNoQuota := starvation_has_no_quota
  starvationNoAging := starvation_has_no_aging_policy
  starvationNoIsolation := starvation_has_no_campaign_isolation
  starvationNoPreemption := starvation_has_no_preemption_discipline
  priorityWithoutDisciplineRejected := priority_preemption_without_discipline_has_no_contract
  finiteInnerNormalizationCloses := every_epoch_inner_normalization_closes
  innerClosureCoexistsWithStarvation := finite_inner_normalization_coexists_with_lineage_starvation

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC94Target



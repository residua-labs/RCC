import RCC.CrossEpochFairness94
import RCC.FormalCore

/-!
# RCC-38 Cross-Epoch Goal Fairness Countermodels

The target and overtaker are both real mandatory ready Goals.  Every scheduler
selection is legal, every migration conserves both Goal lineages, and every
mandatory age is monotone.  Nevertheless the target is starved forever.
-/

open Residua.RCC.CrossEpochFairness94

namespace Residua.RCC.CrossEpochFairness94.Tests

inductive LineageQ
  | target
  | overtaker
  | ghost
  deriving DecidableEq, Repr

def targetState (epoch : Nat) : GoalLocalState where
  mandatory := true
  ready := true
  carryAge := epoch

def overtakerState : GoalLocalState where
  mandatory := true
  ready := true
  carryAge := 0

def starvationGoals (epoch : Nat) : LineageQ → Option GoalLocalState
  | .target => some (targetState epoch)
  | .overtaker => some overtakerState
  | .ghost => none

/-- Two real mandatory ready Goals exist, but the scheduler always picks the overtaker. -/
def starvationRun (epoch : Nat) : EpochFrame LineageQ where
  goals := starvationGoals epoch
  selectedLineage := some .overtaker

theorem starvation_selection_is_legal (epoch : Nat) :
    SelectionLegal (starvationRun epoch) := by
  intro lineage selected
  cases lineage with
  | target =>
      simp [GoalSelected, starvationRun] at selected
  | overtaker =>
      exact ⟨overtakerState, rfl, rfl, rfl⟩
  | ghost =>
      simp [GoalSelected, starvationRun] at selected

/-- Both active mandatory Goals are lawfully carried across every reepoch. -/
theorem starvation_run_is_lawfully_carried :
    LawfulLineageRun starvationRun := by
  intro epoch
  constructor
  · exact starvation_selection_is_legal epoch
  · intro lineage state present mandatory
    cases lineage with
    | target =>
        have stateEq : targetState epoch = state :=
          Option.some.inj (by simpa [GoalAt, starvationRun, starvationGoals] using present)
        subst state
        refine
          ⟨targetState (epoch + 1),
            by simp [GoalAt, starvationRun, starvationGoals],
            rfl, Nat.le_succ epoch, ?_⟩
        intro ready notSelected
        exact Nat.lt_succ_self epoch
    | overtaker =>
        have stateEq : overtakerState = state :=
          Option.some.inj (by simpa [GoalAt, starvationRun, starvationGoals] using present)
        subst state
        refine
          ⟨overtakerState,
            by simp [GoalAt, starvationRun, starvationGoals],
            rfl, Nat.le_refl 0, ?_⟩
        intro ready notSelected
        exact False.elim (notSelected rfl)
    | ghost =>
        simp [GoalAt, starvationRun, starvationGoals] at present

theorem starvation_run_continuously_ready :
    ContinuouslyReadyMandatory starvationRun .target 0 := by
  intro epoch afterStart
  exact ⟨targetState epoch, rfl, rfl, rfl⟩

theorem starvation_run_never_selects_target :
    NeverSelected starvationRun .target 0 := by
  intro epoch afterStart selected
  cases selected

def lawfulCarryStarvation :
    GoalStarvationWitness starvationRun .target 0 where
  lawfulCarry := starvation_run_is_lawfully_carried
  continuouslyReady := starvation_run_continuously_ready
  neverSelected := starvation_run_never_selects_target

/-- Conservation and legal busy scheduling do not manufacture liveness. -/
theorem lawful_conservation_does_not_imply_liveness :
    ¬ WeakFairness starvationRun := by
  intro fair
  exact weak_fairness_excludes_starvation fair lawfulCarryStarvation

/-- The starvation run violates every finite bounded-overtaking promise. -/
theorem starvation_violates_every_overtaking_bound :
    ∀ bound, ¬ BoundedOvertaking starvationRun bound := by
  intro bound bounded
  obtain ⟨epoch, afterStart, beforeBound, selected⟩ :=
    bounded .target 0 starvation_run_continuously_ready
  cases selected

def starvationResidue :
    LineageLivenessResidue starvationRun :=
  .goalStarved lawfulCarryStarvation

def unboundedOvertakingResidue :
    LineageLivenessResidue starvationRun :=
  .priorityOvertakingUnbounded starvation_violates_every_overtaking_bound

def unprovedFairnessResidue :
    LineageLivenessResidue starvationRun :=
  .lineageFairnessEvidenceGap
    starvation_run_continuously_ready

def starvationSelectionBinding : SelectionBinding starvationRun where
  Receipt := Nat × LineageQ
  receiptEpoch := Prod.fst
  receiptLineage := Prod.snd
  admittedAtCanonicalHead := fun receipt => receipt.2 = .overtaker
  grounded := by
    intro epoch lineage selected
    cases lineage with
    | target => simp [GoalSelected, starvationRun] at selected
    | overtaker => exact ⟨(epoch, .overtaker), rfl, rfl, rfl⟩
    | ghost => simp [GoalSelected, starvationRun] at selected

def starvationCoverage :
    LineageFairnessCoverage starvationRun where
  lawfulCarry := starvation_run_is_lawfully_carried
  selectionBinding := starvationSelectionBinding
  evidence := .namedFailure starvationResidue

theorem starvation_coverage_yields_named_failure :
    WeakFairness starvationRun ∨
      Nonempty (LineageLivenessResidue starvationRun) :=
  coverage_yields_fairness_or_named_residue starvationCoverage

/-! ## Age-reset countermodels -/

def blockedOld : GoalLocalState where
  mandatory := true
  ready := false
  carryAge := 10

def resetNew : GoalLocalState where
  mandatory := true
  ready := true
  carryAge := 0

def blockedResetFrame : EpochFrame LineageQ where
  goals := fun
    | .target => some blockedOld
    | _ => none
  selectedLineage := none

def afterResetFrame : EpochFrame LineageQ where
  goals := fun
    | .target => some resetNew
    | _ => none
  selectedLineage := none

def blockedAgeResetWitness :
    MigrationAgeResetWitness blockedResetFrame afterResetFrame where
  lineage := .target
  oldState := blockedOld
  newState := resetNew
  oldPresent := rfl
  newPresent := rfl
  mandatory := rfl
  reset := by decide

theorem blocked_age_reset_is_not_lawful :
    ¬ LawfulCarry blockedResetFrame afterResetFrame := by
  intro lawful
  exact
    (migration_cannot_reset_age
      (lineage := .target)
      (oldState := blockedOld)
      (newState := resetNew)
      lawful rfl rfl rfl)
      blockedAgeResetWitness.reset

def blockedAgeResetRun : Nat → EpochFrame LineageQ
  | 0 => blockedResetFrame
  | _ => afterResetFrame

def ageResetResidue :
    LineageLivenessResidue blockedAgeResetRun :=
  .migrationResetsGoalAge (epoch := 0)
    (by simpa [blockedAgeResetRun] using blockedAgeResetWitness)

/-! ## Illegal scheduler choices -/

def selectionFrame
    (targetMandatory targetReady : Bool)
    (selected : Option LineageQ) : EpochFrame LineageQ where
  goals := fun
    | .target =>
        some
          { mandatory := targetMandatory
            ready := targetReady
            carryAge := 0 }
    | _ => none
  selectedLineage := selected

theorem selecting_missing_goal_is_illegal :
    ¬ SelectionLegal (selectionFrame true true (some .ghost)) := by
  intro legal
  obtain ⟨state, present, mandatory, ready⟩ := legal .ghost rfl
  simp [GoalAt, selectionFrame] at present

theorem selecting_nonready_goal_is_illegal :
    ¬ SelectionLegal (selectionFrame true false (some .target)) := by
  intro legal
  obtain ⟨state, present, mandatory, ready⟩ := legal .target rfl
  simp [GoalAt, selectionFrame] at present
  subst state
  cases ready

theorem selecting_nonmandatory_goal_is_illegal :
    ¬ SelectionLegal (selectionFrame false true (some .target)) := by
  intro legal
  obtain ⟨state, present, mandatory, ready⟩ := legal .target rfl
  simp [GoalAt, selectionFrame] at present
  subst state
  cases mandatory

/-! ## Positive controls for all four admitted preemption disciplines -/

def fairGoals (epoch : Nat) : LineageQ → Option GoalLocalState
  | .target => some (targetState epoch)
  | _ => none

def fairRun (epoch : Nat) : EpochFrame LineageQ where
  goals := fairGoals epoch
  selectedLineage := some .target

theorem fair_run_continuously_ready :
    ContinuouslyReadyMandatory fairRun .target 0 := by
  intro epoch afterStart
  exact ⟨targetState epoch, rfl, rfl, rfl⟩

theorem fair_run_is_lawfully_carried :
    LawfulLineageRun fairRun := by
  intro epoch
  constructor
  · intro lineage selected
    cases lineage with
    | target => exact ⟨targetState epoch, rfl, rfl, rfl⟩
    | overtaker => simp [GoalSelected, fairRun] at selected
    | ghost => simp [GoalSelected, fairRun] at selected
  · intro lineage state present mandatory
    cases lineage with
    | target =>
        have stateEq : targetState epoch = state :=
          Option.some.inj
            (by simpa [GoalAt, fairRun, fairGoals] using present)
        subst state
        refine
          ⟨targetState (epoch + 1),
            by simp [GoalAt, fairRun, fairGoals],
            rfl, Nat.le_succ epoch, ?_⟩
        intro ready notSelected
        exact False.elim (notSelected rfl)
    | overtaker => simp [GoalAt, fairRun, fairGoals] at present
    | ghost => simp [GoalAt, fairRun, fairGoals] at present

theorem fair_run_bounded :
    BoundedOvertaking fairRun 0 := by
  intro lineage start continuouslyReady
  obtain ⟨state, present, mandatory, ready⟩ :=
    continuouslyReady start (Nat.le_refl start)
  cases lineage with
  | target =>
      exact ⟨start, Nat.le_refl start, Nat.le_refl start, rfl⟩
  | overtaker =>
      simp [GoalAt, fairRun, fairGoals] at present
  | ghost =>
      simp [GoalAt, fairRun, fairGoals] at present

theorem fair_run_quota :
    QuotaDiscipline fairRun 1 := by
  constructor
  · decide
  · intro lineage start continuouslyReady
    obtain ⟨state, present, mandatory, ready⟩ :=
      continuouslyReady start (Nat.le_refl start)
    cases lineage with
    | target =>
        exact ⟨0, by decide, by simp [GoalSelected, fairRun]⟩
    | overtaker =>
        simp [GoalAt, fairRun, fairGoals] at present
    | ghost =>
        simp [GoalAt, fairRun, fairGoals] at present

theorem fair_run_aging :
    AgingDiscipline fairRun 0 := by
  intro lineage epoch state present mandatory ready thresholdReached
  cases lineage with
  | target => rfl
  | overtaker => simp [GoalAt, fairRun, fairGoals] at present
  | ghost => simp [GoalAt, fairRun, fairGoals] at present

theorem fair_run_weak_fair_from_bound :
    WeakFairness fairRun :=
  bounded_overtaking_implies_weak_fairness fair_run_bounded

theorem fair_run_weak_fair_from_quota :
    WeakFairness fairRun :=
  quota_implies_weak_fairness fair_run_quota

theorem fair_run_weak_fair_from_aging :
    WeakFairness fairRun :=
  aging_implies_weak_fairness fair_run_is_lawfully_carried fair_run_aging

def fairRunDiscipline : PreemptionDiscipline fairRun :=
  .bounded 0 fair_run_bounded

def fairRunQuotaDiscipline : PreemptionDiscipline fairRun :=
  .quota 1 fair_run_quota

def fairRunAgingDiscipline : PreemptionDiscipline fairRun :=
  .aging inferInstance 0 fair_run_is_lawfully_carried fair_run_aging

theorem fair_run_weak_fair_from_discipline :
    WeakFairness fairRun :=
  preemption_discipline_implies_weak_fairness fairRunDiscipline

theorem fair_run_weak_fair_from_quota_discipline :
    WeakFairness fairRun :=
  preemption_discipline_implies_weak_fairness fairRunQuotaDiscipline

theorem fair_run_weak_fair_from_aging_discipline :
    WeakFairness fairRun :=
  preemption_discipline_implies_weak_fairness fairRunAgingDiscipline

def fairRunSelectionBinding : SelectionBinding fairRun where
  Receipt := Nat × LineageQ
  receiptEpoch := Prod.fst
  receiptLineage := Prod.snd
  admittedAtCanonicalHead := fun receipt => receipt.2 = .target
  grounded := by
    intro epoch lineage selected
    cases lineage with
    | target => exact ⟨(epoch, .target), rfl, rfl, rfl⟩
    | overtaker => simp [GoalSelected, fairRun] at selected
    | ghost => simp [GoalSelected, fairRun] at selected

def fairRunSchedulingContract : SchedulingContract fairRun where
  lawfulCarry := fair_run_is_lawfully_carried
  selectionBinding := fairRunSelectionBinding
  preemptionPolicy := .enabled fairRunDiscipline

theorem fair_run_weak_fair_from_scheduling_contract :
    WeakFairness fairRun :=
  scheduling_contract_implies_weak_fairness fairRunSchedulingContract

theorem fair_run_selection_is_receipt_grounded :
    ∃ receipt,
      fairRunSchedulingContract.selectionBinding.receiptEpoch receipt = 0 ∧
        fairRunSchedulingContract.selectionBinding.receiptLineage receipt =
          .target ∧
        fairRunSchedulingContract.selectionBinding.admittedAtCanonicalHead
          receipt :=
  scheduling_selection_is_grounded fairRunSchedulingContract rfl

/-! ## A real sealed campaign fairly services two conserved lineages -/

def campaignState (epoch : Nat) : GoalLocalState where
  mandatory := true
  ready := true
  carryAge := epoch

def campaignGoals (epoch : Nat) : LineageQ → Option GoalLocalState
  | .target => some (campaignState epoch)
  | .overtaker => some (campaignState epoch)
  | .ghost => none

/-- A deterministic two-lineage round robin. -/
def targetTurn : Nat → Bool
  | 0 => true
  | epoch + 1 => !(targetTurn epoch)

def campaignRun (epoch : Nat) : EpochFrame LineageQ where
  goals := campaignGoals epoch
  selectedLineage :=
    if targetTurn epoch then some .target else some .overtaker

theorem campaign_run_is_lawfully_carried :
    LawfulLineageRun campaignRun := by
  intro epoch
  constructor
  · intro lineage selected
    cases lineage with
    | target =>
        exact ⟨campaignState epoch, rfl, rfl, rfl⟩
    | overtaker =>
        exact ⟨campaignState epoch, rfl, rfl, rfl⟩
    | ghost =>
        cases turn : targetTurn epoch <;>
          simp [GoalSelected, campaignRun, turn] at selected
  · intro lineage state present mandatory
    cases lineage with
    | target =>
        have stateEq : campaignState epoch = state :=
          Option.some.inj
            (by simpa [GoalAt, campaignRun, campaignGoals] using present)
        subst state
        refine
          ⟨campaignState (epoch + 1),
            by simp [GoalAt, campaignRun, campaignGoals],
            rfl, Nat.le_succ epoch, ?_⟩
        intro ready notSelected
        exact Nat.lt_succ_self epoch
    | overtaker =>
        have stateEq : campaignState epoch = state :=
          Option.some.inj
            (by simpa [GoalAt, campaignRun, campaignGoals] using present)
        subst state
        refine
          ⟨campaignState (epoch + 1),
            by simp [GoalAt, campaignRun, campaignGoals],
            rfl, Nat.le_succ epoch, ?_⟩
        intro ready notSelected
        exact Nat.lt_succ_self epoch
    | ghost =>
        simp [GoalAt, campaignRun, campaignGoals] at present

def campaignIsolationCertificate :
    CampaignIsolation campaignRun where
  sealedLineages := [.target, .overtaker]
  lawfulCarry := campaign_run_is_lawfully_carried
  universeSealed := by
    intro lineage epoch mandatoryReady
    obtain ⟨state, present, mandatory, ready⟩ := mandatoryReady
    cases lineage with
    | target => exact List.Mem.head _
    | overtaker => exact List.Mem.tail _ (List.Mem.head _)
    | ghost => simp [GoalAt, campaignRun, campaignGoals] at present
  service := by
    intro lineage member start continuouslyReady
    cases lineage with
    | target =>
        cases turn : targetTurn start with
        | false =>
            exact
              ⟨start + 1, Nat.le_add_right start 1,
                by simp [GoalSelected, campaignRun, targetTurn, turn]⟩
        | true =>
            exact
              ⟨start, Nat.le_refl start,
                by simp [GoalSelected, campaignRun, turn]⟩
    | overtaker =>
        cases turn : targetTurn start with
        | false =>
            exact
              ⟨start, Nat.le_refl start,
                by simp [GoalSelected, campaignRun, turn]⟩
        | true =>
            exact
              ⟨start + 1, Nat.le_add_right start 1,
                by simp [GoalSelected, campaignRun, targetTurn, turn]⟩
    | ghost =>
        cases member with
        | tail _ member =>
            cases member with
            | tail _ member => cases member

theorem campaign_run_weak_fair_from_isolation :
    WeakFairness campaignRun :=
  campaign_isolation_implies_weak_fairness
    campaignIsolationCertificate

def campaignRunDiscipline : PreemptionDiscipline campaignRun :=
  .campaignIsolation campaignIsolationCertificate

def campaignRunSelectionBinding : SelectionBinding campaignRun where
  Receipt := Nat × LineageQ
  receiptEpoch := Prod.fst
  receiptLineage := Prod.snd
  admittedAtCanonicalHead := fun receipt =>
    GoalSelected (campaignRun receipt.1) receipt.2
  grounded := by
    intro epoch lineage selected
    exact ⟨(epoch, lineage), rfl, rfl, selected⟩

def campaignRunSchedulingContract : SchedulingContract campaignRun where
  lawfulCarry := campaign_run_is_lawfully_carried
  selectionBinding := campaignRunSelectionBinding
  preemptionPolicy := .enabled campaignRunDiscipline

theorem campaign_run_weak_fair_from_scheduling_contract :
    WeakFairness campaignRun :=
  scheduling_contract_implies_weak_fairness
    campaignRunSchedulingContract

/-!
Dropping a mandatory incumbent makes a superficial continuity premise vacuous.
The load-bearing `lawfulCarry` field prevents that mutant from certifying
campaign isolation.
-/
def droppedCampaignGoals : Nat → LineageQ → Option GoalLocalState
  | 0, .target => some (campaignState 0)
  | 0, _ => none
  | _ + 1, .overtaker => some (campaignState 0)
  | _ + 1, _ => none

def droppedUnselectedCampaignRun : Nat → EpochFrame LineageQ
  | 0 =>
      { goals := droppedCampaignGoals 0
        selectedLineage := none }
  | epoch + 1 =>
      { goals := droppedCampaignGoals (epoch + 1)
        selectedLineage := some .overtaker }

theorem dropped_unselected_campaign_is_not_lawful :
    ¬ LawfulLineageRun droppedUnselectedCampaignRun := by
  intro lawful
  obtain ⟨newState, nextPresent, mandatory, ageMonotone, waiting⟩ :=
    (lawful 0).2 .target (campaignState 0) rfl rfl
  simp
    [GoalAt, droppedUnselectedCampaignRun, droppedCampaignGoals]
    at nextPresent

theorem dropped_unselected_campaign_has_no_isolation_certificate :
    ¬ Nonempty (CampaignIsolation droppedUnselectedCampaignRun) := by
  intro inhabited
  rcases inhabited with ⟨certificate⟩
  exact
    dropped_unselected_campaign_is_not_lawful
      certificate.lawfulCarry

/-! ## A nominal selection without legal Goal state cannot enter a contract -/

def illegalSelectionRun (_epoch : Nat) : EpochFrame LineageQ where
  goals := fun _ => none
  selectedLineage := some .ghost

theorem illegal_selection_run_is_not_lawful :
    ¬ LawfulLineageRun illegalSelectionRun := by
  intro lawful
  obtain ⟨state, present, mandatory, ready⟩ :=
    (lawful 0).1 .ghost rfl
  simp [GoalAt, illegalSelectionRun] at present

theorem illegal_selection_run_has_no_scheduling_contract :
    ¬ Nonempty (SchedulingContract illegalSelectionRun) := by
  intro inhabited
  rcases inhabited with ⟨contract⟩
  exact illegal_selection_run_is_not_lawful contract.lawfulCarry

/-! ## Every discipline is load-bearing on the starvation run -/

theorem starvation_has_no_quota :
    ∀ window, ¬ QuotaDiscipline starvationRun window := by
  intro window quota
  obtain ⟨offset, insideWindow, selected⟩ :=
    quota.2 .target 0 starvation_run_continuously_ready
  cases selected

theorem starvation_has_no_aging_policy :
    ∀ threshold, ¬ AgingDiscipline starvationRun threshold := by
  intro threshold aging
  have selected :=
    aging .target threshold (targetState threshold)
      rfl rfl rfl (Nat.le_refl threshold)
  cases selected

theorem starvation_has_no_campaign_isolation :
    ¬ Nonempty (CampaignIsolation starvationRun) := by
  intro inhabited
  rcases inhabited with ⟨isolated⟩
  have member :=
    isolated.universeSealed .target 0
      (starvation_run_continuously_ready 0 (Nat.le_refl 0))
  obtain ⟨epoch, afterStart, selected⟩ :=
    isolated.service .target member 0
      starvation_run_continuously_ready
  cases selected

theorem starvation_has_no_preemption_discipline :
    ¬ Nonempty (PreemptionDiscipline starvationRun) := by
  intro inhabited
  rcases inhabited with ⟨discipline⟩
  exact
    lawful_conservation_does_not_imply_liveness
      (preemption_discipline_implies_weak_fairness discipline)

theorem priority_preemption_without_discipline_has_no_contract :
    ¬ Nonempty (SchedulingContract starvationRun) := by
  intro inhabited
  rcases inhabited with ⟨contract⟩
  exact
    lawful_conservation_does_not_imply_liveness
      (scheduling_contract_implies_weak_fairness contract)

/-! The inner RCC normalizer uses the current four-branch executable core. -/

def innerCountdownExec : Residua.RCC.Exec where
  State := Nat
  measure := id
  closed := fun n => n = 0
  closedDecidable := fun n => inferInstance
  stepOpen := fun n h =>
    .advanced (Nat.pred n) (Nat.pred_lt h)

theorem inner_countdown_normalize_succ (n : Nat) :
    Residua.RCC.normalize innerCountdownExec (Nat.succ n) =
      Residua.RCC.normalize innerCountdownExec n := by
  rw [Residua.RCC.normalize]
  simp [innerCountdownExec, Residua.RCC.OpenStepResult.target?]

theorem inner_countdown_closes :
    (Residua.RCC.normalize innerCountdownExec (3 : Nat)).state? =
      some (0 : Nat) := by
  rw [show (3 : Nat) = Nat.succ 2 by rfl,
    inner_countdown_normalize_succ 2]
  rw [show (2 : Nat) = Nat.succ 1 by rfl,
    inner_countdown_normalize_succ 1]
  rw [show (1 : Nat) = Nat.succ 0 by rfl,
    inner_countdown_normalize_succ 0]
  exact Residua.RCC.normalize_state_of_closed innerCountdownExec (0 : Nat) rfl

theorem every_epoch_inner_normalization_closes :
    ∀ _epoch : Nat,
      (Residua.RCC.normalize innerCountdownExec (3 : Nat)).state? =
        some (0 : Nat) := by
  intro _epoch
  exact inner_countdown_closes

theorem finite_inner_normalization_coexists_with_lineage_starvation :
    (∀ _epoch : Nat,
      (Residua.RCC.normalize innerCountdownExec (3 : Nat)).state? =
        some (0 : Nat)) ∧
      ¬ WeakFairness starvationRun :=
  ⟨every_epoch_inner_normalization_closes,
    lawful_conservation_does_not_imply_liveness⟩

end Residua.RCC.CrossEpochFairness94.Tests


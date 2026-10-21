import RCC.RCC38Target

/-! Independent proof-level checks for the RCC-38 target certificate. -/

namespace Residua.RCC.RCC38Target.Tests

open Residua.RCC.CrossEpochFairness
open Residua.RCC.CrossEpochFairness.Tests
open Residua.RCC.RCC38Target

theorem lawful_carry_can_still_starve :
    LawfulLineageRun starvationRun ∧
      ContinuouslyReadyMandatory starvationRun .target 0 ∧
      NeverSelected starvationRun .target 0 ∧
      ¬ WeakFairness starvationRun :=
  ⟨(Certificate.starvationIsLawful certificate).1,
    (Certificate.starvationIsLawful certificate).2.1,
    (Certificate.starvationIsLawful certificate).2.2,
    Certificate.conservationDoesNotImplyLiveness certificate⟩

theorem age_reset_is_not_lawful_migration :
    (∀ epoch,
      CarryConservesGoal (ageResetRun epoch) (ageResetRun (epoch + 1))) ∧
      ¬ LawfulLineageRun ageResetRun :=
  Certificate.ageResetRejected certificate

theorem weak_fairness_is_explicit_liveness_input :
    WeakFairness fairRun ∧ EventuallySelected fairRun .target 0 :=
  Certificate.explicitFairnessProducesSelection certificate

theorem lawful_ready_carry_advances_age :
    ∀ {current next : EpochFrame LineageQ},
      LawfulCarry current next →
      current.goal.mandatory = true →
      current.goal.ready = true →
      ¬ GoalSelected current →
      current.goal.carryAge < next.goal.carryAge :=
  Certificate.strictAgeProgress certificate

theorem overtaking_does_not_count_as_fairness :
    (∀ epoch, (starvationRun epoch).selectedLineage = some .overtaker) ∧
      ¬ WeakFairness starvationRun :=
  Certificate.overtakingIsNotFair certificate

#print axioms lawful_carry_can_still_starve
#print axioms age_reset_is_not_lawful_migration
#print axioms weak_fairness_is_explicit_liveness_input
#print axioms lawful_ready_carry_advances_age
#print axioms overtaking_does_not_count_as_fairness

end Residua.RCC.RCC38Target.Tests

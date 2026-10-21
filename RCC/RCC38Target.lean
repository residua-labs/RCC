import RCCTests.CrossEpochFairness

/-!
# RCC-38 target package

This target packages the standalone cross-epoch fairness fixture.  It records
the safety/liveness separation explicitly: lawful migration conserves and
ages a ready mandatory lineage, but only an explicit weak-fairness premise
provides eventual selection.  The starvation run is a deliberate negative
control, not a closure claim.

The target does not claim scheduler fairness from conservation, finite
normalizer termination, or any concrete runtime scheduler implementation.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC38Target

open Residua.RCC.CrossEpochFairness
open Residua.RCC.CrossEpochFairness.Tests

structure Certificate : Prop where
  starvationIsLawful :
    LawfulLineageRun starvationRun ∧
      ContinuouslyReadyMandatory starvationRun .target 0 ∧
      NeverSelected starvationRun .target 0
  conservationDoesNotImplyLiveness :
    ¬ WeakFairness starvationRun
  ageResetRejected :
    (∀ epoch,
      CarryConservesGoal (ageResetRun epoch) (ageResetRun (epoch + 1))) ∧
      ¬ LawfulLineageRun ageResetRun
  overtakingIsNotFair :
    (∀ epoch, (starvationRun epoch).selectedLineage = some .overtaker) ∧
      ¬ WeakFairness starvationRun
  explicitFairnessProducesSelection :
    WeakFairness fairRun ∧
      EventuallySelected fairRun .target 0
  strictAgeProgress :
    ∀ {current next : EpochFrame LineageQ},
      LawfulCarry current next →
      current.goal.mandatory = true →
      current.goal.ready = true →
      ¬ GoalSelected current →
      current.goal.carryAge < next.goal.carryAge

def certificate : Certificate where
  starvationIsLawful :=
    ⟨starvation_run_is_lawfully_carried,
      starvation_run_continuously_ready,
      starvation_run_never_selects_target⟩
  conservationDoesNotImplyLiveness := lawful_carry_does_not_imply_liveness
  ageResetRejected :=
    ⟨age_reset_preserves_only_conservation, migration_age_reset_is_rejected⟩
  overtakingIsNotFair :=
    ⟨unbounded_overtaking_selects_other_work,
      unbounded_overtaking_is_not_weak_fair⟩
  explicitFairnessProducesSelection :=
    ⟨fair_run_is_weak_fair, weak_fairness_produces_eventual_selection⟩
  strictAgeProgress := lawful_ready_carry_strictly_increases_age

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC38Target

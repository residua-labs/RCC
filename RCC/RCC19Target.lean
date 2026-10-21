import RCC.GoalAdequacy

/-! RCC-19 candidate: intent/goal non-vacuity under an explicit policy. -/

namespace Residua.RCC.RCC19Target

open Residua.RCC

structure Certificate where
  mandatoryNonempty :
    ∀ (intent : IntentProfile.{0, 0, 0}),
      intent.policy = .requireLoadBearing →
      ClosureAdequate intent →
      intent.mandatoryGoals ≠ []
  mandatoryLoadBearing :
    ∀ (intent : IntentProfile.{0, 0, 0}),
      intent.policy = .requireLoadBearing →
      ClosureAdequate intent →
      HasLoadBearingGoal intent intent.mandatoryGoals
  criticalLoadBearing :
    ∀ (intent : IntentProfile.{0, 0, 0}),
      intent.policy = .requireLoadBearing →
      ClosureAdequate intent →
      HasLoadBearingGoal intent intent.criticalGoals
  headline :
    ∀ (intent : IntentProfile.{0, 0, 0}),
      intent.policy = .requireLoadBearing →
      ClosureAdequate intent →
      intent.mandatoryGoals ≠ [] ∧
        HasLoadBearingGoal intent intent.mandatoryGoals ∧
        HasLoadBearingGoal intent intent.criticalGoals

def certificate : Certificate where
  mandatoryNonempty := fun intent hpolicy hclosure =>
    intent_adequate_requires_nonempty_mandatory intent hpolicy hclosure.1
  mandatoryLoadBearing := fun intent hpolicy hclosure =>
    intent_adequate_requires_load_bearing_mandatory intent hpolicy hclosure.1
  criticalLoadBearing := fun _ _ hclosure => hclosure.2
  headline := fun intent hpolicy hclosure =>
    rcc19_intent_goal_nonvacuity intent hpolicy hclosure

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC19Target

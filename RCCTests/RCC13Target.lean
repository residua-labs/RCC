import RCC.RCC13Target

namespace Residua.RCC.RCC13Target.Tests

open Residua.RCC
open Residua.RCC.RCC13Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

/-- A two-Goal/two-WorkItem fixture, so the target-sensitive mutant is nonconstant. -/
def boolSystem : GoalWorkSystem where
  Goal := Bool
  WorkItem := Bool
  workDecidableEq := inferInstance
  target := id

instance boolSystemGoalDecidableEq : DecidableEq boolSystem.Goal := by
  change DecidableEq Bool
  infer_instance

def boolSnapshot : GoalWorkSnapshot boolSystem where
  goalPresent
    | false => true
    | true => false
  goalStatus
    | false => .open
    | true => .satisfied
  workStatus := fun _ => .active

/-- The real implementation is admitted on the same finite fixture. -/
theorem bool_real_transition_is_admitted :
    assessWorkTransition boolSystem boolSnapshot false .invalidate
        (applyWorkAction boolSystem boolSnapshot false .invalidate) = .admitted :=
  certificate.appliedTransitionAdmitted boolSystem boolSnapshot false .invalidate

/-- The mutant is a near miss: it still gives the WorkItem the requested status. -/
theorem bool_mutant_still_applies_disposition :
    (applyErasingTargetMutant boolSystem boolSnapshot false .invalidate).workStatus false =
      .invalid :=
  certificate.mutantStillAppliesDisposition boolSystem boolSnapshot false .invalidate

/-- The same assessor rejects that near miss for erasing the open target Goal. -/
theorem bool_erasing_mutant_is_refused :
    assessWorkTransition boolSystem boolSnapshot false .invalidate
        (applyErasingTargetMutant boolSystem boolSnapshot false .invalidate) =
      .refuse .goalPresenceChanged :=
  certificate.mutantGoalPresenceRefused boolSystem boolSnapshot false .invalidate rfl

#print axioms bool_real_transition_is_admitted
#print axioms bool_mutant_still_applies_disposition
#print axioms bool_erasing_mutant_is_refused

end Residua.RCC.RCC13Target.Tests

import RCCTests.ActuationBinding

/-! RCC-15 candidate: formal artifacts do not substitute for observed actuation. -/

namespace Residua.RCC.RCC15Target

open Residua.RCC.ActuationBinding
open Residua.RCC.ActuationBinding.Tests

structure Certificate where
  gradeOrderExact :
    ClosureGrade.Precedes .specified .proved ∧
      ClosureGrade.Precedes .proved .built ∧
      ClosureGrade.Precedes .built .admitted ∧
      ClosureGrade.Precedes .admitted .activated ∧
      ClosureGrade.Precedes .activated .observedConformant ∧
      ClosureGrade.Precedes .observedConformant .rollbackSettled ∧
      ¬ ClosureGrade.Precedes .rollbackSettled .observedConformant
  liveClosureHasActuationAndObservation :
    Activated demoSystem .live .production ∧
      ObservedConformant demoSystem .live .production
  artifactAndGreenDoNotClose :
    ArtifactClosed shadowPathSystem .live ∧
      ¬ LiveIntentClosed shadowPathSystem .live .production
  differentObservationRefused :
    ¬ LiveIntentClosed mismatchedObservationSystem .live .production
  activeOldAuthorityRefused :
    ¬ LiveIntentClosed oldAuthorityActiveSystem .live .production
  decoyRetirementRefused :
    decoyOnlyRetiredSystem.oldAuthorityRetired .decoyWriter .production ∧
      ¬ LiveIntentClosed decoyOnlyRetiredSystem .live .production
  unsealedInventoryRefused :
    ¬ LiveIntentClosed unsealedEmptyAuthorityInventorySystem .live .production
  unsettledRollbackRefused :
    ¬ LiveIntentClosed rollbackUnsettledSystem .live .production

def certificate : Certificate where
  gradeOrderExact := closure_grade_order_is_exact
  liveClosureHasActuationAndObservation :=
    headline_live_closure_implies_actuation_and_observation
  artifactAndGreenDoNotClose := merged_code_and_ci_do_not_construct_live_closure
  differentObservationRefused := different_artifact_observation_refuses_live_closure
  activeOldAuthorityRefused := active_old_authority_refuses_live_closure
  decoyRetirementRefused := decoy_authority_retirement_refuses_live_closure
  unsealedInventoryRefused := unsealed_empty_authority_inventory_refuses_live_closure
  unsettledRollbackRefused := unsettled_rollback_refuses_live_closure

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC15Target

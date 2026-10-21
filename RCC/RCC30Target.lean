import RCC.ActuationBinding
import RCCTests.ActuationBinding

/-!
# RCC-30 target package

This candidate packages the artifact-to-live actuation ladder.  A merged or
green artifact alone is not live closure: the certificate must bind the exact
target and observed artifact, retire every declared prior authority, and settle
rollback.  External deployment liveness and observation authenticity remain
explicit nonclaims.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC30Target

open Residua.RCC.ActuationBinding
open Residua.RCC.ActuationBinding.Tests

universe u v w x y z

theorem generic_live_closure_implies_activation_and_observation
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    Activated system artifact target ∧
      ObservedConformant system artifact target :=
  live_intent_closed_implies_activated_and_observed_conformant closed

theorem generic_live_closure_retires_declared_authority
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target)
    (authority : system.Authority)
    (prior : system.priorLiveAuthority authority artifact target) :
    system.oldAuthorityRetired authority target :=
  live_intent_closed_retires_every_declared_prior_authority
    closed authority prior

structure ConcreteWitness : Prop where
  gradeOrder :
    ClosureGrade.Precedes .specified .proved ∧
      ClosureGrade.Precedes .proved .built ∧
      ClosureGrade.Precedes .built .admitted ∧
      ClosureGrade.Precedes .admitted .activated ∧
      ClosureGrade.Precedes .activated .observedConformant ∧
      ClosureGrade.Precedes .observedConformant .rollbackSettled ∧
      ¬ ClosureGrade.Precedes .rollbackSettled .observedConformant
  liveClosure : LiveIntentClosed demoSystem .live .production
  activationAndObservation :
    Activated demoSystem .live .production ∧
      ObservedConformant demoSystem .live .production
  priorAuthorityRetired :
    demoSystem.oldAuthorityRetired .legacyWriter .production
  externalLivenessNonclaim :
    LiveIntentClosed demoSystem .live .production ∧
      ¬ demoSystem.deploymentEventuallyOccurs .live .production
  observationAuthenticityNonclaim :
    LiveIntentClosed demoSystem .live .production ∧
      ¬ demoSystem.observationAuthentic .liveArtifact

structure MutantRefusal : Prop where
  shadowPathNotLive :
    ArtifactClosed shadowPathSystem .live ∧
      ¬ LiveIntentClosed shadowPathSystem .live .production
  differentObservationRefused :
    ¬ LiveIntentClosed mismatchedObservationSystem .live .production
  activeOldAuthorityRefused :
    ¬ LiveIntentClosed oldAuthorityActiveSystem .live .production
  decoyOnlyRetirementRefused :
    decoyOnlyRetiredSystem.oldAuthorityRetired .decoyWriter .production ∧
      ¬ LiveIntentClosed decoyOnlyRetiredSystem .live .production
  emptyInventoryRefused :
    ¬ LiveIntentClosed
      unsealedEmptyAuthorityInventorySystem .live .production
  unsettledRollbackRefused :
    ¬ LiveIntentClosed rollbackUnsettledSystem .live .production

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { gradeOrder := closure_grade_order_is_exact
      liveClosure := liveClosed
      activationAndObservation :=
        headline_live_closure_implies_actuation_and_observation
      priorAuthorityRetired := by
        exact live_intent_closed_retires_every_declared_prior_authority
          liveClosed .legacyWriter rfl
      externalLivenessNonclaim := live_closure_does_not_claim_deployment_liveness
      observationAuthenticityNonclaim :=
        live_closure_does_not_claim_observation_authenticity }
  mutants :=
    { shadowPathNotLive := merged_code_and_ci_do_not_construct_live_closure
      differentObservationRefused := different_artifact_observation_refuses_live_closure
      activeOldAuthorityRefused := active_old_authority_refuses_live_closure
      decoyOnlyRetirementRefused := decoy_authority_retirement_refuses_live_closure
      emptyInventoryRefused :=
        unsealed_empty_authority_inventory_refuses_live_closure
      unsettledRollbackRefused := unsettled_rollback_refuses_live_closure }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC30Target


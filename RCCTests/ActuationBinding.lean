import RCC.ActuationBinding

/-!
# RCC-30 Actuation-Binding Witnesses

The positive witness reaches live closure only through the complete actuation
ladder.  Six countermodels pin the gaps that artifact-only closure must not
hide: a shadow path, an observation of different bytes, an active old
authority, retirement of an irrelevant decoy authority, an unsealed empty
authority inventory, and an unsettled rollback path.
-/

namespace Residua.RCC.ActuationBinding.Tests

open Residua.RCC.ActuationBinding

inductive Artifact
  | live
  | shadow
  deriving DecidableEq, Repr

inductive Target
  | production
  deriving DecidableEq, Repr

inductive ActivationEvent
  | liveCutover
  | shadowDeploy
  deriving DecidableEq, Repr

inductive Observation
  | liveArtifact
  | shadowArtifact
  deriving DecidableEq, Repr

inductive Authority
  | legacyWriter
  | decoyWriter
  deriving DecidableEq, Repr

inductive Rollback
  | productionPlan
  deriving DecidableEq, Repr

def demoSystem : ActuationSystem where
  Artifact := Artifact
  DeploymentTarget := Target
  ActivationEvent := ActivationEvent
  LiveObservation := Observation
  Authority := Authority
  Rollback := Rollback
  specified := fun _ => True
  proved := fun _ => True
  built := fun _ => True
  codeMerged := fun _ => True
  ciGreen := fun _ => True
  artifactAdmitted := fun _ => True
  deploymentTargetBound := fun _ _ => True
  activationEventAdmitted := fun _ => True
  activationArtifact
    | .liveCutover => .live
    | .shadowDeploy => .shadow
  activationTarget := fun _ => .production
  liveObservationAdmitted := fun _ => True
  observedArtifact
    | .liveArtifact => .live
    | .shadowArtifact => .shadow
  observedTarget := fun _ => .production
  priorLiveAuthority := fun authority _ _ => authority = .legacyWriter
  priorAuthorityInventoryAdequate := fun _ _ => True
  oldAuthorityRetired := fun _ _ => True
  rollbackSettled := fun _ _ _ => True
  deploymentEventuallyOccurs := fun _ _ => False
  observationAuthentic := fun _ => False

theorem closure_grade_order_is_exact :
    ClosureGrade.Precedes .specified .proved ∧
      ClosureGrade.Precedes .proved .built ∧
      ClosureGrade.Precedes .built .admitted ∧
      ClosureGrade.Precedes .admitted .activated ∧
      ClosureGrade.Precedes .activated .observedConformant ∧
      ClosureGrade.Precedes .observedConformant .rollbackSettled ∧
      ¬ ClosureGrade.Precedes .rollbackSettled .observedConformant := by
  decide

def liveSpecified : Specified demoSystem .live :=
  ⟨trivial⟩

def liveProved : Proved demoSystem .live where
  toSpecified := liveSpecified
  proofAccepted := trivial

def liveBuilt : Built demoSystem .live where
  toProved := liveProved
  buildAvailable := trivial

def liveAdmitted : Admitted demoSystem .live where
  toBuilt := liveBuilt
  admissionAccepted := trivial

def liveActivated : Activated demoSystem .live .production where
  toAdmitted := liveAdmitted
  targetBound := trivial
  activationEvidence := ⟨.liveCutover, trivial, rfl, rfl⟩

def liveObserved : ObservedConformant demoSystem .live .production where
  toActivated := liveActivated
  observationEvidence := ⟨.liveArtifact, trivial, rfl, rfl⟩

def liveClosed : LiveIntentClosed demoSystem .live .production where
  toObservedConformant := liveObserved
  inventoryAdequate := trivial
  authorityRetirement := fun _ _ => trivial
  rollbackSettlement := ⟨.productionPlan, trivial⟩

theorem headline_live_closure_implies_actuation_and_observation :
    Activated demoSystem .live .production ∧
      ObservedConformant demoSystem .live .production :=
  live_intent_closed_implies_activated_and_observed_conformant liveClosed

/-!
The live certificate deliberately does not entail either external-world claim.
Those propositions remain explicit assumptions outside RCC-30.
-/
theorem live_closure_does_not_claim_deployment_liveness :
    LiveIntentClosed demoSystem .live .production ∧
      ¬ demoSystem.deploymentEventuallyOccurs .live .production :=
  ⟨liveClosed, fun impossible => impossible⟩

theorem live_closure_does_not_claim_observation_authenticity :
    LiveIntentClosed demoSystem .live .production ∧
      ¬ demoSystem.observationAuthentic .liveArtifact :=
  ⟨liveClosed, fun impossible => impossible⟩

/-! ## Countermodel 1: merged, green, and admitted, but only a shadow path exists -/

def shadowPathSystem : ActuationSystem :=
  { demoSystem with
    activationArtifact := fun _ => .shadow }

def shadowPathSpecified : Specified shadowPathSystem .live :=
  ⟨trivial⟩

def shadowPathProved : Proved shadowPathSystem .live where
  toSpecified := shadowPathSpecified
  proofAccepted := trivial

def shadowPathBuilt : Built shadowPathSystem .live where
  toProved := shadowPathProved
  buildAvailable := trivial

def shadowPathAdmitted : Admitted shadowPathSystem .live where
  toBuilt := shadowPathBuilt
  admissionAccepted := trivial

def shadowPathArtifactClosed : ArtifactClosed shadowPathSystem .live where
  admittedArtifact := shadowPathAdmitted
  codeMerged := trivial
  ciGreen := trivial

theorem merged_code_and_ci_do_not_construct_live_closure :
    ArtifactClosed shadowPathSystem .live ∧
      ¬ LiveIntentClosed shadowPathSystem .live .production := by
  constructor
  · exact shadowPathArtifactClosed
  · intro closed
    obtain ⟨activation, _, exactArtifact, _⟩ :=
      closed.toObservedConformant.toActivated.activationEvidence
    cases activation <;>
      change Artifact.shadow = Artifact.live at exactArtifact <;>
      cases exactArtifact

/-! ## Countermodel 2: the live observation names different artifact bytes -/

def mismatchedObservationSystem : ActuationSystem :=
  { demoSystem with
    observedArtifact := fun _ => .shadow }

theorem different_artifact_observation_refuses_live_closure :
    ¬ LiveIntentClosed mismatchedObservationSystem .live .production := by
  intro closed
  obtain ⟨observation, _, exactArtifact, _⟩ :=
    closed.toObservedConformant.observationEvidence
  cases observation <;>
    change Artifact.shadow = Artifact.live at exactArtifact <;>
    cases exactArtifact

/-! ## Countermodel 3: the legacy authority is still active -/

def oldAuthorityActiveSystem : ActuationSystem :=
  { demoSystem with
    oldAuthorityRetired := fun _ _ => False }

theorem active_old_authority_refuses_live_closure :
    ¬ LiveIntentClosed oldAuthorityActiveSystem .live .production := by
  intro closed
  have retired := closed.authorityRetirement .legacyWriter rfl
  exact retired

/-! ## Countermodel 4: retiring only an irrelevant authority is insufficient -/

def decoyOnlyRetiredSystem : ActuationSystem :=
  { demoSystem with
    oldAuthorityRetired := fun authority _ => authority = .decoyWriter }

theorem decoy_authority_retirement_refuses_live_closure :
    decoyOnlyRetiredSystem.oldAuthorityRetired .decoyWriter .production ∧
      ¬ LiveIntentClosed decoyOnlyRetiredSystem .live .production := by
  constructor
  · rfl
  · intro closed
    have retiredLegacy := closed.authorityRetirement .legacyWriter rfl
    change Authority.legacyWriter = Authority.decoyWriter at retiredLegacy
    cases retiredLegacy

/-! ## Countermodel 5: an unsealed empty prior-authority inventory is insufficient -/

def unsealedEmptyAuthorityInventorySystem : ActuationSystem :=
  { demoSystem with
    priorLiveAuthority := fun _ _ _ => False
    priorAuthorityInventoryAdequate := fun _ _ => False }

theorem unsealed_empty_authority_inventory_refuses_live_closure :
    ¬ LiveIntentClosed
      unsealedEmptyAuthorityInventorySystem .live .production := by
  intro closed
  exact closed.inventoryAdequate

/-! ## Countermodel 6: the rollback path has not settled -/

def rollbackUnsettledSystem : ActuationSystem :=
  { demoSystem with
    rollbackSettled := fun _ _ _ => False }

theorem unsettled_rollback_refuses_live_closure :
    ¬ LiveIntentClosed rollbackUnsettledSystem .live .production := by
  intro closed
  obtain ⟨_, settled⟩ := closed.rollbackSettlement
  exact settled

#print axioms closure_grade_order_is_exact
#print axioms live_intent_closed_implies_activated_and_observed_conformant
#print axioms live_intent_closed_implies_prior_authority_inventory_adequate
#print axioms live_intent_closed_retires_every_declared_prior_authority
#print axioms headline_live_closure_implies_actuation_and_observation
#print axioms live_closure_does_not_claim_deployment_liveness
#print axioms live_closure_does_not_claim_observation_authenticity
#print axioms merged_code_and_ci_do_not_construct_live_closure
#print axioms different_artifact_observation_refuses_live_closure
#print axioms active_old_authority_refuses_live_closure
#print axioms decoy_authority_retirement_refuses_live_closure
#print axioms unsealed_empty_authority_inventory_refuses_live_closure
#print axioms unsettled_rollback_refuses_live_closure

end Residua.RCC.ActuationBinding.Tests


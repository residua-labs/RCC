import RCC.ActuationSoundness

/-!
# WI-5 Actuation soundness tests

The positive fixture applies one declared delta to one world.  The mutants pin
the five load-bearing bindings: actuator, runtime, semantic effect, occurrence,
and the sealed snapshot head.  A final mutant supplies artifact-only closure but
no activation, demonstrating that candidate/proof/merge evidence cannot imply
live actuation.
-/

namespace Residua.RCC.ActuationSoundnessTests

open ActuationBinding EffectSettlement ActuationSoundness

inductive Artifact where
  | release
  | shadow
  deriving DecidableEq

inductive Target where
  | production
  deriving DecidableEq

inductive Activation where
  | cutover
  deriving DecidableEq

inductive Observation where
  | live
  deriving DecidableEq

inductive Authority where
  | writer
  | decoy
  deriving DecidableEq

inductive Rollback where
  | ready
  deriving DecidableEq

def binding : ActuationSystem where
  Artifact := Artifact
  DeploymentTarget := Target
  ActivationEvent := Activation
  LiveObservation := Observation
  Authority := Authority
  Rollback := Rollback
  specified := fun artifact => artifact = .release
  proved := fun artifact => artifact = .release
  built := fun artifact => artifact = .release
  codeMerged := fun artifact => artifact = .release
  ciGreen := fun artifact => artifact = .release
  artifactAdmitted := fun artifact => artifact = .release
  deploymentTargetBound := fun artifact target =>
    artifact = .release ∧ target = .production
  activationEventAdmitted := fun activation => activation = .cutover
  activationArtifact := fun _ => .release
  activationTarget := fun _ => .production
  liveObservationAdmitted := fun observation => observation = .live
  observedArtifact := fun _ => .release
  observedTarget := fun _ => .production
  priorLiveAuthority := fun authority artifact target =>
    authority = .decoy ∧ artifact = .release ∧ target = .production
  priorAuthorityInventoryAdequate := fun artifact target =>
    artifact = .release ∧ target = .production
  oldAuthorityRetired := fun authority target =>
    authority = .decoy ∧ target = .production
  rollbackSettled := fun rollback artifact target =>
    rollback = .ready ∧ artifact = .release ∧ target = .production
  deploymentEventuallyOccurs := fun _ _ => True
  observationAuthentic := fun _ => True

def admittedRelease : Admitted binding .release where
  toBuilt := {
    toProved := {
      toSpecified := ⟨rfl⟩
      proofAccepted := rfl
    }
    buildAvailable := rfl
  }
  admissionAccepted := rfl

def activatedRelease : Activated binding .release .production where
  toAdmitted := admittedRelease
  targetBound := ⟨rfl, rfl⟩
  activationEvidence := ⟨.cutover, rfl, rfl, rfl⟩

def artifactClosedRelease : ArtifactClosed binding .release where
  admittedArtifact := admittedRelease
  codeMerged := rfl
  ciGreen := rfl

inductive Actuator where
  | primary
  | wrong
  deriving DecidableEq

inductive Runtime where
  | production
  | shadow
  deriving DecidableEq

def AuthorityAllowsAt
    (requiredHead : Nat)
    (snapshot : EffectSnapshot Nat Nat Nat Nat Nat Nat)
    (preWorld : Nat)
    (authority : Authority) (artifact : Artifact) (target : Target)
    (actuator : Actuator) : Prop :=
  snapshot.epoch = 1 ∧ snapshot.head = requiredHead ∧ preWorld = 100 ∧
    authority = .writer ∧ artifact = .release ∧
    target = .production ∧ actuator = .primary

instance authorityAllowsDecidable
    (requiredHead : Nat)
    (snapshot : EffectSnapshot Nat Nat Nat Nat Nat Nat)
    (preWorld : Nat)
    (authority : Authority) (artifact : Artifact) (target : Target)
    (actuator : Actuator) :
    Decidable
      (AuthorityAllowsAt
        requiredHead snapshot preWorld authority artifact target actuator) := by
  unfold AuthorityAllowsAt
  infer_instance

def RuntimeRealizes
    (runtime : Runtime) (artifact : Artifact) (target : Target) : Prop :=
  runtime = .production ∧ artifact = .release ∧ target = .production

instance runtimeRealizesDecidable
    (runtime : Runtime) (artifact : Artifact) (target : Target) :
    Decidable (RuntimeRealizes runtime artifact target) := by
  unfold RuntimeRealizes
  infer_instance

def DeclaresEffect
    (artifact : Artifact) (target : Target)
    (external : ExternalEffect Nat Nat Nat) (effect : Nat) : Prop :=
  artifact = .release ∧ target = .production ∧
    external.occurrence = 7 ∧ external.expectedParent = 10 ∧
    external.effectSlot = 3 ∧ effect = 5

instance declaresEffectDecidable
    (artifact : Artifact) (target : Target)
    (external : ExternalEffect Nat Nat Nat) (effect : Nat) :
    Decidable (DeclaresEffect artifact target external effect) := by
  unfold DeclaresEffect
  infer_instance

abbrev makeWorldSystem (requiredAuthorityHead : Nat) :
    WorldActuationSystem binding Nat Nat Nat Nat Nat Nat where
  World := Nat
  Runtime := Runtime
  Actuator := Actuator
  Effect := Nat
  AuthorityAllows := AuthorityAllowsAt requiredAuthorityHead
  RuntimeRealizes := RuntimeRealizes
  DeclaresEffect := DeclaresEffect
  verifyAuthority := fun snapshot preWorld authority artifact target actuator =>
    decide
      (AuthorityAllowsAt
        requiredAuthorityHead snapshot preWorld
        authority artifact target actuator)
  verifyRuntime := fun runtime artifact target =>
    decide (RuntimeRealizes runtime artifact target)
  verifyEffect := fun artifact target external effect =>
    decide (DeclaresEffect artifact target external effect)
  authoritySound := by
    intro snapshot preWorld authority artifact target actuator accepted
    exact of_decide_eq_true accepted
  runtimeSound := by
    intro runtime artifact target accepted
    exact of_decide_eq_true accepted
  effectSound := by
    intro artifact target external effect accepted
    exact of_decide_eq_true accepted
  apply := fun _ _ pre effect => pre + effect
  EffectRelation := fun pre effect post => post = pre + effect
  applySound := by
    intro _snapshot _authority _artifact _target _external _actuator _runtime
      _pre _effect _authorityAccepted _runtimeAccepted _effectAccepted
    rfl

abbrev worldSystem :
    WorldActuationSystem binding Nat Nat Nat Nat Nat Nat :=
  makeWorldSystem 10

/--
This actuator has an otherwise valid authority packet, but only for the
successor head 11.  It must not authorize the sealed pre-effect snapshot at 10.
-/
abbrev postHeadWorldSystem :
    WorldActuationSystem binding Nat Nat Nat Nat Nat Nat :=
  makeWorldSystem 11

def declaredExternal : ExternalEffect Nat Nat Nat where
  occurrence := 7
  expectedParent := 10
  effectSlot := 3

def snapshot : EffectSnapshot Nat Nat Nat Nat Nat Nat where
  epoch := 1
  head := 10
  currentGeneration := fun _ => 4
  policyTerminalFailure := fun _ => False
  externalEffects := [declaredExternal]
  observe := fun _ => none

def context : DeclaredEffectContext snapshot where
  effect := declaredExternal
  declared := by simp [snapshot]

def goodAttempt : ActuationAttempt worldSystem where
  claimedHead := 10
  claimedOccurrence := 7
  authority := .writer
  actuator := .primary
  runtime := .production
  effect := 5
  preWorld := 100

def wrongActuator : ActuationAttempt worldSystem :=
  { goodAttempt with actuator := .wrong }

def wrongRuntime : ActuationAttempt worldSystem :=
  { goodAttempt with runtime := .shadow }

def wrongEffect : ActuationAttempt worldSystem :=
  { goodAttempt with effect := 6 }

def wrongOccurrence : ActuationAttempt worldSystem :=
  { goodAttempt with claimedOccurrence := 8 }

def staleHead : ActuationAttempt worldSystem :=
  { goodAttempt with claimedHead := 11 }

def postHeadAuthorityAttempt : ActuationAttempt postHeadWorldSystem where
  claimedHead := 10
  claimedOccurrence := 7
  authority := .writer
  actuator := .primary
  runtime := .production
  effect := 5
  preWorld := 100

/-! ## Positive path -/

theorem admitted_action_produces_only_declared_effect :
    match admitActuation
        worldSystem snapshot context .release .production
        (.certified activatedRelease) goodAttempt with
    | .admitted admitted =>
        worldSystem.EffectRelation
          goodAttempt.preWorld goodAttempt.effect
          (worldSystem.apply
            goodAttempt.actuator goodAttempt.runtime
            goodAttempt.preWorld goodAttempt.effect) ∧
        admitted.activated = admitted.activated
    | .refused _ => False := by
  simp [admitActuation, goodAttempt, snapshot, context, declaredExternal,
    AuthorityAllowsAt, RuntimeRealizes, DeclaresEffect]

theorem admitted_action_changes_fixture_world_to_105 :
    worldSystem.apply
      goodAttempt.actuator goodAttempt.runtime
      goodAttempt.preWorld goodAttempt.effect = 105 := by
  rfl

/-! ## Binding mutants -/

theorem wrong_actuator_refused :
    admitActuation
      worldSystem snapshot context .release .production
      (.certified activatedRelease) wrongActuator =
        .refused .actuatorUnauthorized := by
  rfl

theorem wrong_runtime_refused :
    admitActuation
      worldSystem snapshot context .release .production
      (.certified activatedRelease) wrongRuntime =
        .refused .runtimeUnbound := by
  rfl

theorem wrong_effect_refused :
    admitActuation
      worldSystem snapshot context .release .production
      (.certified activatedRelease) wrongEffect =
        .refused .effectUndeclared := by
  rfl

theorem wrong_occurrence_refused :
    admitActuation
      worldSystem snapshot context .release .production
      (.certified activatedRelease) wrongOccurrence =
        .refused .occurrenceMismatch := by
  rfl

theorem stale_history_head_refused :
    admitActuation
      worldSystem snapshot context .release .production
      (.certified activatedRelease) staleHead =
        .refused .staleHead := by
  rfl

theorem authority_valid_only_at_post_head_refused :
    admitActuation
      postHeadWorldSystem snapshot context .release .production
      (.certified activatedRelease) postHeadAuthorityAttempt =
        .refused .actuatorUnauthorized := by
  rfl

/--
Even merged, green, admitted artifact evidence cannot replace an activation
certificate.  The argument is deliberately present but unused by the common
admission tree.
-/
theorem artifact_closure_alone_cannot_imply_live_actuation
    (_closed : ArtifactClosed binding .release) :
    admitActuation
      worldSystem snapshot context .release .production
      .absent goodAttempt =
        .refused .artifactNotActivated := by
  rfl

example :
    admitActuation
      worldSystem snapshot context .release .production
      .absent goodAttempt =
        .refused .artifactNotActivated :=
  artifact_closure_alone_cannot_imply_live_actuation artifactClosedRelease

#print axioms admitted_actuation_only_declared_effect
#print axioms admitted_actuation_binds_snapshot_head_and_occurrence
#print axioms admitted_action_produces_only_declared_effect
#print axioms wrong_actuator_refused
#print axioms wrong_runtime_refused
#print axioms wrong_effect_refused
#print axioms wrong_occurrence_refused
#print axioms stale_history_head_refused
#print axioms authority_valid_only_at_post_head_refused
#print axioms artifact_closure_alone_cannot_imply_live_actuation

end Residua.RCC.ActuationSoundnessTests

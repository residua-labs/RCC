import RCC.PostEffectFeedback
import RCCTests.ActuationSoundness

/-!
# WI-6 post-effect feedback tests

The fixture re-observes WI-5's post-world `105` from an independent audit
sensor at snapshot 11.  Mutants pin absence, actor/source independence,
freshness, occurrence, effect, post-world, and WI-1 certificate verification.
-/

namespace Residua.RCC.PostEffectFeedbackTests

open ActuationSoundness
open ObservationSoundness
open PostEffectFeedback
open ActuationSoundnessTests

inductive Observer where
  | auditor
  | actuator
  deriving DecidableEq

inductive Source where
  | sensor
  | actuator
  deriving DecidableEq

structure RawObservation where
  source : Source
  world : Nat
  occurrence : Nat
  effect : Nat
  deriving DecidableEq

structure ObservedEffect where
  occurrence : Nat
  effect : Nat
  postWorld : Nat
  deriving DecidableEq

inductive Certificate where
  | valid
  | invalid
  deriving DecidableEq

def RawRepresents
    (world : Nat) (source : Source) (raw : RawObservation) : Prop :=
  raw.world = world ∧ raw.source = source

def ObservationTrue (world : Nat) (observed : ObservedEffect) : Prop :=
  observed.postWorld = world

def ObservationCertificateAccepted
    (source : Source) (raw : RawObservation)
    (observed : ObservedEffect) (certificate : Certificate) : Prop :=
  certificate = .valid ∧ raw.source = source ∧
    observed.postWorld = raw.world ∧
    observed.occurrence = raw.occurrence ∧ observed.effect = raw.effect

instance observationCertificateAcceptedDecidable
    (source : Source) (raw : RawObservation)
    (observed : ObservedEffect) (certificate : Certificate) :
    Decidable
      (ObservationCertificateAccepted source raw observed certificate) := by
  unfold ObservationCertificateAccepted
  infer_instance

abbrev observationSystem : ObservationSystem where
  World := Nat
  SnapshotQ := Nat
  Source := Source
  Raw := RawObservation
  Observation := ObservedEffect
  Certificate := Certificate
  snapshotQDecidableEq := inferInstance
  RawRepresents := RawRepresents
  ObservationTrue := ObservationTrue
  verify := fun source raw observed certificate =>
    decide
      (ObservationCertificateAccepted source raw observed certificate)
  verifySound := by
    intro world source raw observed certificate authentic accepted
    have acceptedProp :
        ObservationCertificateAccepted source raw observed certificate :=
      of_decide_eq_true accepted
    exact acceptedProp.2.2.1.trans authentic.1

def PostSnapshotFor
    (preSnapshot : EffectSettlement.EffectSnapshot Nat Nat Nat Nat Nat Nat)
    (postSnapshot : SealedWorldSnapshot observationSystem) : Prop :=
  preSnapshot.head = 10 ∧ postSnapshot.snapshotQ = 11

instance postSnapshotForDecidable
    (preSnapshot : EffectSettlement.EffectSnapshot Nat Nat Nat Nat Nat Nat)
    (postSnapshot : SealedWorldSnapshot observationSystem) :
    Decidable (PostSnapshotFor preSnapshot postSnapshot) := by
  unfold PostSnapshotFor
  infer_instance

def IndependentObserverSource
    (actuator : Actuator) (observer : Observer) (source : Source) : Prop :=
  actuator = .primary ∧ observer = .auditor ∧ source = .sensor

instance independentObserverSourceDecidable
    (actuator : Actuator) (observer : Observer) (source : Source) :
    Decidable (IndependentObserverSource actuator observer source) := by
  unfold IndependentObserverSource
  infer_instance

def ReportsOccurrence
    (_world : Nat) (observed : ObservedEffect) (occurrence : Nat) : Prop :=
  observed.occurrence = occurrence

def ReportsEffect
    (_world : Nat) (observed : ObservedEffect) (effect : Nat) : Prop :=
  observed.effect = effect

def ReportsPostWorld
    (_world : Nat) (observed : ObservedEffect) (postWorld : Nat) : Prop :=
  observed.postWorld = postWorld

abbrev feedbackSystem :
    FeedbackSystem worldSystem observationSystem where
  Observer := Observer
  PostSnapshotFor := PostSnapshotFor
  IndependentObserverSource := IndependentObserverSource
  ReportsOccurrence := ReportsOccurrence
  ReportsEffect := ReportsEffect
  ReportsPostWorld := ReportsPostWorld
  verifyPostSnapshot := fun preSnapshot postSnapshot =>
    decide (PostSnapshotFor preSnapshot postSnapshot)
  verifyIndependence := fun actuator observer source =>
    decide (IndependentObserverSource actuator observer source)
  verifyOccurrence := fun _world observed occurrence =>
    decide (observed.occurrence = occurrence)
  verifyEffect := fun _world observed effect =>
    decide (observed.effect = effect)
  verifyPostWorld := fun _world observed postWorld =>
    decide (observed.postWorld = postWorld)
  postSnapshotSound := by
    intro preSnapshot postSnapshot accepted
    exact of_decide_eq_true accepted
  independenceSound := by
    intro actuator observer source accepted
    exact of_decide_eq_true accepted
  occurrenceSound := by
    intro _world _observed _occurrence _true accepted
    simpa [ReportsOccurrence] using of_decide_eq_true accepted
  effectSound := by
    intro _world _observed _effect _true accepted
    simpa [ReportsEffect] using of_decide_eq_true accepted
  postWorldSound := by
    intro _world _observed _postWorld _true accepted
    simpa [ReportsPostWorld] using of_decide_eq_true accepted

def admittedActuationFixture :
    AdmittedActuation
      worldSystem snapshot context .release .production goodAttempt where
  activated := activatedRelease
  snapshotHeadBound := rfl
  declaredEffectHeadBound := rfl
  occurrenceBound := rfl
  authorityAccepted := by
    simp [AuthorityAllowsAt, snapshot, goodAttempt]
  runtimeAccepted := by
    simp [RuntimeRealizes, goodAttempt]
  effectAccepted := by
    simp [DeclaresEffect, goodAttempt, context, declaredExternal]
  effectRelation := rfl

def postSnapshot : SealedWorldSnapshot observationSystem where
  snapshotQ := 11
  world := 105

def stalePreEffectSnapshot : SealedWorldSnapshot observationSystem where
  snapshotQ := 10
  world := 100

def wrongPostWorldSnapshot : SealedWorldSnapshot observationSystem where
  snapshotQ := 11
  world := 104

def goodObserved : ObservedEffect where
  occurrence := 7
  effect := 5
  postWorld := 105

def wrongOccurrenceObserved : ObservedEffect :=
  { goodObserved with occurrence := 8 }

def wrongEffectObserved : ObservedEffect :=
  { goodObserved with effect := 6 }

def wrongPostWorldObserved : ObservedEffect where
  occurrence := 7
  effect := 5
  postWorld := 104

def rawFor (source : Source) (observed : ObservedEffect) : RawObservation where
  source := source
  world := observed.postWorld
  occurrence := observed.occurrence
  effect := observed.effect

def observationAttempt
    (sealed : SealedWorldSnapshot observationSystem)
    (source : Source)
    (observed : ObservedEffect)
    (certificate : Certificate := .valid) :
    ObservationAttempt observationSystem sealed where
  claimedSnapshotQ := sealed.snapshotQ
  source := source
  raw := rawFor source observed
  observation := observed
  certificate := certificate

def captureAuthorization
    (sealed : SealedWorldSnapshot observationSystem)
    (source : Source)
    (observed : ObservedEffect)
    (certificate : Certificate)
    (worldBound : observed.postWorld = sealed.world) :
    CaptureAuthorization
      observationSystem sealed
      (observationAttempt sealed source observed certificate) :=
  .certified (by
    exact ⟨worldBound, rfl⟩)

def goodInput : ReobservationInput observationSystem postSnapshot :=
  .supplied
    (observationAttempt postSnapshot .sensor goodObserved)
    (captureAuthorization postSnapshot .sensor goodObserved .valid rfl)

def sameSourceInput : ReobservationInput observationSystem postSnapshot :=
  .supplied
    (observationAttempt postSnapshot .actuator goodObserved)
    (captureAuthorization postSnapshot .actuator goodObserved .valid rfl)

def staleInput :
    ReobservationInput observationSystem stalePreEffectSnapshot :=
  .supplied
    (observationAttempt stalePreEffectSnapshot .sensor
      { occurrence := 7, effect := 5, postWorld := 100 })
    (captureAuthorization stalePreEffectSnapshot .sensor
      { occurrence := 7, effect := 5, postWorld := 100 } .valid rfl)

def wrongOccurrenceInput :
    ReobservationInput observationSystem postSnapshot :=
  .supplied
    (observationAttempt postSnapshot .sensor wrongOccurrenceObserved)
    (captureAuthorization
      postSnapshot .sensor wrongOccurrenceObserved .valid rfl)

def wrongEffectInput :
    ReobservationInput observationSystem postSnapshot :=
  .supplied
    (observationAttempt postSnapshot .sensor wrongEffectObserved)
    (captureAuthorization postSnapshot .sensor wrongEffectObserved .valid rfl)

def wrongPostWorldInput :
    ReobservationInput observationSystem wrongPostWorldSnapshot :=
  .supplied
    (observationAttempt wrongPostWorldSnapshot .sensor wrongPostWorldObserved)
    (captureAuthorization
      wrongPostWorldSnapshot .sensor wrongPostWorldObserved .valid rfl)

def unverifiableInput :
    ReobservationInput observationSystem postSnapshot :=
  .supplied
    (observationAttempt postSnapshot .sensor goodObserved .invalid)
    (captureAuthorization postSnapshot .sensor goodObserved .invalid rfl)

/-! ## Positive closure -/

theorem independent_reobservation_closes_feedback :
    match admitFeedback
        feedbackSystem snapshot context .release .production goodAttempt
        admittedActuationFixture postSnapshot .auditor goodInput with
    | .closed closed =>
        observationSystem.ObservationTrue
            postSnapshot.world closed.reobservation.observation ∧
          feedbackSystem.IndependentObserverSource
            goodAttempt.actuator .auditor closed.reobservation.source ∧
          feedbackSystem.ReportsOccurrence
            postSnapshot.world closed.reobservation.observation
            context.effect.occurrence ∧
          feedbackSystem.ReportsEffect
            postSnapshot.world closed.reobservation.observation
            goodAttempt.effect ∧
          feedbackSystem.ReportsPostWorld
            postSnapshot.world closed.reobservation.observation
            (worldSystem.apply
              goodAttempt.actuator goodAttempt.runtime
              goodAttempt.preWorld goodAttempt.effect)
    | .refused _ => False := by
  simp [admitFeedback, admitObservation, goodInput, observationAttempt, rawFor,
    captureAuthorization, postSnapshot, goodObserved, feedbackSystem,
    PostSnapshotFor, IndependentObserverSource, ReportsOccurrence,
    ReportsEffect, ReportsPostWorld, ObservationCertificateAccepted,
    ObservationTrue, snapshot, context, declaredExternal,
    goodAttempt]

/-! ## Countermodels -/

theorem no_reobservation_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .auditor .absent =
        .refused .noReobservation := by
  rfl

theorem same_actor_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .actuator goodInput =
        .refused .observerSourceNotIndependent := by
  rfl

theorem same_actuator_source_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .auditor sameSourceInput =
        .refused .observerSourceNotIndependent := by
  rfl

theorem stale_pre_effect_observation_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture stalePreEffectSnapshot .auditor staleInput =
        .refused .stalePreEffectObservation := by
  rfl

theorem wrong_occurrence_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .auditor wrongOccurrenceInput =
        .refused .occurrenceMismatch := by
  rfl

theorem wrong_effect_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .auditor wrongEffectInput =
        .refused .effectMismatch := by
  rfl

theorem wrong_post_world_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture wrongPostWorldSnapshot .auditor
      wrongPostWorldInput =
        .refused .postWorldMismatch := by
  rfl

theorem unverifiable_observation_refused :
    admitFeedback
      feedbackSystem snapshot context .release .production goodAttempt
      admittedActuationFixture postSnapshot .auditor unverifiableInput =
        .refused (.observationRefused .certificateRefused) := by
  simp [admitFeedback, admitObservation, unverifiableInput, observationAttempt, rawFor,
    captureAuthorization, postSnapshot, goodObserved, observationSystem,
    ObservationCertificateAccepted]

#print axioms feedback_closed_contains_exact_wi5_actuation
#print axioms feedback_closed_has_independent_admitted_reobservation
#print axioms feedback_closed_binds_occurrence_effect_and_post_world
#print axioms independent_reobservation_closes_feedback
#print axioms no_reobservation_refused
#print axioms same_actor_refused
#print axioms same_actuator_source_refused
#print axioms stale_pre_effect_observation_refused
#print axioms wrong_occurrence_refused
#print axioms wrong_effect_refused
#print axioms wrong_post_world_refused
#print axioms unverifiable_observation_refused

end Residua.RCC.PostEffectFeedbackTests

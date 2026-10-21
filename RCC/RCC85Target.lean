import RCCTests.PostEffectFeedback

/-! RCC-85 candidate: independent post-effect feedback closure. -/

namespace Residua.RCC.RCC85Target

open Residua.RCC.PostEffectFeedbackTests
open Residua.RCC.PostEffectFeedback
open Residua.RCC.ActuationBinding
open Residua.RCC.ActuationSoundness
open Residua.RCC.EffectSettlement
open Residua.RCC.ObservationSoundness

def feedbackCloses := independent_reobservation_closes_feedback
def noReobservationRefused := no_reobservation_refused
def sameActorRefused := same_actor_refused
def sameSourceRefused := same_actuator_source_refused
def staleObservationRefused := stale_pre_effect_observation_refused
def wrongOccurrenceRefused := wrong_occurrence_refused
def wrongEffectRefused := wrong_effect_refused
def wrongPostWorldRefused := wrong_post_world_refused
def unverifiableObservationRefused := unverifiable_observation_refused

/-!
The generic feedback theorems are universe-polymorphic.  The admission packet
pins one concrete `Type 0` schema so the certificate has no unresolved universe
metavariables while still carrying the full bridge shape (effect, independent
re-observation, occurrence/effect/post-world binding).
-/
abbrev FeedbackBridgeClaim : Prop :=
  ∀ {binding : ActuationSystem.{0, 0, 0, 0, 0, 0}}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem.{0, 0, 0, 0, 0, 0}
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem.{0, 0, 0, 0, 0, 0}}
    {feedback : FeedbackSystem.{0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
      actuation observation}
    {effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {effectContext : DeclaredEffectContext effectSnapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {actuationAttempt : ActuationAttempt actuation}
    {admittedActuation :
      AdmittedActuation actuation effectSnapshot effectContext artifact target
        actuationAttempt}
    {postSnapshot : SealedWorldSnapshot.{0, 0, 0, 0, 0, 0} observation}
    {observer : feedback.Observer}
    (closed :
      FeedbackClosed feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer),
    actuation.EffectRelation actuationAttempt.preWorld actuationAttempt.effect
        (actuation.apply actuationAttempt.actuator actuationAttempt.runtime
          actuationAttempt.preWorld actuationAttempt.effect) ∧
      (observation.ObservationTrue postSnapshot.world
          closed.reobservation.observation ∧
        feedback.IndependentObserverSource actuationAttempt.actuator observer
          closed.reobservation.source) ∧
      (feedback.ReportsOccurrence postSnapshot.world
          closed.reobservation.observation effectContext.effect.occurrence ∧
        feedback.ReportsEffect postSnapshot.world
          closed.reobservation.observation actuationAttempt.effect ∧
        feedback.ReportsPostWorld postSnapshot.world
          closed.reobservation.observation
          (actuation.apply actuationAttempt.actuator actuationAttempt.runtime
            actuationAttempt.preWorld actuationAttempt.effect))

def feedbackBridgeSound : FeedbackBridgeClaim := by
  intro binding Epoch Head EffectSlot Generation Occurrence FailureName
    actuation observation feedback effectSnapshot effectContext artifact target
    actuationAttempt admittedActuation postSnapshot observer closed
  exact ⟨
    feedback_closed_contains_exact_wi5_actuation closed,
    ⟨feedback_closed_has_independent_admitted_reobservation closed,
      feedback_closed_binds_occurrence_effect_and_post_world closed⟩⟩

structure Certificate where
  feedbackBridgeSound : FeedbackBridgeClaim

def certificate : Certificate where
  feedbackBridgeSound := feedbackBridgeSound

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC85Target

import RCC.ActuationSoundness
import RCC.ObservationSoundness

/-!
# WI-6 — Post-effect feedback closure by independent re-observation

An admitted actuation proves only that the selected invocation realizes its
declared effect relation.  It is not evidence that the changed world was later
observed.  WI-6 adds that missing feedback edge.

The common admission tree first runs WI-1 on an independently captured
observation.  It then verifies that the observation snapshot is appropriate
after the exact WI-5 actuation, that observer and source are independent from
the actuator, and that the admitted observation names the exact effect
occurrence, effect value, and computed post-world.

`EffectSnapshot.head` remains a declared sealed-snapshot coordinate.  This
kernel does not manufacture canonical-head finality, eventual observation, or
observation completeness.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or custom assumptions.
-/

namespace Residua.RCC.PostEffectFeedback

open ActuationBinding
open EffectSettlement
open ActuationSoundness
open ObservationSoundness

/--
Executable bindings between one WI-5 actuation and one WI-1 observation.

Every accepted boolean has a soundness law.  The observation-binding laws also
consume WI-1's semantic truth proof, so a raw self-report cannot bypass
observation admission.
-/
structure FeedbackSystem
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    (actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName)
    (observation : ObservationSystem) where
  Observer : Type

  PostSnapshotFor :
    EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName →
      SealedWorldSnapshot observation → Prop
  IndependentObserverSource :
    actuation.Actuator → Observer → observation.Source → Prop
  ReportsOccurrence :
    observation.World → observation.Observation → Occurrence → Prop
  ReportsEffect :
    observation.World → observation.Observation → actuation.Effect → Prop
  ReportsPostWorld :
    observation.World → observation.Observation → actuation.World → Prop

  verifyPostSnapshot :
    EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName →
      SealedWorldSnapshot observation → Bool
  verifyIndependence :
    actuation.Actuator → Observer → observation.Source → Bool
  verifyOccurrence :
    observation.World → observation.Observation → Occurrence → Bool
  verifyEffect :
    observation.World → observation.Observation → actuation.Effect → Bool
  verifyPostWorld :
    observation.World → observation.Observation → actuation.World → Bool

  postSnapshotSound :
    ∀ preSnapshot postSnapshot,
      verifyPostSnapshot preSnapshot postSnapshot = true →
        PostSnapshotFor preSnapshot postSnapshot
  independenceSound :
    ∀ actuator observer source,
      verifyIndependence actuator observer source = true →
        IndependentObserverSource actuator observer source
  occurrenceSound :
    ∀ world observed occurrence,
      observation.ObservationTrue world observed →
      verifyOccurrence world observed occurrence = true →
        ReportsOccurrence world observed occurrence
  effectSound :
    ∀ world observed effect,
      observation.ObservationTrue world observed →
      verifyEffect world observed effect = true →
        ReportsEffect world observed effect
  postWorldSound :
    ∀ world observed postWorld,
      observation.ObservationTrue world observed →
      verifyPostWorld world observed postWorld = true →
        ReportsPostWorld world observed postWorld

/--
Feedback input is either absent or contains one exact WI-1 attempt together
with its exact capture authorization.  An actuator receipt is not a substitute
for this constructor.
-/
inductive ReobservationInput
    (observation : ObservationSystem)
    (snapshot : SealedWorldSnapshot observation) where
  | absent
  | supplied
      (attempt : ObservationAttempt observation snapshot)
      (authorization :
        CaptureAuthorization observation snapshot attempt)

/-- Exhaustive WI-6 refusal vocabulary. -/
inductive FeedbackResidue where
  | noReobservation
  | observationRefused (residue : ObservationAdmissionResidue)
  | stalePreEffectObservation
  | observerSourceNotIndependent
  | occurrenceMismatch
  | effectMismatch
  | postWorldMismatch
  deriving DecidableEq, Repr

/--
Proof-carrying feedback closure for one exact admitted actuation.

The closure stores the independently admitted packet and all five bridge
proofs.  Its expected post-world is definitionally the WI-5 domain `apply`.
-/
structure FeedbackClosed
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    (feedback : FeedbackSystem actuation observation)
    (effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (effectContext : DeclaredEffectContext effectSnapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (actuationAttempt : ActuationAttempt actuation)
    (admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt)
    (postSnapshot : SealedWorldSnapshot observation)
    (observer : feedback.Observer) where
  /--
  The exact dependent WI-5 witness supplied to this closure establishes the
  effect relation being re-observed; it is not a detached premise.
  -/
  actuationEffectRelation :
    actuation.EffectRelation
      actuationAttempt.preWorld
      actuationAttempt.effect
      (actuation.apply
        actuationAttempt.actuator
        actuationAttempt.runtime
        actuationAttempt.preWorld
        actuationAttempt.effect)
  reobservation : AdmittedObservation observation postSnapshot
  observationTrue :
    observation.ObservationTrue
      postSnapshot.world reobservation.observation
  postSnapshotBound :
    feedback.PostSnapshotFor effectSnapshot postSnapshot
  observerSourceIndependent :
    feedback.IndependentObserverSource
      actuationAttempt.actuator observer reobservation.source
  occurrenceBound :
    feedback.ReportsOccurrence
      postSnapshot.world reobservation.observation
      effectContext.effect.occurrence
  effectBound :
    feedback.ReportsEffect
      postSnapshot.world reobservation.observation actuationAttempt.effect
  postWorldBound :
    feedback.ReportsPostWorld
      postSnapshot.world reobservation.observation
      (actuation.apply
        actuationAttempt.actuator
        actuationAttempt.runtime
        actuationAttempt.preWorld
        actuationAttempt.effect)

inductive FeedbackAdmissionResult
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    (feedback : FeedbackSystem actuation observation)
    (effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (effectContext : DeclaredEffectContext effectSnapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (actuationAttempt : ActuationAttempt actuation)
    (admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt)
    (postSnapshot : SealedWorldSnapshot observation)
    (observer : feedback.Observer) where
  | closed :
      FeedbackClosed
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer →
      FeedbackAdmissionResult
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer
  | refused :
      FeedbackResidue →
      FeedbackAdmissionResult
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer

/-- The common WI-6 admission tree; instances cannot self-report closure. -/
def admitFeedback
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    (feedback : FeedbackSystem actuation observation)
    (effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (effectContext : DeclaredEffectContext effectSnapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (actuationAttempt : ActuationAttempt actuation)
    (admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt)
    (postSnapshot : SealedWorldSnapshot observation)
    (observer : feedback.Observer)
    (input : ReobservationInput observation postSnapshot) :
    FeedbackAdmissionResult
      feedback effectSnapshot effectContext artifact target
      actuationAttempt admittedActuation postSnapshot observer := by
  match input with
  | .absent =>
      exact .refused .noReobservation
  | .supplied attempt authorization =>
      match observationResult : admitObservation attempt authorization with
      | .refuse residue =>
          exact .refused (.observationRefused residue)
      | .admitted packet =>
          if postSnapshotAccepted :
              feedback.verifyPostSnapshot effectSnapshot postSnapshot = true then
            if independent :
                feedback.verifyIndependence
                    actuationAttempt.actuator observer packet.source = true then
              if occurrence :
                  feedback.verifyOccurrence
                      postSnapshot.world packet.observation
                      effectContext.effect.occurrence = true then
                if effect :
                    feedback.verifyEffect
                        postSnapshot.world packet.observation
                        actuationAttempt.effect = true then
                  let postWorld :=
                    actuation.apply
                      actuationAttempt.actuator
                      actuationAttempt.runtime
                      actuationAttempt.preWorld
                      actuationAttempt.effect
                  if world :
                      feedback.verifyPostWorld
                          postSnapshot.world packet.observation postWorld = true then
                    have observationTrue :
                        observation.ObservationTrue
                          postSnapshot.world packet.observation :=
                      admitted_result_is_sound observationResult
                    exact .closed {
                      actuationEffectRelation :=
                        admitted_actuation_only_declared_effect admittedActuation
                      reobservation := packet
                      observationTrue := observationTrue
                      postSnapshotBound :=
                        feedback.postSnapshotSound
                          effectSnapshot postSnapshot postSnapshotAccepted
                      observerSourceIndependent :=
                        feedback.independenceSound
                          actuationAttempt.actuator observer packet.source independent
                      occurrenceBound :=
                        feedback.occurrenceSound
                          postSnapshot.world packet.observation
                          effectContext.effect.occurrence observationTrue occurrence
                      effectBound :=
                        feedback.effectSound
                          postSnapshot.world packet.observation
                          actuationAttempt.effect observationTrue effect
                      postWorldBound :=
                        feedback.postWorldSound
                          postSnapshot.world packet.observation
                          postWorld observationTrue world
                    }
                  else
                    exact .refused .postWorldMismatch
                else
                  exact .refused .effectMismatch
              else
                exact .refused .occurrenceMismatch
            else
              exact .refused .observerSourceNotIndependent
          else
            exact .refused .stalePreEffectObservation

/-! ## Headline projections -/

theorem feedback_closed_contains_exact_wi5_actuation
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    {feedback : FeedbackSystem actuation observation}
    {effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {effectContext : DeclaredEffectContext effectSnapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {actuationAttempt : ActuationAttempt actuation}
    {admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt}
    {postSnapshot : SealedWorldSnapshot observation}
    {observer : feedback.Observer}
    (closed :
      FeedbackClosed
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer) :
    actuation.EffectRelation
      actuationAttempt.preWorld
      actuationAttempt.effect
      (actuation.apply
        actuationAttempt.actuator actuationAttempt.runtime
        actuationAttempt.preWorld actuationAttempt.effect) :=
  closed.actuationEffectRelation

theorem feedback_closed_has_independent_admitted_reobservation
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    {feedback : FeedbackSystem actuation observation}
    {effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {effectContext : DeclaredEffectContext effectSnapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {actuationAttempt : ActuationAttempt actuation}
    {admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt}
    {postSnapshot : SealedWorldSnapshot observation}
    {observer : feedback.Observer}
    (closed :
      FeedbackClosed
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer) :
    observation.ObservationTrue
        postSnapshot.world closed.reobservation.observation ∧
      feedback.IndependentObserverSource
        actuationAttempt.actuator observer closed.reobservation.source :=
  ⟨closed.observationTrue, closed.observerSourceIndependent⟩

theorem feedback_closed_binds_occurrence_effect_and_post_world
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    {feedback : FeedbackSystem actuation observation}
    {effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {effectContext : DeclaredEffectContext effectSnapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {actuationAttempt : ActuationAttempt actuation}
    {admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt}
    {postSnapshot : SealedWorldSnapshot observation}
    {observer : feedback.Observer}
    (closed :
      FeedbackClosed
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer) :
    feedback.ReportsOccurrence
        postSnapshot.world closed.reobservation.observation
        effectContext.effect.occurrence ∧
      feedback.ReportsEffect
        postSnapshot.world closed.reobservation.observation
        actuationAttempt.effect ∧
      feedback.ReportsPostWorld
        postSnapshot.world closed.reobservation.observation
        (actuation.apply
          actuationAttempt.actuator actuationAttempt.runtime
          actuationAttempt.preWorld actuationAttempt.effect) :=
  ⟨closed.occurrenceBound, closed.effectBound, closed.postWorldBound⟩

/--
WI-6 headline: one closure binds the exact WI-5 effect relation to an
independently admitted, semantically true observation at an accepted
post-effect snapshot, including occurrence, effect, and post-world reports.
-/
theorem FeedbackClosed.sound
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {actuation :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {observation : ObservationSystem}
    {feedback : FeedbackSystem actuation observation}
    {effectSnapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {effectContext : DeclaredEffectContext effectSnapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {actuationAttempt : ActuationAttempt actuation}
    {admittedActuation :
      AdmittedActuation
        actuation effectSnapshot effectContext artifact target actuationAttempt}
    {postSnapshot : SealedWorldSnapshot observation}
    {observer : feedback.Observer}
    (closed :
      FeedbackClosed
        feedback effectSnapshot effectContext artifact target
        actuationAttempt admittedActuation postSnapshot observer) :
    actuation.EffectRelation
        actuationAttempt.preWorld
        actuationAttempt.effect
        (actuation.apply
          actuationAttempt.actuator actuationAttempt.runtime
          actuationAttempt.preWorld actuationAttempt.effect) ∧
      observation.ObservationTrue
        postSnapshot.world closed.reobservation.observation ∧
      feedback.PostSnapshotFor effectSnapshot postSnapshot ∧
      feedback.IndependentObserverSource
        actuationAttempt.actuator observer closed.reobservation.source ∧
      feedback.ReportsOccurrence
        postSnapshot.world closed.reobservation.observation
        effectContext.effect.occurrence ∧
      feedback.ReportsEffect
        postSnapshot.world closed.reobservation.observation
        actuationAttempt.effect ∧
      feedback.ReportsPostWorld
        postSnapshot.world closed.reobservation.observation
        (actuation.apply
          actuationAttempt.actuator actuationAttempt.runtime
          actuationAttempt.preWorld actuationAttempt.effect) :=
  ⟨closed.actuationEffectRelation,
    closed.observationTrue,
    closed.postSnapshotBound,
    closed.observerSourceIndependent,
    closed.occurrenceBound,
    closed.effectBound,
    closed.postWorldBound⟩

end Residua.RCC.PostEffectFeedback

import RCC.WorldModelAdequacy

/-!
# RCC WI-4 world-model-adequacy tests and countermodels

The positive fixture promotes the exact WI-3 temperature model to the external
intent that the sealed physical world has temperature 42.

Countermodels pin four boundaries:

* a different external intent is not implied by the true model claim;
* stale snapshots and wrong contexts are refused before adequacy verification;
* internal model truth can coexist with a false external intent; and
* a missing adequacy certificate cannot create an admitted judgment.
-/

namespace Residua.RCC.WorldModelAdequacy.Tests

open Residua.RCC.ObservationSoundness
open Residua.RCC.ObservationAbstraction
open Residua.RCC.WorldModelAdequacy

structure PhysicalWorld where
  temperature : Nat
  deriving DecidableEq, Repr

abbrev observationSystem : ObservationSystem where
  World := PhysicalWorld
  SnapshotQ := Nat
  Source := Unit
  Raw := Nat
  Observation := Nat
  Certificate := Bool
  snapshotQDecidableEq := inferInstance
  RawRepresents := fun world _ raw => raw = world.temperature
  ObservationTrue := fun world observation =>
    observation = world.temperature
  verify := fun _ raw observation certificate =>
    decide (raw = observation ∧ certificate = true)
  verifySound := by
    intro world _source raw observation _certificate authentic accepted
    have checked : raw = observation ∧ True :=
      ⟨(of_decide_eq_true accepted).1, True.intro⟩
    exact checked.1.symm.trans authentic

abbrev sealedSnapshot : SealedWorldSnapshot observationSystem where
  snapshotQ := 10
  world := ⟨42⟩

structure ModelContext where
  snapshotQ : Nat
  modelVersion : Nat
  deriving DecidableEq, Repr

abbrev exactContext : ModelContext :=
  ⟨10, 1⟩

abbrev abstractionSystem : AbstractionSystem observationSystem where
  ModelContext := ModelContext
  Model := Nat
  Claim := Nat
  Certificate := Bool
  ContextMatches := fun snapshotQ context =>
    context.snapshotQ = snapshotQ ∧ context.modelVersion = 1
  abstract := fun _ observations =>
    observations.head?.getD 0
  ModelClaim := fun _ observations model claim =>
    observations = [claim] ∧ model = claim
  verify := fun _ observations model claim certificate =>
    decide
      (observations = [claim] ∧
        model = claim ∧
        certificate = true)
  verifySound := by
    intro _world _snapshotQ _context observations model claim certificate
      _contextBound _observationsSound _computed accepted
    have checked :
        observations = [claim] ∧
          model = claim ∧
          certificate = true :=
      of_decide_eq_true accepted
    exact ⟨checked.1, checked.2.1⟩

abbrev admittedModel42 :
    AdmittedModelClaim
      observationSystem abstractionSystem sealedSnapshot where
  context := exactContext
  observations := [42]
  model := 42
  claim := 42
  certificate := true
  contextBound := ⟨rfl, rfl⟩
  observationsSound := by
    intro observation member
    simp at member
    subst observation
    rfl
  computed := rfl
  verifierAccepted := by decide

/--
External intent is a property of the sealed physical world, not a Boolean
copied from the model layer.
-/
abbrev intentSystem :
    ExternalIntentSystem observationSystem abstractionSystem where
  Intent := Nat
  AdequacyCertificate := Option Unit
  IntentSatisfied := fun snapshot intendedTemperature =>
    snapshot.world.temperature = intendedTemperature
  verify :=
    fun snapshotQ context _observations _model claim intent certificate =>
      decide
        (snapshotQ = context.snapshotQ ∧
          intent = claim ∧
          certificate = some ())
  verifySound := by
    intro snapshot context observations model claim intent certificate
      _contextBound observationsSound modelClaim accepted
    have checked :
        snapshot.snapshotQ = context.snapshotQ ∧
          intent = claim ∧
          certificate = some () :=
      of_decide_eq_true accepted
    have claimObserved : claim ∈ observations := by
      rw [modelClaim.1]
      simp
    have claimTrue :
        claim = snapshot.world.temperature :=
      observationsSound claim claimObserved
    exact claimTrue.symm.trans checked.2.1.symm

abbrev validAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot where
  claimedSnapshotQ := 10
  claimedContext := exactContext
  claimedObservations := [42]
  claimedModel := 42
  claimedClaim := 42
  intent := 42
  certificate := some ()

abbrev admittedIntent42 :
    AdmittedExternalIntent
      observationSystem abstractionSystem intentSystem sealedSnapshot where
  packet := admittedModel42
  intent := 42
  certificate := some ()
  verifierAccepted := by decide

theorem exact_model_property_establishes_external_intent :
    deriveExternalIntent admittedModel42 validAttempt =
      .admitted admittedIntent42 := by
  rfl

theorem admitted_external_intent_is_true :
    intentSystem.IntentSatisfied sealedSnapshot 42 :=
  admittedIntent42.sound

/-! ## Countermodel 1: wrong intent -/

abbrev wrongIntentAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with intent := 0 }

theorem wrong_intent_is_not_implied_by_model_claim :
    abstractionSystem.ModelClaim exactContext [42] 42 42 ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0 := by
  constructor
  · exact ⟨rfl, rfl⟩
  · decide

theorem wrong_intent_certificate_is_refused :
    deriveExternalIntent admittedModel42 wrongIntentAttempt =
      .refuse .adequacyCertificateRefused := by
  rfl

/-! ## Countermodel 2: stale snapshot and wrong context -/

abbrev staleAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with claimedSnapshotQ := 9 }

theorem stale_snapshot_is_refused :
    deriveExternalIntent admittedModel42 staleAttempt =
      .refuse .staleObservationSnapshot :=
  stale_adequacy_snapshot_is_refused _ _ (by decide)

abbrev wrongContext : ModelContext :=
  ⟨10, 2⟩

abbrev wrongContextAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with claimedContext := wrongContext }

theorem wrong_context_is_refused :
    deriveExternalIntent admittedModel42 wrongContextAttempt =
      .refuse .modelContextMismatch :=
  wrong_adequacy_context_is_refused _ _ rfl (by decide)

abbrev wrongObservationsAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with claimedObservations := [0] }

theorem wrong_observation_set_is_refused :
    deriveExternalIntent admittedModel42 wrongObservationsAttempt =
      .refuse .observationSetMismatch := by
  rfl

abbrev wrongModelAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with claimedModel := 0 }

theorem wrong_model_is_refused :
    deriveExternalIntent admittedModel42 wrongModelAttempt =
      .refuse .modelMismatch := by
  rfl

abbrev wrongClaimAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with claimedClaim := 0 }

theorem wrong_model_claim_is_refused :
    deriveExternalIntent admittedModel42 wrongClaimAttempt =
      .refuse .modelClaimMismatch := by
  rfl

/-! ## Countermodel 3: internal model truth is not external truth -/

theorem model_truth_can_coexist_with_false_external_intent :
    abstractionSystem.ModelClaim
        admittedModel42.context
        admittedModel42.observations
        admittedModel42.model
        admittedModel42.claim ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0 := by
  constructor
  · exact admittedModel42.sound
  · decide

theorem caller_boolean_cannot_establish_external_intent :
    true = true ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0 := by
  exact ⟨rfl, by decide⟩

/-! ## Countermodel 4: missing adequacy certificate -/

abbrev missingCertificateAttempt :
    AdequacyAttempt
      observationSystem abstractionSystem intentSystem sealedSnapshot :=
  { validAttempt with certificate := none }

theorem missing_adequacy_certificate_is_refused :
    deriveExternalIntent admittedModel42 missingCertificateAttempt =
      .refuse .adequacyCertificateRefused := by
  rfl

theorem missing_certificate_cannot_construct_admitted_judgment :
    ¬ ∃ judgment,
      deriveExternalIntent admittedModel42 missingCertificateAttempt =
        .admitted judgment := by
  intro alleged
  obtain ⟨judgment, admitted⟩ := alleged
  rw [missing_adequacy_certificate_is_refused] at admitted
  cases admitted

#print axioms AdmittedExternalIntent.sound
#print axioms admitted_external_intent_is_sound
#print axioms stale_adequacy_snapshot_is_refused
#print axioms wrong_adequacy_context_is_refused
#print axioms refused_adequacy_certificate_is_not_admitted
#print axioms exact_model_property_establishes_external_intent
#print axioms admitted_external_intent_is_true
#print axioms wrong_intent_is_not_implied_by_model_claim
#print axioms wrong_intent_certificate_is_refused
#print axioms stale_snapshot_is_refused
#print axioms wrong_context_is_refused
#print axioms wrong_observation_set_is_refused
#print axioms wrong_model_is_refused
#print axioms wrong_model_claim_is_refused
#print axioms model_truth_can_coexist_with_false_external_intent
#print axioms caller_boolean_cannot_establish_external_intent
#print axioms missing_adequacy_certificate_is_refused
#print axioms missing_certificate_cannot_construct_admitted_judgment

end Residua.RCC.WorldModelAdequacy.Tests

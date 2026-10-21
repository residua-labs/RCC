import RCCTests.WorldModelAdequacy

/-! RCC-77 candidate: sealed-world observation and intent adequacy bridge. -/

namespace Residua.RCC.RCC77Target

open Residua.RCC.WorldModelAdequacy.Tests
open Residua.RCC.WorldModelAdequacy
open Residua.RCC.ObservationAbstraction
open Residua.RCC.ObservationSoundness

def modelEstablishesIntent := exact_model_property_establishes_external_intent
def admittedIntentIsTrue := admitted_external_intent_is_true
def wrongIntentNotImplied := wrong_intent_is_not_implied_by_model_claim
def wrongIntentRefused := wrong_intent_certificate_is_refused
def staleSnapshotRefused := Residua.RCC.WorldModelAdequacy.Tests.stale_snapshot_is_refused
def wrongContextRefused := Residua.RCC.WorldModelAdequacy.Tests.wrong_context_is_refused
def wrongObservationsRefused := Residua.RCC.WorldModelAdequacy.Tests.wrong_observation_set_is_refused
def wrongModelRefused := Residua.RCC.WorldModelAdequacy.Tests.wrong_model_is_refused
def wrongClaimRefused := Residua.RCC.WorldModelAdequacy.Tests.wrong_model_claim_is_refused
def modelTruthFalseIntent := Residua.RCC.WorldModelAdequacy.Tests.model_truth_can_coexist_with_false_external_intent
def callerBooleanCannotEstablish := Residua.RCC.WorldModelAdequacy.Tests.caller_boolean_cannot_establish_external_intent
def missingCertificateRefused := Residua.RCC.WorldModelAdequacy.Tests.missing_adequacy_certificate_is_refused
def missingCertificateCannotAdmit := Residua.RCC.WorldModelAdequacy.Tests.missing_certificate_cannot_construct_admitted_judgment

universe uS uQ uSource uRaw uObs uCert
universe uCtx uModel uClaim uAbsCert
universe uIntent uAdeqCert

abbrev AdmittedIntentSoundClaim : Prop :=
  ∀ {S : ObservationSystem.{uS, uQ, uSource, uRaw, uObs, uCert}}
    {A : AbstractionSystem.{uCtx, uModel, uClaim, uAbsCert,
      uS, uQ, uSource, uRaw, uObs, uCert} S}
    {I : ExternalIntentSystem.{uIntent, uAdeqCert, uS, uAbsCert,
      uQ, uSource, uRaw, uObs, uCert, uCtx, uModel, uClaim} S A}
    {snapshot : SealedWorldSnapshot.{uS, uQ, uSource, uRaw, uObs, uCert} S}
    (admitted : AdmittedExternalIntent.{uS, uAbsCert, uIntent, uAdeqCert,
      uQ, uSource, uRaw, uObs, uCert, uCtx, uModel, uClaim} S A I snapshot),
    I.IntentSatisfied snapshot admitted.intent

def admittedIntentSound : AdmittedIntentSoundClaim := by
  intro S A I snapshot admitted
  exact admitted.sound

structure Certificate where
  modelEstablishesIntent :
    deriveExternalIntent admittedModel42 validAttempt =
      .admitted admittedIntent42
  admittedIntentIsTrue :
    intentSystem.IntentSatisfied sealedSnapshot 42
  wrongIntentNotImplied :
    abstractionSystem.ModelClaim exactContext [42] 42 42 ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0
  admittedIntentSound :
    ∀ (admitted :
      AdmittedExternalIntent observationSystem abstractionSystem intentSystem
        sealedSnapshot),
      intentSystem.IntentSatisfied sealedSnapshot admitted.intent
  wrongIntentRefused :
    deriveExternalIntent admittedModel42 wrongIntentAttempt =
      .refuse .adequacyCertificateRefused
  staleSnapshotRefused :
    deriveExternalIntent admittedModel42 staleAttempt =
      .refuse .staleObservationSnapshot
  wrongContextRefused :
    deriveExternalIntent admittedModel42 wrongContextAttempt =
      .refuse .modelContextMismatch
  wrongObservationsRefused :
    deriveExternalIntent admittedModel42 wrongObservationsAttempt =
      .refuse .observationSetMismatch
  wrongModelRefused :
    deriveExternalIntent admittedModel42 wrongModelAttempt =
      .refuse .modelMismatch
  wrongClaimRefused :
    deriveExternalIntent admittedModel42 wrongClaimAttempt =
      .refuse .modelClaimMismatch
  modelTruthFalseIntent :
    abstractionSystem.ModelClaim
        admittedModel42.context
        admittedModel42.observations
        admittedModel42.model
        admittedModel42.claim ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0
  callerBooleanCannotEstablish :
    true = true ∧
      ¬ intentSystem.IntentSatisfied sealedSnapshot 0
  missingCertificateRefused :
    deriveExternalIntent admittedModel42 missingCertificateAttempt =
      .refuse .adequacyCertificateRefused
  missingCertificateCannotAdmit :
    ¬ ∃ judgment,
      deriveExternalIntent admittedModel42 missingCertificateAttempt =
        .admitted judgment

def certificate : Certificate where
  modelEstablishesIntent := exact_model_property_establishes_external_intent
  admittedIntentIsTrue := admitted_external_intent_is_true
  wrongIntentNotImplied := wrong_intent_is_not_implied_by_model_claim
  admittedIntentSound := by
    intro admitted
    exact admitted.sound
  wrongIntentRefused := wrong_intent_certificate_is_refused
  staleSnapshotRefused := stale_snapshot_is_refused
  wrongContextRefused := wrong_context_is_refused
  wrongObservationsRefused := wrong_observation_set_is_refused
  wrongModelRefused := wrong_model_is_refused
  wrongClaimRefused := wrong_model_claim_is_refused
  modelTruthFalseIntent := model_truth_can_coexist_with_false_external_intent
  callerBooleanCannotEstablish := caller_boolean_cannot_establish_external_intent
  missingCertificateRefused := missing_adequacy_certificate_is_refused
  missingCertificateCannotAdmit := missing_certificate_cannot_construct_admitted_judgment

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC77Target

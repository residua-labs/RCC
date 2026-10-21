import RCCTests.ObservationSoundness

/-! RCC-82 candidate: sealed observation soundness and authority boundaries. -/

namespace Residua.RCC.RCC82Target

open Residua.RCC.ObservationSoundness.Tests
open Residua.RCC.ObservationSoundness

def validObservationAdmitted := valid_observation_is_admitted
def admittedTemperatureTrue := admitted_temperature_is_true_of_sealed_world
def logicalWorldSound := logical_world_contains_only_sound_fixture
def staleSnapshotRefused := stale_observation_is_refused
def unsignedCaptureRefused := unsigned_capture_is_refused
def substitutedSourceUnverified := substituted_source_has_no_authentic_capture
def substitutedSourceRefused := substituted_source_without_authority_is_refused
def forgedValueRefused := forged_value_certificate_is_refused
def forgedValueNotTrue := forged_value_is_not_true_of_world
def alwaysAcceptUnsound := always_accept_verifier_is_unsound
def trueMayBeRefused := true_observation_may_be_refused_without_completeness

structure Certificate where
  validObservationAdmitted :
    admitObservation validAttempt validCapture = .admitted validPacket
  admittedTemperatureTrue :
    temperatureSystem.ObservationTrue sealedWorld.world validPacket.observation
  substitutedSourceUnverified :
    ¬ temperatureSystem.RawRepresents sealedWorld.world
        substitutedSourceAttempt.source substitutedSourceAttempt.raw
  forgedValueNotTrue :
    ¬ temperatureSystem.ObservationTrue sealedWorld.world forgedValueAttempt.observation
  alwaysAcceptUnsound :
    ¬ ∀ {world source raw observation certificate},
      temperatureSystem.RawRepresents world source raw →
        mutantAlwaysAccept source raw observation certificate = true →
          temperatureSystem.ObservationTrue world observation

def certificate : Certificate where
  validObservationAdmitted := validObservationAdmitted
  admittedTemperatureTrue := admittedTemperatureTrue
  substitutedSourceUnverified := substitutedSourceUnverified
  forgedValueNotTrue := forgedValueNotTrue
  alwaysAcceptUnsound := alwaysAcceptUnsound

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC82Target

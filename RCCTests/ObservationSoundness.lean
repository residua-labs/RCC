import RCC.ObservationSoundness

/-!
# RCC WI-1 observation-soundness tests and countermodels

The fixture models a temperature sensor.  A raw capture is authentic only when
its physical source identity and measured value agree with the sealed world.
The certificate verifier additionally binds the semantic observation.

Mutants cover stale snapshots, absent capture authority, source substitution,
forged semantic values, and an always-accept verifier.  A final fixture shows
the deliberate WI-1/WI-2 boundary: an invalid certificate may reject an
actually true observation without violating soundness.
-/

namespace Residua.RCC.ObservationSoundness.Tests

open Residua.RCC.ObservationSoundness

inductive Sensor
  | primary
  | backup
  deriving DecidableEq, Repr

inductive Certificate
  | valid
  | invalid
  deriving DecidableEq, Repr

structure PhysicalWorld where
  temperature : Nat
  deriving DecidableEq, Repr

structure RawReading where
  sensor : Sensor
  value : Nat
  deriving DecidableEq, Repr

abbrev temperatureSystem : ObservationSystem where
  World := PhysicalWorld
  SnapshotQ := Nat
  Source := Sensor
  Raw := RawReading
  Observation := Nat
  Certificate := Certificate
  snapshotQDecidableEq := inferInstance
  RawRepresents := fun world source raw =>
    raw.sensor = source ∧ raw.value = world.temperature
  ObservationTrue := fun world observation =>
    observation = world.temperature
  verify := fun source raw observation certificate =>
    decide
      (raw.sensor = source ∧
        raw.value = observation ∧
        certificate = .valid)
  verifySound := by
    intro world source raw observation certificate authentic accepted
    have checked :
        raw.sensor = source ∧
          raw.value = observation ∧
          certificate = Certificate.valid :=
      of_decide_eq_true accepted
    exact checked.2.1.symm.trans authentic.2

abbrev sealedWorld : SealedWorldSnapshot temperatureSystem where
  snapshotQ := 10
  world := ⟨42⟩

abbrev validAttempt : ObservationAttempt temperatureSystem sealedWorld where
  claimedSnapshotQ := 10
  source := .primary
  raw := ⟨.primary, 42⟩
  observation := 42
  certificate := .valid

abbrev validCapture :
    CaptureAuthorization temperatureSystem sealedWorld validAttempt :=
  .certified ⟨rfl, rfl⟩

abbrev validPacket : AdmittedObservation temperatureSystem sealedWorld where
  source := .primary
  raw := ⟨.primary, 42⟩
  observation := 42
  certificate := .valid
  sourceAuthentic := ⟨rfl, rfl⟩
  verifierAccepted := by decide

theorem valid_observation_is_admitted :
    admitObservation validAttempt validCapture =
      .admitted validPacket := by
  rfl

theorem admitted_temperature_is_true_of_sealed_world :
    temperatureSystem.ObservationTrue
      sealedWorld.world validPacket.observation :=
  validPacket.sound

def validLogicalWorld :
    LogicalWorld temperatureSystem sealedWorld where
  observations := [validPacket]

theorem logical_world_contains_only_sound_fixture :
    temperatureSystem.ObservationTrue
      sealedWorld.world validPacket.observation :=
  logical_world_member_is_sound
    validLogicalWorld validPacket (by simp [validLogicalWorld])

/-! ## Mutant 1: stale snapshot identity -/

abbrev staleAttempt : ObservationAttempt temperatureSystem sealedWorld :=
  { validAttempt with claimedSnapshotQ := 9 }

theorem stale_observation_is_refused :
    admitObservation staleAttempt
        (.certified (by exact ⟨rfl, rfl⟩)) =
      .refuse .staleSnapshot :=
  stale_snapshot_is_refused _ _ (by decide)

/-! ## Mutant 2: no source-capture authority -/

theorem unsigned_capture_is_refused :
    admitObservation validAttempt (.absent) =
      .refuse .sourceCaptureUnverified :=
  absent_capture_authority_is_refused validAttempt rfl

/-! ## Mutant 3: source substitution -/

abbrev substitutedSourceAttempt :
    ObservationAttempt temperatureSystem sealedWorld :=
  { validAttempt with source := .backup }

theorem substituted_source_has_no_authentic_capture :
    ¬ temperatureSystem.RawRepresents
        sealedWorld.world
        substitutedSourceAttempt.source
        substitutedSourceAttempt.raw := by
  intro alleged
  exact (by decide : Sensor.primary ≠ Sensor.backup) alleged.1

theorem substituted_source_without_authority_is_refused :
    admitObservation substitutedSourceAttempt (.absent) =
      .refuse .sourceCaptureUnverified :=
  absent_capture_authority_is_refused substitutedSourceAttempt rfl

/-! ## Mutant 4: raw value and semantic observation disagree -/

abbrev forgedValueAttempt :
    ObservationAttempt temperatureSystem sealedWorld :=
  { validAttempt with observation := 99 }

theorem forged_value_certificate_is_refused :
    admitObservation forgedValueAttempt
        (.certified (by exact ⟨rfl, rfl⟩)) =
      .refuse .certificateRefused := by
  apply refused_certificate_is_not_admitted
  · rfl
  · decide

theorem forged_value_is_not_true_of_world :
    ¬ temperatureSystem.ObservationTrue
        sealedWorld.world forgedValueAttempt.observation := by
  decide

/-! ## Mutant 5: always-accept cannot inhabit the soundness law -/

def mutantAlwaysAccept
    (_source : Sensor)
    (_raw : RawReading)
    (_observation : Nat)
    (_certificate : Certificate) : Bool :=
  true

theorem always_accept_verifier_is_unsound :
    ¬ ∀ {world source raw observation certificate},
      temperatureSystem.RawRepresents world source raw →
        mutantAlwaysAccept source raw observation certificate = true →
        temperatureSystem.ObservationTrue world observation := by
  intro alleged
  have falseObservation :
      temperatureSystem.ObservationTrue (PhysicalWorld.mk 42) 99 :=
    alleged
      (world := PhysicalWorld.mk 42)
      (source := Sensor.primary)
      (raw := RawReading.mk Sensor.primary 42)
      (observation := 99)
      (certificate := Certificate.valid)
      ⟨rfl, rfl⟩
      rfl
  exact (by decide : (99 : Nat) ≠ 42) falseObservation

/-! ## WI-1 does not overclaim WI-2 completeness -/

abbrev trueButInvalidCertificateAttempt :
    ObservationAttempt temperatureSystem sealedWorld :=
  { validAttempt with certificate := .invalid }

theorem true_observation_may_be_refused_without_completeness :
    temperatureSystem.ObservationTrue
        sealedWorld.world trueButInvalidCertificateAttempt.observation ∧
      admitObservation trueButInvalidCertificateAttempt
          (.certified (by exact ⟨rfl, rfl⟩)) =
        .refuse .certificateRefused := by
  constructor
  · rfl
  · apply refused_certificate_is_not_admitted
    · rfl
    · decide

#print axioms AdmittedObservation.sound
#print axioms admitted_result_is_sound
#print axioms stale_snapshot_is_refused
#print axioms absent_capture_authority_is_refused
#print axioms refused_certificate_is_not_admitted
#print axioms logical_world_member_is_sound
#print axioms valid_observation_is_admitted
#print axioms admitted_temperature_is_true_of_sealed_world
#print axioms stale_observation_is_refused
#print axioms unsigned_capture_is_refused
#print axioms substituted_source_has_no_authentic_capture
#print axioms forged_value_certificate_is_refused
#print axioms forged_value_is_not_true_of_world
#print axioms always_accept_verifier_is_unsound
#print axioms true_observation_may_be_refused_without_completeness

end Residua.RCC.ObservationSoundness.Tests

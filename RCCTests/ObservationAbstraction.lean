import RCC.ObservationAbstraction

/-!
# RCC WI-3 abstraction-soundness tests and countermodels

The positive fixture takes one WI-1 admitted temperature observation and
constructs a context-bound model whose value is exactly that observation.

Countermodels pin four boundaries:

* a raw forged value cannot enter the WI-1 logical world;
* an abstraction function's output alone is not a model theorem;
* stale snapshots and wrong model contexts are refused; and
* an internal model claim does not by itself establish an external intent
  (the later WI-4 obligation).
-/

namespace Residua.RCC.ObservationAbstraction.Tests

open Residua.RCC.ObservationSoundness
open Residua.RCC.ObservationAbstraction

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
    intro world source raw observation certificate authentic accepted
    have checked : raw = observation ∧ certificate = true :=
      of_decide_eq_true accepted
    exact checked.1.symm.trans authentic

abbrev sealedSnapshot : SealedWorldSnapshot observationSystem where
  snapshotQ := 10
  world := ⟨42⟩

abbrev observed42 :
    AdmittedObservation observationSystem sealedSnapshot where
  source := ()
  raw := 42
  observation := 42
  certificate := true
  sourceAuthentic := rfl
  verifierAccepted := by decide

def logicalWorld42 : LogicalWorld observationSystem sealedSnapshot where
  observations := [observed42]

structure ModelContext where
  snapshotQ : Nat
  modelVersion : Nat
  deriving DecidableEq, Repr

abbrev exactContext : ModelContext :=
  ⟨10, 1⟩

/-- The bounded WI-3 instance: one observation becomes one exact model value. -/
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

abbrev validAttempt :
    AbstractionAttempt
      observationSystem abstractionSystem sealedSnapshot where
  claimedSnapshotQ := 10
  context := exactContext
  claim := 42
  certificate := true

abbrev validContextAuthorization :
    ModelContextAuthorization
      observationSystem abstractionSystem sealedSnapshot validAttempt :=
  .certified ⟨rfl, rfl⟩

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

theorem admitted_logical_world_abstraction :
    abstractLogicalWorld
        logicalWorld42 validAttempt validContextAuthorization =
      .admitted admittedModel42 := by
  rfl

theorem admitted_model_claim_is_sound :
    abstractionSystem.ModelClaim
      admittedModel42.context
      admittedModel42.observations
      admittedModel42.model
      admittedModel42.claim :=
  admittedModel42.sound

/-! ## Countermodel 1: forged observation cannot enter through WI-1 -/

theorem forged_observation_is_not_true :
    ¬ observationSystem.ObservationTrue sealedSnapshot.world 99 := by
  decide

theorem logical_world_has_no_forged_observation :
    ¬ ∃ packet,
      packet ∈ logicalWorld42.observations ∧
        packet.observation = 99 := by
  intro alleged
  obtain ⟨packet, member, forged⟩ := alleged
  have sound :=
    logical_world_member_is_sound logicalWorld42 packet member
  rw [forged] at sound
  exact forged_observation_is_not_true sound

/-! ## Countermodel 2: executable abstraction alone has no authority -/

def mutantConstantZero
    (_context : ModelContext)
    (_observations : List Nat) : Nat :=
  0

theorem abstraction_output_alone_does_not_establish_model_claim :
    mutantConstantZero exactContext [42] = 0 ∧
      ¬ abstractionSystem.ModelClaim exactContext [42]
        (mutantConstantZero exactContext [42]) 42 := by
  constructor
  · rfl
  · intro alleged
    exact (by decide : (0 : Nat) ≠ 42) alleged.2

theorem always_accept_unsound_abstraction_has_no_soundness_law :
    ¬ ∀ {world snapshotQ context observations model claim},
      abstractionSystem.ContextMatches snapshotQ context →
        (∀ observation, observation ∈ observations →
          observationSystem.ObservationTrue world observation) →
        model = mutantConstantZero context observations →
        true = true →
        abstractionSystem.ModelClaim context observations model claim := by
  intro alleged
  have falseClaim :
      abstractionSystem.ModelClaim exactContext [42] 0 42 :=
    alleged
      (world := PhysicalWorld.mk 42)
      (snapshotQ := 10)
      (context := exactContext)
      (observations := [42])
      (model := 0)
      (claim := 42)
      ⟨rfl, rfl⟩
      (by
        intro observation member
        simp at member
        subst observation
        rfl)
      rfl
      rfl
  exact (by decide : (0 : Nat) ≠ 42) falseClaim.2

/-! ## Countermodel 3: stale snapshot and wrong model context -/

abbrev staleAttempt :
    AbstractionAttempt
      observationSystem abstractionSystem sealedSnapshot :=
  { validAttempt with claimedSnapshotQ := 9 }

theorem stale_model_abstraction_is_refused :
    abstractLogicalWorld logicalWorld42 staleAttempt
        (.certified (by exact ⟨rfl, rfl⟩)) =
      .refuse .staleObservationSnapshot :=
  stale_abstraction_snapshot_is_refused _ _ _ (by decide)

abbrev wrongVersionContext : ModelContext :=
  ⟨10, 2⟩

abbrev wrongContextAttempt :
    AbstractionAttempt
      observationSystem abstractionSystem sealedSnapshot :=
  { validAttempt with context := wrongVersionContext }

theorem wrong_model_context_is_not_bound :
    ¬ abstractionSystem.ContextMatches
        sealedSnapshot.snapshotQ wrongVersionContext := by
  intro alleged
  exact (by decide : (2 : Nat) ≠ 1) alleged.2

theorem wrong_model_context_is_refused :
    abstractLogicalWorld logicalWorld42 wrongContextAttempt (.absent) =
      .refuse .modelContextUnbound :=
  absent_model_context_is_refused _ _ rfl

/-! ## Countermodel 4: WI-3 model truth is not WI-4 external intent -/

def ExternalIntent (world : PhysicalWorld) : Prop :=
  world.temperature = 0

theorem model_claim_does_not_establish_external_intent :
    abstractionSystem.ModelClaim exactContext [42] 42 42 ∧
      ¬ ExternalIntent sealedSnapshot.world := by
  constructor
  · exact ⟨rfl, rfl⟩
  · intro alleged
    change (42 : Nat) = 0 at alleged
    exact (by decide : (42 : Nat) ≠ 0) alleged

#print axioms observationValuesSound
#print axioms AdmittedModelClaim.sound
#print axioms admitted_abstraction_is_sound
#print axioms stale_abstraction_snapshot_is_refused
#print axioms absent_model_context_is_refused
#print axioms refused_abstraction_certificate_is_not_admitted
#print axioms admitted_logical_world_abstraction
#print axioms admitted_model_claim_is_sound
#print axioms forged_observation_is_not_true
#print axioms logical_world_has_no_forged_observation
#print axioms abstraction_output_alone_does_not_establish_model_claim
#print axioms always_accept_unsound_abstraction_has_no_soundness_law
#print axioms stale_model_abstraction_is_refused
#print axioms wrong_model_context_is_not_bound
#print axioms wrong_model_context_is_refused
#print axioms model_claim_does_not_establish_external_intent

end Residua.RCC.ObservationAbstraction.Tests

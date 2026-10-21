import RCC.SerializableEpochClosure
import RCCTests.ConflictSerializability
import RCCTests.GlobalSerializability

/-!
# RCC-56 Serializable Finalized Epoch Cut Countermodels

The positive witness combines:

* an actual RCC-45 finalized closure;
* a complete RCC-49 finalized-event universe and global serial execution; and
* the RCC-51 invariant law over that exact execution.

Local/nonfinal views, partition-local orders, pending transitions, empty event
coverage, and empty occurrence schedules cannot inhabit the certificate.
-/

namespace Residua.RCC.SerializableEpochClosure.Tests

open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.SerializableEpochClosure

/-- The actual RCC-45 finalized cut used by the RCC-56 fixture. -/
def finalizedClosure :
    FinalizedClosureEvidence
      (environment := admissionEnvironment)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      (protocol := sourceProtocol)
      (ConfigStable := configStable) where
  snapshot := currentSnapshot
  finalizedHead := headEnvelope
  finalizedWindow := fullSealEnvelope
  slotMatches := rfl
  parentMatches := rfl
  headMatches := rfl
  headConfigMatches := rfl
  windowHeadMatches := rfl
  windowConfigMatches := rfl
  sourceAuthorityMatches := rfl
  watermarkMatches := rfl
  partitionsMatch := rfl
  stableConfig := stableConfigEvidence

abbrev ActualConflictSerializableHistory :=
  ConflictSerializableHistory
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    surface finalizedHistory configLawful Head.genesis

/-- Complete one-event RCC-45 universe for the one-step serial execution. -/
def actualEventUniverse :
    FinalizedEventUniverse ActualFinalizedEvent where
  InUniverse event := event = actualFinalizedEvent
  enumeration := [actualFinalizedEvent]
  sound := by
    intro event member
    simp at member
    exact member
  complete := by
    intro event inUniverse
    simp [inUniverse]

/-- Actual RCC-49 global history, not a union of local orders. -/
def actualConflictSerializableHistory :
    ActualConflictSerializableHistory where
  eventUniverse := actualEventUniverse
  occurrences := [.deployment]
  finalState := .headA
  execution := actualSerialHistory
  enumeratedOccurrenceComplete := by
    intro event member
    have actual : event = actualFinalizedEvent :=
      actualEventUniverse.sound event member
    cases actual
    simp
  occurrenceSound := by
    intro occurrence member
    simp at member
    cases member
    exact ⟨actualFinalizedEvent, rfl, rfl⟩
  occurrenceFaithful := by
    intro left right leftIn rightIn _sameOccurrence
    cases leftIn
    cases rightIn
    rfl

abbrev ActualRCC56Certificate :=
  SerializableEpochClosureEvidence
    surface finalizedHistory configLawful Head.genesis reachableInvariant
      finalizedClosure

def actualSerializableEpochClosure :
    ActualRCC56Certificate where
  serial := actualConflictSerializableHistory
  headEvent := actualFinalizedEvent
  headEventInUniverse := rfl
  headEventIsClosureEvent := rfl
  headEventFinal := ⟨[], rfl⟩
  headEventHeadBound := rfl
  headEventConfigBound := rfl
  finalHeadBound := rfl
  invariantLaw := reachableInvariantLaw
  initialInvariant := Or.inl rfl

theorem actual_cut_is_eligible :
    assessSerializableEpochClosure (some actualSerializableEpochClosure) =
      SerializableEpochClosureAssessment.eligible
        actualSerializableEpochClosure := by
  rfl

theorem actual_cut_preserves_global_invariant :
    reachableInvariant actualConflictSerializableHistory.finalState :=
  serializable_epoch_closure_final_invariant actualSerializableEpochClosure

theorem actual_cut_serializes_canonical_head_occurrence :
    actualSerializableEpochClosure.headEvent.occurrenceId ∈
      actualConflictSerializableHistory.occurrences :=
  closure_head_occurrence_is_serialized actualSerializableEpochClosure

theorem actual_cut_retains_complete_source_coverage :
    CoverageCertificate
      sourceProtocol.InUniverse finalizedClosure.snapshot.priorPartitions :=
  serializable_epoch_closure_source_coverage actualSerializableEpochClosure

/-! ## Mutant 1: local/nonfinal view -/

structure LocalHistoryCut where
  localHead : Head
  localConfig : Config
  localGreen : Bool

def localOnlyCut : LocalHistoryCut :=
  ⟨.headA, .v1, true⟩

theorem local_nonfinal_cut_is_refused :
    localOnlyCut.localGreen = true ∧
      assessSerializableEpochClosure
        (none : Option ActualRCC56Certificate) =
        SerializableEpochClosureAssessment.refuse
          .canonicalFinalizedSerializableCutRequired := by
  exact ⟨rfl, rfl⟩

/-! ## Mutant 2: partition-local order presented as global serializability -/

theorem locally_ordered_cut_can_still_be_unserializable :
    Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .westSecond ∧
      Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .eastFirst .eastSecond ∧
      ¬ Residua.RCC.ConflictSerializability.Tests.PairComparable
        Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .eastFirst :=
  Residua.RCC.ConflictSerializability.Tests.locally_ordered_partitions_are_not_a_global_order

theorem unserializable_local_cut_is_refused :
    assessSerializableEpochClosure
      (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired := by
  rfl

/-! ## Mutant 3: actual pending transition at the closure coordinate -/

theorem pending_transition_cut_has_no_stability_certificate :
    ¬ Nonempty
      (StableConfigEvidence
        pendingTransitionView .deploy .headA .v1) :=
  actual_pending_transition_excludes_stable_evidence

theorem pending_transition_cut_is_refused :
    assessSerializableEpochClosure
      (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired := by
  rfl

/-! ## Mutant 4: empty closed-world event coverage -/

theorem empty_event_universe_cannot_cover_canonical_head
    (eventUniverse : FinalizedEventUniverse ActualFinalizedEvent)
    (headInUniverse :
      eventUniverse.InUniverse actualFinalizedEvent)
    (empty : eventUniverse.enumeration = []) :
    False :=
  empty_event_coverage_cannot_contain_canonical_head
    eventUniverse actualFinalizedEvent headInUniverse empty

theorem empty_occurrence_schedule_cannot_be_eligible
    (certificate : ActualRCC56Certificate)
    (empty : certificate.serial.occurrences = []) :
    False :=
  (serializable_epoch_closure_schedule_nonempty certificate) empty

end Residua.RCC.SerializableEpochClosure.Tests

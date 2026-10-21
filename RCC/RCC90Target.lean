import RCCTests.SerializableEpochClosure

/-! RCC-90 candidate: serializable finalized epoch closure. -/

namespace Residua.RCC.RCC90Target

open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.SerializableEpochClosure
open Residua.RCC.SerializableEpochClosure.Tests

def actualCutEligible := actual_cut_is_eligible
def actualInvariantPreserved := actual_cut_preserves_global_invariant
def canonicalHeadOccurrenceSerialized := actual_cut_serializes_canonical_head_occurrence
def sourceCoverageComplete := actual_cut_retains_complete_source_coverage
def localNonfinalRefused := local_nonfinal_cut_is_refused
def localOrderNotGlobal := locally_ordered_cut_can_still_be_unserializable
def unserializableLocalRefused := unserializable_local_cut_is_refused
def pendingTransitionUnstable := pending_transition_cut_has_no_stability_certificate
def pendingTransitionRefused := pending_transition_cut_is_refused
def emptyEventCoverageRefused := empty_event_universe_cannot_cover_canonical_head
def emptyOccurrenceScheduleRefused := empty_occurrence_schedule_cannot_be_eligible

structure Certificate where
  actualCutEligible :
    assessSerializableEpochClosure (some actualSerializableEpochClosure) =
      SerializableEpochClosureAssessment.eligible
        actualSerializableEpochClosure
  actualInvariantPreserved :
    reachableInvariant actualConflictSerializableHistory.finalState
  canonicalHeadOccurrenceSerialized :
    actualSerializableEpochClosure.headEvent.occurrenceId ∈
      actualConflictSerializableHistory.occurrences
  sourceCoverageComplete :
    CoverageCertificate
      sourceProtocol.InUniverse finalizedClosure.snapshot.priorPartitions
  localNonfinalRefused :
    localOnlyCut.localGreen = true ∧
      assessSerializableEpochClosure
        (none : Option ActualRCC56Certificate) =
        SerializableEpochClosureAssessment.refuse
          .canonicalFinalizedSerializableCutRequired
  localOrderNotGlobal :
    Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .westSecond ∧
      Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .eastFirst .eastSecond ∧
      ¬ Residua.RCC.ConflictSerializability.Tests.PairComparable
        Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .eastFirst
  unserializableLocalRefused :
    assessSerializableEpochClosure
      (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired
  pendingTransitionUnstable :
    ¬ Nonempty
      (StableConfigEvidence
        pendingTransitionView .deploy .headA .v1)
  pendingTransitionRefused :
    assessSerializableEpochClosure
      (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired
  emptyEventCoverageRefused :
    ∀ eventUniverse : FinalizedEventUniverse ActualFinalizedEvent,
      eventUniverse.InUniverse actualFinalizedEvent →
      eventUniverse.enumeration = [] → False
  emptyOccurrenceScheduleRefused :
    ∀ certificate : ActualRCC56Certificate,
      certificate.serial.occurrences = [] → False

def certificate : Certificate where
  actualCutEligible := actual_cut_is_eligible
  actualInvariantPreserved := actual_cut_preserves_global_invariant
  canonicalHeadOccurrenceSerialized := actual_cut_serializes_canonical_head_occurrence
  sourceCoverageComplete := actual_cut_retains_complete_source_coverage
  localNonfinalRefused := local_nonfinal_cut_is_refused
  localOrderNotGlobal := locally_ordered_cut_can_still_be_unserializable
  unserializableLocalRefused := unserializable_local_cut_is_refused
  pendingTransitionUnstable := pending_transition_cut_has_no_stability_certificate
  pendingTransitionRefused := pending_transition_cut_is_refused
  emptyEventCoverageRefused := empty_event_universe_cannot_cover_canonical_head
  emptyOccurrenceScheduleRefused := empty_occurrence_schedule_cannot_be_eligible

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC90Target

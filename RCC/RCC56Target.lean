import RCCTests.SerializableEpochClosure

/-! RCC-56 candidate receipt: serializable finalized epoch closure. -/
namespace Residua.RCC.RCC56Target
open Residua.RCC.SerializableEpochClosure.Tests
open Residua.RCC.SerializableEpochClosure
open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.GlobalSerializability
open Residua.RCC.GlobalSerializability.Tests

structure Certificate where
  eligible :
    assessSerializableEpochClosure (some actualSerializableEpochClosure) =
      SerializableEpochClosureAssessment.eligible actualSerializableEpochClosure
  invariant : reachableInvariant actualConflictSerializableHistory.finalState
  headSerialized :
    actualSerializableEpochClosure.headEvent.occurrenceId ∈
      actualConflictSerializableHistory.occurrences
  sourceCoverage :
    CoverageCertificate sourceProtocol.InUniverse
      finalizedClosure.snapshot.priorPartitions
  localRefused :
    localOnlyCut.localGreen = true ∧
      assessSerializableEpochClosure (none : Option ActualRCC56Certificate) =
        SerializableEpochClosureAssessment.refuse
          .canonicalFinalizedSerializableCutRequired
  partitionOrderRefused :
    Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .westSecond ∧
      Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .eastFirst .eastSecond ∧
      ¬ Residua.RCC.ConflictSerializability.Tests.PairComparable
        Residua.RCC.ConflictSerializability.Tests.LocalBefore
        .westFirst .eastFirst
  unserializableRefused :
    assessSerializableEpochClosure (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired
  pendingRefused :
    assessSerializableEpochClosure (none : Option ActualRCC56Certificate) =
      SerializableEpochClosureAssessment.refuse
        .canonicalFinalizedSerializableCutRequired
  pendingStabilityRefused :
    ¬ Nonempty
      (StableConfigEvidence
        pendingTransitionView .deploy .headA .v1)
  emptyEventRefused :
    ∀ (eventUniverse : FinalizedEventUniverse ActualFinalizedEvent),
      (headInUniverse : eventUniverse.InUniverse actualFinalizedEvent) →
      eventUniverse.enumeration = [] → False
  emptyScheduleRefused :
    ∀ (certificate : ActualRCC56Certificate),
      certificate.serial.occurrences = [] → False

def certificate : Certificate where
  eligible := actual_cut_is_eligible
  invariant := actual_cut_preserves_global_invariant
  headSerialized := actual_cut_serializes_canonical_head_occurrence
  sourceCoverage := actual_cut_retains_complete_source_coverage
  localRefused := local_nonfinal_cut_is_refused
  partitionOrderRefused := locally_ordered_cut_can_still_be_unserializable
  unserializableRefused := unserializable_local_cut_is_refused
  pendingRefused := pending_transition_cut_is_refused
  pendingStabilityRefused := pending_transition_cut_has_no_stability_certificate
  emptyEventRefused := empty_event_universe_cannot_cover_canonical_head
  emptyScheduleRefused := empty_occurrence_schedule_cannot_be_eligible

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩
end Residua.RCC.RCC56Target

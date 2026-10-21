import RCCTests.ConflictSerializability

/-! RCC-91 candidate: global conflict serializability and occurrence coverage. -/

namespace Residua.RCC.RCC91Target

open Residua.RCC.ConflictSerializability.Tests
open Residua.RCC.GlobalSerializability

def westLocalOrder := west_partition_is_locally_ordered
def eastLocalOrder := east_partition_is_locally_ordered
def localOrdersNotGlobal := locally_ordered_partitions_are_not_a_global_order
def globalScheduleCompares := one_global_schedule_compares_cross_partition_occurrences
def sameValueNotOccurrence := same_value_does_not_identify_occurrence
def valueDedupCannotCover := value_dedup_cannot_cover_both_occurrences
def valueScheduleIncomplete := value_deduplicated_schedule_is_not_occurrence_complete

theorem globalScheduleCompares_exact :
    OccursBefore
      Occurrence.westFirst Occurrence.eastFirst
      [.westFirst, .westSecond, .eastFirst, .eastSecond] := by
  exact OccursBefore.here (List.Mem.tail _ (List.Mem.head _))

theorem valueScheduleIncomplete_exact :
    ¬ (∀ occurrence,
      occurrence ∈ [Occurrence.westFirst, Occurrence.eastFirst] →
      occurrence ∈ [Occurrence.westFirst]) := by
  intro complete
  have eastCovered :=
    complete .eastFirst (List.Mem.tail _ (List.Mem.head _))
  nomatch eastCovered

structure Certificate where
  westLocalOrder :
    LocalBefore .westFirst .westSecond
  eastLocalOrder :
    LocalBefore .eastFirst .eastSecond
  localOrdersNotGlobal :
    LocalBefore .westFirst .westSecond ∧
      LocalBefore .eastFirst .eastSecond ∧
      ¬ PairComparable LocalBefore .westFirst .eastFirst
  globalScheduleCompares :
    OccursBefore
      Occurrence.westFirst Occurrence.eastFirst
      [.westFirst, .westSecond, .eastFirst, .eastSecond]
  sameValueNotOccurrence :
    valueOf .westFirst = valueOf .eastFirst ∧
      Occurrence.westFirst ≠ Occurrence.eastFirst
  valueDedupCannotCover :
    ¬ ∃ representative : Value → Occurrence,
      representative (valueOf .westFirst) = .westFirst ∧
        representative (valueOf .eastFirst) = .eastFirst
  valueScheduleIncomplete :
    ¬ (∀ occurrence,
      occurrence ∈ [Occurrence.westFirst, Occurrence.eastFirst] →
      occurrence ∈ [Occurrence.westFirst])

def certificate : Certificate where
  westLocalOrder := west_partition_is_locally_ordered
  eastLocalOrder := east_partition_is_locally_ordered
  localOrdersNotGlobal := locally_ordered_partitions_are_not_a_global_order
  globalScheduleCompares := globalScheduleCompares_exact
  sameValueNotOccurrence := same_value_does_not_identify_occurrence
  valueDedupCannotCover := value_dedup_cannot_cover_both_occurrences
  valueScheduleIncomplete := valueScheduleIncomplete_exact

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC91Target

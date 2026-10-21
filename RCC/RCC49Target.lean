import RCCTests.ConflictSerializability

/-!
# RCC-49 target package

This candidate packages global occurrence ordering and the identity boundary:
partition-local orders do not establish a global serial order, and equal
values do not identify distinct durable occurrences.
-/

namespace Residua.RCC.RCC49Target

open Residua.RCC.ConflictSerializability.Tests
open Residua.RCC.ConflictSerializability
open Residua.RCC.GlobalSerializability

structure Certificate : Prop where
  localOrderNotGlobal :
    LocalBefore .westFirst .westSecond ∧
      LocalBefore .eastFirst .eastSecond ∧
      ¬ PairComparable LocalBefore .westFirst .eastFirst
  globalScheduleCompares :
    OccursBefore
      Occurrence.westFirst Occurrence.eastFirst
      [.westFirst, .westSecond, .eastFirst, .eastSecond]
  valueAndOccurrenceSeparate :
    valueOf .westFirst = valueOf .eastFirst ∧
      Occurrence.westFirst ≠ Occurrence.eastFirst
  valueDedupRefused :
    ¬ ∃ representative : Value → Occurrence,
      representative (valueOf .westFirst) = .westFirst ∧
        representative (valueOf .eastFirst) = .eastFirst
  occurrenceCoverageRefused :
    ¬ (∀ occurrence,
      occurrence ∈ [Occurrence.westFirst, Occurrence.eastFirst] →
      occurrence ∈ [Occurrence.westFirst])

def certificate : Certificate where
  localOrderNotGlobal := locally_ordered_partitions_are_not_a_global_order
  globalScheduleCompares := one_global_schedule_compares_cross_partition_occurrences
  valueAndOccurrenceSeparate := same_value_does_not_identify_occurrence
  valueDedupRefused := value_dedup_cannot_cover_both_occurrences
  occurrenceCoverageRefused := value_deduplicated_schedule_is_not_occurrence_complete

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC49Target

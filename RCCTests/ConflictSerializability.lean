import RCC.ConflictSerializability

/-!
# RCC-49 Conflict Serializability Countermodels

These mutants isolate the two identity/coverage failures that a collection of
locally ordered histories does not exclude:

* partition-local orders need not compare a cross-partition conflict;
* equal values do not identify equal durable occurrences.
-/

namespace Residua.RCC.ConflictSerializability.Tests

open Residua.RCC.GlobalSerializability
open Residua.RCC.ConflictSerializability

inductive Partition
  | west
  | east
  deriving DecidableEq

inductive Occurrence
  | westFirst
  | westSecond
  | eastFirst
  | eastSecond
  deriving DecidableEq, Repr

def partitionOf : Occurrence → Partition
  | .westFirst | .westSecond => .west
  | .eastFirst | .eastSecond => .east

/--
Two independent partition logs each expose a real local order, but intentionally
contain no cross-partition edge.
-/
def LocalBefore : Occurrence → Occurrence → Prop
  | .westFirst, .westSecond => True
  | .eastFirst, .eastSecond => True
  | _, _ => False

def PairComparable
    (Before : Occurrence → Occurrence → Prop)
    (left right : Occurrence) : Prop :=
  Before left right ∨ Before right left

theorem west_partition_is_locally_ordered :
    LocalBefore .westFirst .westSecond :=
  True.intro

theorem east_partition_is_locally_ordered :
    LocalBefore .eastFirst .eastSecond :=
  True.intro

/--
CM-RCC49-LOCAL: local sorting on both partitions is not a global total order;
the cross-partition occurrence pair is incomparable.
-/
theorem locally_ordered_partitions_are_not_a_global_order :
    LocalBefore .westFirst .westSecond ∧
      LocalBefore .eastFirst .eastSecond ∧
      ¬ PairComparable LocalBefore .westFirst .eastFirst := by
  refine ⟨True.intro, True.intro, ?_⟩
  intro comparable
  cases comparable with
  | inl westBeforeEast => exact westBeforeEast
  | inr eastBeforeWest => exact eastBeforeWest

/--
One actual global occurrence schedule compares the same cross-partition pair.
The schedule, rather than either local projection, is the authority.
-/
theorem one_global_schedule_compares_cross_partition_occurrences :
    OccursBefore
      Occurrence.westFirst Occurrence.eastFirst
      [.westFirst, .westSecond, .eastFirst, .eastSecond] := by
  exact OccursBefore.here (by simp)

inductive Value
  | samePayload
  deriving DecidableEq, Repr

def valueOf (_ : Occurrence) : Value :=
  .samePayload

/--
CM-RCC49-VALUE: equal payload/value identity does not collapse two durable
occurrences.
-/
theorem same_value_does_not_identify_occurrence :
    valueOf .westFirst = valueOf .eastFirst ∧
      Occurrence.westFirst ≠ Occurrence.eastFirst :=
  ⟨rfl, Occurrence.noConfusion⟩

/--
No value-keyed representative function can retain both equal-valued
occurrences.  One of them would be silently swallowed.
-/
theorem value_dedup_cannot_cover_both_occurrences :
    ¬ ∃ representative : Value → Occurrence,
      representative (valueOf .westFirst) = .westFirst ∧
        representative (valueOf .eastFirst) = .eastFirst := by
  rintro ⟨representative, westBound, eastBound⟩
  have collapsed :
      Occurrence.westFirst = Occurrence.eastFirst :=
    westBound.symm.trans eastBound
  exact Occurrence.noConfusion collapsed

/--
A schedule deduplicated by the shared value cannot satisfy RCC-49 occurrence
coverage for both finalized occurrence identities.
-/
theorem value_deduplicated_schedule_is_not_occurrence_complete :
    ¬ (∀ occurrence,
      occurrence ∈ [Occurrence.westFirst, Occurrence.eastFirst] →
      occurrence ∈ [Occurrence.westFirst]) := by
  intro complete
  have eastCovered :=
    complete .eastFirst (by simp)
  simp at eastCovered

#print axioms west_partition_is_locally_ordered
#print axioms east_partition_is_locally_ordered
#print axioms locally_ordered_partitions_are_not_a_global_order
#print axioms one_global_schedule_compares_cross_partition_occurrences
#print axioms same_value_does_not_identify_occurrence
#print axioms value_dedup_cannot_cover_both_occurrences
#print axioms value_deduplicated_schedule_is_not_occurrence_complete
#print axioms inUniverse_occurrence_mem
#print axioms all_noncommuting_finalized_occurrence_pairs_globally_ordered
#print axioms global_occurrence_order_nodup
#print axioms same_occurrence_same_durable_event

end Residua.RCC.ConflictSerializability.Tests

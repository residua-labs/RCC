import RCC.RCC49Target

/-! Thin admission checks for RCC-49 occurrence ordering and identity. -/

namespace Residua.RCC.RCC49Target.Tests

open Residua.RCC.ConflictSerializability.Tests
open Residua.RCC.ConflictSerializability
open Residua.RCC.GlobalSerializability

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_local_order_not_global :
    LocalBefore .westFirst .westSecond ∧
      LocalBefore .eastFirst .eastSecond ∧
      ¬ PairComparable LocalBefore .westFirst .eastFirst :=
  certificate.localOrderNotGlobal

theorem target_global_schedule_compares_cross_partition :
    OccursBefore
      Occurrence.westFirst Occurrence.eastFirst
      [.westFirst, .westSecond, .eastFirst, .eastSecond] :=
  certificate.globalScheduleCompares

theorem target_value_and_occurrence_separate :
    valueOf .westFirst = valueOf .eastFirst ∧
      Occurrence.westFirst ≠ Occurrence.eastFirst :=
  certificate.valueAndOccurrenceSeparate

theorem target_value_dedup_refused :
    ¬ ∃ representative : Value → Occurrence,
      representative (valueOf .westFirst) = .westFirst ∧
        representative (valueOf .eastFirst) = .eastFirst :=
  certificate.valueDedupRefused

#print axioms target_certificate_nonempty
#print axioms target_local_order_not_global
#print axioms target_global_schedule_compares_cross_partition
#print axioms target_value_and_occurrence_separate
#print axioms target_value_dedup_refused

end Residua.RCC.RCC49Target.Tests

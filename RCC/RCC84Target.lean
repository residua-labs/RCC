import RCCTests.OccurrenceExactness

/-! RCC-84 candidate: occurrence quotient exactness and consumer separation. -/

namespace Residua.RCC.RCC84Target

open Residua.RCC.OccurrenceExactness.Tests
open Residua.RCC.OccurrenceExactness

def retryDeliveryDistinct := retry_is_distinct_delivery_of_same_occurrence
def retryPreservesOccurrence := retry_preserves_logical_occurrence
def intentionalRepeatDistinct := intentional_repeat_mints_distinct_occurrence_key
def intentionalRepeatNotRetry := intentional_repeat_is_not_retry
def contentDoesNotIdentifyOccurrence := identical_content_does_not_identify_occurrence
def contentOnlyDedupRejected := content_only_dedup_conflates_intentional_repeat

structure Certificate where
  retryDeliveryDistinct :
    firstDelivery ≠ retryDelivery ∧
      occurrenceKey firstDelivery.occurrence =
        occurrenceKey retryDelivery.occurrence
  retryPreservesOccurrence :
    SameLogicalOccurrence firstDelivery.occurrence retryDelivery.occurrence
  intentionalRepeatDistinct :
    occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment
  intentionalRepeatNotRetry :
    ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment
  contentDoesNotIdentifyOccurrence :
    paymentPayload firstPayment = paymentPayload intentionalSecondPayment ∧
      occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment
  contentOnlyDedupRejected :
    contentOnlyKey firstPayment = contentOnlyKey intentionalSecondPayment ∧
      ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment

def certificate : Certificate where
  retryDeliveryDistinct := retryDeliveryDistinct
  retryPreservesOccurrence := retryPreservesOccurrence
  intentionalRepeatDistinct := intentionalRepeatDistinct
  intentionalRepeatNotRetry := intentionalRepeatNotRetry
  contentDoesNotIdentifyOccurrence := contentDoesNotIdentifyOccurrence
  contentOnlyDedupRejected := contentOnlyDedupRejected

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC84Target

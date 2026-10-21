import RCC.OccurrenceExactness

/-!
# RCC-27 Occurrence Exactness Witnesses

Two intentional identical effects may share content while remaining different
logical occurrences.  Retries preserve the occurrence key; intentional repeats
must mint a new generation.
-/

namespace Residua.RCC.OccurrenceExactness.Tests

open Residua.RCC.OccurrenceExactness

inductive Run
  | checkout
  deriving DecidableEq

inductive Slot
  | charge
  deriving DecidableEq

inductive EffectKind
  | payment
  deriving DecidableEq

inductive Payload
  | amount100
  deriving DecidableEq

abbrev PaymentOccurrence :=
  Occurrence Run Slot Nat EffectKind

def firstPayment : PaymentOccurrence where
  run := .checkout
  slot := .charge
  generation := 1
  effectKind := .payment

def firstPaymentRetry : PaymentOccurrence :=
  firstPayment

def intentionalSecondPayment : PaymentOccurrence where
  run := .checkout
  slot := .charge
  generation := 2
  effectKind := .payment

/-!
Delivery-attempt identity is deliberately outside `Occurrence`.  A transport
retry is a different delivery attempt for the same logical occurrence.
-/
structure DeliveryAttempt where
  occurrence : PaymentOccurrence
  attempt : Nat
  deriving DecidableEq

def firstDelivery : DeliveryAttempt where
  occurrence := firstPayment
  attempt := 1

def retryDelivery : DeliveryAttempt where
  occurrence := firstPaymentRetry
  attempt := 2

theorem retry_is_distinct_delivery_of_same_occurrence :
    firstDelivery ≠ retryDelivery ∧
      occurrenceKey firstDelivery.occurrence =
        occurrenceKey retryDelivery.occurrence := by
  exact ⟨by decide, rfl⟩

theorem retry_preserves_logical_occurrence :
    SameLogicalOccurrence
      firstDelivery.occurrence retryDelivery.occurrence :=
  (occurrence_key_exact _ _).mp
    retry_is_distinct_delivery_of_same_occurrence.2

theorem intentional_repeat_mints_distinct_occurrence_key :
    occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment := by
  decide

theorem intentional_repeat_is_not_retry :
    ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment := by
  intro same
  have equal :=
    (occurrence_key_exact firstPayment intentionalSecondPayment).mpr same
  have different :
      occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment := by
    decide
  exact different equal

def paymentPayload (_ : PaymentOccurrence) : Payload :=
  .amount100

theorem identical_content_does_not_identify_occurrence :
    paymentPayload firstPayment = paymentPayload intentionalSecondPayment ∧
      occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment := by
  exact ⟨rfl, by decide⟩

def contentOnlyKey (occurrence : PaymentOccurrence) : Payload :=
  paymentPayload occurrence

theorem content_only_dedup_conflates_intentional_repeat :
    contentOnlyKey firstPayment = contentOnlyKey intentionalSecondPayment ∧
      ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment := by
  constructor
  · rfl
  · intro same
    have equal :=
      (occurrence_key_exact firstPayment intentionalSecondPayment).mpr same
    have different :
        occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment := by
      decide
    exact different equal

example (left right : PaymentOccurrence) :
    occurrenceKey left = occurrenceKey right ↔
      SameLogicalOccurrence left right :=
  occurrence_key_exact left right

#print axioms occurrence_key_exact
#print axioms same_logical_occurrence_refl
#print axioms same_logical_occurrence_symm
#print axioms same_logical_occurrence_trans
#print axioms retry_is_distinct_delivery_of_same_occurrence
#print axioms retry_preserves_logical_occurrence
#print axioms intentional_repeat_mints_distinct_occurrence_key
#print axioms intentional_repeat_is_not_retry
#print axioms identical_content_does_not_identify_occurrence
#print axioms content_only_dedup_conflates_intentional_repeat

end Residua.RCC.OccurrenceExactness.Tests

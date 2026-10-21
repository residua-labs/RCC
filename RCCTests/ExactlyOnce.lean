import RCC.ExactlyOnce

/-!
# RCC-28 Exactly-Once Premise Witnesses

The positive theorem requires all three load-bearing premises:

* a logical occurrence is delivered at least once;
* every admitted delivery carries the receiver's current fence;
* the receiver atomically commits enactment and receipt under occurrence
  identity.

The four countermodels pin the boundaries: content identity is too coarse,
check-then-enact is not atomic, at-most-once delivery permits zero effects, and
history CAS alone does not couple the external world to history.
-/

namespace Residua.RCC.ExactlyOnce.Tests

open Residua.RCC.ExactlyOnce

inductive PaymentOccurrence
  | first
  | second
  deriving DecidableEq, Repr

inductive PaymentEffect
  | charge100
  deriving DecidableEq, Repr

inductive PaymentReceipt
  | settledFirst
  | settledSecond
  deriving DecidableEq, Repr

abbrev PaymentFence :=
  FencingToken Unit Unit Unit Nat

def paymentFence : PaymentOccurrence → PaymentFence
  | .first =>
      { epoch := ()
      , head := ()
      , effectSlot := ()
      , generation := 7 }
  | .second =>
      { epoch := ()
      , head := ()
      , effectSlot := ()
      , generation := 8 }

def paymentEffect (_ : PaymentOccurrence) : PaymentEffect :=
  .charge100

def paymentReceipt (occurrence : PaymentOccurrence)
    (_fence : PaymentFence) (_effect : PaymentEffect) : PaymentReceipt :=
  match occurrence with
  | .first => .settledFirst
  | .second => .settledSecond

def paymentReceiver :
    AtomicReceiverContract
      PaymentOccurrence PaymentFence PaymentEffect PaymentReceipt where
  currentFence := paymentFence
  effectFor := paymentEffect
  receiptFor := paymentReceipt

def firstDelivery : Delivery PaymentOccurrence PaymentFence where
  occurrence := .first
  fence := paymentFence .first

def firstRetry : Delivery PaymentOccurrence PaymentFence :=
  firstDelivery

def firstAtLeastOnceSchedule :
    List (Delivery PaymentOccurrence PaymentFence) :=
  [firstDelivery, firstRetry, firstRetry]

theorem first_schedule_at_least_once :
    AtLeastOnce firstAtLeastOnceSchedule .first := by
  exact ⟨firstDelivery, List.Mem.head _, rfl⟩

theorem first_schedule_is_fenced :
    FencedDeliveries paymentReceiver firstAtLeastOnceSchedule := by
  intro delivery member
  cases member with
  | head =>
      rfl
  | tail _ secondOrThird =>
      cases secondOrThird with
      | head =>
          rfl
      | tail _ thirdOrEmpty =>
          cases thirdOrEmpty with
          | head =>
              rfl
          | tail _ impossible =>
              cases impossible

/-- RCC-28 positive control: retries still yield one observable enactment. -/
theorem atomic_receiver_delivers_exactly_once :
    ExactlyOnceObservable
      (run paymentReceiver
        (emptyState
          (Occurrence := PaymentOccurrence)
          (Fence := PaymentFence)
          (Effect := PaymentEffect)
          (Receipt := PaymentReceipt))
        firstAtLeastOnceSchedule)
      .first := by
  exact exactly_once_observable_of_at_least_once
    paymentReceiver firstAtLeastOnceSchedule .first
    first_schedule_at_least_once first_schedule_is_fenced

/-- The positive witness exposes the receipt coupled to the enacted effect. -/
theorem atomic_receiver_enactment_has_receiver_receipt :
    ∃ receipt,
      ObservableReceipt
        (run paymentReceiver
          (emptyState
            (Occurrence := PaymentOccurrence)
            (Fence := PaymentFence)
            (Effect := PaymentEffect)
            (Receipt := PaymentReceipt))
          firstAtLeastOnceSchedule)
        .first receipt := by
  rcases atomic_receiver_delivers_exactly_once with
    ⟨effect, observable, _unique⟩
  exact observable_enactment_has_coupled_receipt
    (run paymentReceiver emptyState firstAtLeastOnceSchedule)
    .first effect observable

/-! ## CM-RCC28-01: content key conflates intentional identical effects -/

structure IntentionalPayment where
  occurrence : PaymentOccurrence
  amount : Nat
  deriving DecidableEq, Repr

def intentionalFirst : IntentionalPayment :=
  ⟨.first, 100⟩

def intentionalSecond : IntentionalPayment :=
  ⟨.second, 100⟩

def contentKey (payment : IntentionalPayment) : Nat :=
  payment.amount

def contentKeyObservableCount
    (first second : IntentionalPayment) : Nat :=
  if contentKey first = contentKey second then 1 else 2

theorem content_key_conflates_two_intentional_effects :
    intentionalFirst.occurrence ≠ intentionalSecond.occurrence ∧
      contentKeyObservableCount intentionalFirst intentionalSecond = 1 := by
  decide

/-! ## CM-RCC28-02: non-atomic check-then-enact can double fire -/

structure CheckThenEnactRace where
  firstSawFree : Bool
  secondSawFree : Bool
  deriving DecidableEq, Repr

def racedEffects (race : CheckThenEnactRace) : Nat :=
  (if race.firstSawFree then 1 else 0) +
    (if race.secondSawFree then 1 else 0)

def doubleCheckThenEnact : CheckThenEnactRace :=
  ⟨true, true⟩

theorem non_atomic_check_then_enact_double_fires :
    racedEffects doubleCheckThenEnact = 2 := by
  decide

/-! ## CM-RCC28-03: at-most-once delivery permits zero effects -/

def AtMostOnceDelivery (schedule : List Nat) (occurrence : Nat) : Prop :=
  schedule.count occurrence ≤ 1

theorem empty_schedule_is_at_most_once_but_not_exactly_once :
    AtMostOnceDelivery [] 42 ∧ ¬ (List.count 42 [] = 1) := by
  constructor
  · unfold AtMostOnceDelivery
    decide
  · decide

/-! ## CM-RCC28-04: history CAS alone permits a world/history split -/

structure HistoryCASOnly where
  worldEffects : Nat
  historyReceipts : Nat
  deriving DecidableEq, Repr

def historyCASRace : HistoryCASOnly :=
  ⟨2, 1⟩

def HistoryCASHolds (state : HistoryCASOnly) : Prop :=
  state.historyReceipts ≤ 1

theorem history_cas_does_not_couple_world_and_history :
    HistoryCASHolds historyCASRace ∧
      historyCASRace.worldEffects ≠ historyCASRace.historyReceipts := by
  constructor
  · unfold HistoryCASHolds historyCASRace
    decide
  · decide

#print axioms atomic_receiver_delivers_exactly_once
#print axioms atomic_receiver_enactment_has_receiver_receipt
#print axioms content_key_conflates_two_intentional_effects
#print axioms non_atomic_check_then_enact_double_fires
#print axioms empty_schedule_is_at_most_once_but_not_exactly_once
#print axioms history_cas_does_not_couple_world_and_history

end Residua.RCC.ExactlyOnce.Tests


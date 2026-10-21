import RCC.ExactlyOnce
import RCCTests.ExactlyOnce

/-!
# RCC-28 target package

This candidate packages the scoped exactly-once premise: at-least-once
delivery, current fencing, and receiver-owned atomic deduplication keyed by
logical occurrence yield one observable enactment with a coupled receipt.
It also records the four load-bearing countermodels from the test surface.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC28Target

open Residua.RCC.ExactlyOnce
open Residua.RCC.ExactlyOnce.Tests

universe u v w x

theorem generic_exactly_once_of_at_least_once
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (deliveries : List (Delivery Occurrence Fence))
    (occurrence : Occurrence)
    (atLeastOnce : AtLeastOnce deliveries occurrence)
    (fenced : FencedDeliveries contract deliveries) :
    ExactlyOnceObservable
      (run contract emptyState deliveries) occurrence :=
  exactly_once_observable_of_at_least_once
    contract deliveries occurrence atLeastOnce fenced

structure ConcreteWitness : Prop where
  scheduleAtLeastOnce :
    AtLeastOnce firstAtLeastOnceSchedule .first
  scheduleFenced :
    FencedDeliveries paymentReceiver firstAtLeastOnceSchedule
  exactlyOnceObservable :
    ExactlyOnceObservable
      (run paymentReceiver
        (emptyState
          (Occurrence := PaymentOccurrence)
          (Fence := PaymentFence)
          (Effect := PaymentEffect)
          (Receipt := PaymentReceipt))
        firstAtLeastOnceSchedule)
      .first
  coupledReceipt :
    ∃ receipt,
      ObservableReceipt
        (run paymentReceiver
          (emptyState
            (Occurrence := PaymentOccurrence)
            (Fence := PaymentFence)
            (Effect := PaymentEffect)
            (Receipt := PaymentReceipt))
          firstAtLeastOnceSchedule)
        .first receipt

structure MutantRefusal : Prop where
  contentKeyConflation :
    intentionalFirst.occurrence ≠ intentionalSecond.occurrence ∧
      contentKeyObservableCount intentionalFirst intentionalSecond = 1
  nonAtomicDoubleFire :
    racedEffects doubleCheckThenEnact = 2
  atMostOnceAllowsZero :
    AtMostOnceDelivery [] 42 ∧ ¬ (List.count 42 [] = 1)
  historyWorldSplit :
    HistoryCASHolds historyCASRace ∧
      historyCASRace.worldEffects ≠ historyCASRace.historyReceipts

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { scheduleAtLeastOnce := first_schedule_at_least_once
      scheduleFenced := first_schedule_is_fenced
      exactlyOnceObservable := atomic_receiver_delivers_exactly_once
      coupledReceipt := atomic_receiver_enactment_has_receiver_receipt }
  mutants :=
    { contentKeyConflation := content_key_conflates_two_intentional_effects
      nonAtomicDoubleFire := non_atomic_check_then_enact_double_fires
      atMostOnceAllowsZero := empty_schedule_is_at_most_once_but_not_exactly_once
      historyWorldSplit := history_cas_does_not_couple_world_and_history }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC28Target


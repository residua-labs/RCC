import RCC.OccurrenceExactness
import RCCTests.OccurrenceExactness

/-!
# RCC-27 target package

This candidate packages the structured occurrence identity law.  It proves
that retries preserve one logical occurrence while intentional repeats mint a
new generation, and it rejects content-only deduplication as an occurrence
identity.  Digest binding and at-least-once delivery remain separate targets.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC27Target

open Residua.RCC.OccurrenceExactness
open Residua.RCC.OccurrenceExactness.Tests

universe u v w x

theorem generic_occurrence_key_exact
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (left right : Occurrence Run Slot Generation EffectKind) :
    occurrenceKey left = occurrenceKey right ↔
      SameLogicalOccurrence left right :=
  occurrence_key_exact left right

structure ConcreteWitness : Prop where
  retryDistinctDelivery :
    firstDelivery ≠ retryDelivery
  retryPreservesOccurrence :
    SameLogicalOccurrence
      firstDelivery.occurrence retryDelivery.occurrence
  intentionalRepeatDistinctKey :
    occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment
  intentionalRepeatNotRetry :
    ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment
  identicalContentDistinctOccurrence :
    paymentPayload firstPayment = paymentPayload intentionalSecondPayment ∧
      occurrenceKey firstPayment ≠ occurrenceKey intentionalSecondPayment

structure MutantRefusal : Prop where
  contentOnlyDedupConflation :
    contentOnlyKey firstPayment = contentOnlyKey intentionalSecondPayment ∧
      ¬ SameLogicalOccurrence firstPayment intentionalSecondPayment

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { retryDistinctDelivery := retry_is_distinct_delivery_of_same_occurrence.1
      retryPreservesOccurrence := retry_preserves_logical_occurrence
      intentionalRepeatDistinctKey := intentional_repeat_mints_distinct_occurrence_key
      intentionalRepeatNotRetry := intentional_repeat_is_not_retry
      identicalContentDistinctOccurrence :=
        identical_content_does_not_identify_occurrence }
  mutants :=
    { contentOnlyDedupConflation :=
        content_only_dedup_conflates_intentional_repeat }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC27Target


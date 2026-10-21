import RCC.OccurrenceExactness
import RCC.DigestBinding

/-!
# RCC-27 typed occurrence-address realization

This bridge lifts the structured `OccurrenceKey` exactness theorem to the
typed digest-address layer.  The cryptographic boundary remains explicit:
address exactness requires `DigestInjectiveOnCanonicalRange` for the supplied
domain- and schema-separated occurrence binding.

The theorem does not derive occurrence minting, atomic receiver deduplication,
or fencing; those remain RCC-28 obligations.
-/

namespace Residua.RCC.OccurrenceExactness

open Residua.RCC.Addressing

universe u v w x y

/-- Occurrence identity as an explicit typed quotient domain. -/
def occurrenceIdentityDomain
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) : IdentityDomain .occurrence where
  Object := Occurrence Run Slot Generation EffectKind
  Context := Unit
  Observation := OccurrenceKey Run Slot Generation EffectKind
  equivalent := fun _ => SameLogicalOccurrence
  observe := fun _ => occurrenceKey

/-- The occurrence relation is an equivalence and the structured key respects it. -/
def occurrenceQuotientAdequate
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) :
    QuotientAdequate
      (occurrenceIdentityDomain Run Slot Generation EffectKind) where
  equivalence := fun _ =>
    ⟨same_logical_occurrence_refl,
      same_logical_occurrence_symm,
      same_logical_occurrence_trans⟩
  observe_sound := fun same =>
    (occurrence_key_exact _ _).2 same

/-- Structured-key equality also reflects the declared occurrence relation. -/
def occurrenceObservationExact
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) :
    ObservationExact
      (occurrenceIdentityDomain Run Slot Generation EffectKind) :=
  fun equalKey => (occurrence_key_exact _ _).1 equalKey

/-- Reconstruct the structured occurrence represented by a canonical key. -/
def occurrenceOfKey
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (key : OccurrenceKey Run Slot Generation EffectKind) :
    Occurrence Run Slot Generation EffectKind where
  run := key.run
  slot := key.slot
  generation := key.generation
  effectKind := key.effectKind

theorem occurrence_key_of_key
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (key : OccurrenceKey Run Slot Generation EffectKind) :
    occurrenceKey (occurrenceOfKey key) = key := by
  cases key
  rfl

theorem occurrence_of_key_of_occurrence
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (occurrence : Occurrence Run Slot Generation EffectKind) :
    occurrenceOfKey (occurrenceKey occurrence) = occurrence := by
  cases occurrence
  rfl

/-- The occurrence quotient at its sole intrinsic context. -/
abbrev OccurrenceClass
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) :=
  Quotient
    ((occurrenceIdentityDomain Run Slot Generation EffectKind).setoid
      (occurrenceQuotientAdequate Run Slot Generation EffectKind) ())

/-- Eliminate an occurrence quotient into its exact structured key. -/
def occurrenceClassKey
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (quotientClass : OccurrenceClass Run Slot Generation EffectKind) :
    OccurrenceKey Run Slot Generation EffectKind :=
  Quotient.lift occurrenceKey
    (fun left right same =>
      (occurrence_key_exact left right).2 same)
    quotientClass

/-- Inject a structured occurrence key into the declared quotient. -/
def occurrenceKeyClass
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (key : OccurrenceKey Run Slot Generation EffectKind) :
    OccurrenceClass Run Slot Generation EffectKind :=
  qAbs
    (occurrenceIdentityDomain Run Slot Generation EffectKind)
    (occurrenceQuotientAdequate Run Slot Generation EffectKind)
    () (occurrenceOfKey key)

/-- Exact canonical codec between occurrence classes and structured keys. -/
def occurrenceClassCodec
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) :
    ExactCanonicalCodec
      (OccurrenceClass Run Slot Generation EffectKind)
      (OccurrenceKey Run Slot Generation EffectKind) where
  encode := occurrenceClassKey
  decode := fun key => some (occurrenceKeyClass key)
  decode_encode := by
    intro quotientClass
    refine Quotient.inductionOn quotientClass ?_
    intro occurrence
    change
      some
          (qAbs
            (occurrenceIdentityDomain Run Slot Generation EffectKind)
            (occurrenceQuotientAdequate Run Slot Generation EffectKind)
            () (occurrenceOfKey (occurrenceKey occurrence))) =
        some
          (qAbs
            (occurrenceIdentityDomain Run Slot Generation EffectKind)
            (occurrenceQuotientAdequate Run Slot Generation EffectKind)
            () occurrence)
    rw [occurrence_of_key_of_occurrence]
  encode_decode_canonical := by
    intro key quotientClass decoded
    change some (occurrenceKeyClass key) = some quotientClass at decoded
    have equalClass : occurrenceKeyClass key = quotientClass :=
      Option.some.inj decoded
    rw [← equalClass]
    exact occurrence_key_of_key key

/-- A digest binding whose address kind is statically fixed to occurrence. -/
abbrev OccurrenceDigestBinding
    (Run : Type u) (Slot : Type v) (Generation : Type w)
    (EffectKind : Type x) (Wire : Type y) :=
  DigestBinding .occurrence
    (OccurrenceKey Run Slot Generation EffectKind) Wire

/-- Derive a typed occurrence address from the exact structured key. -/
def occurrenceAddress
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x} {Wire : Type y}
    (binding : OccurrenceDigestBinding Run Slot Generation EffectKind Wire)
    (occurrence : Occurrence Run Slot Generation EffectKind) :
    Address .occurrence :=
  canonicalObjectAddress
    (occurrenceIdentityDomain Run Slot Generation EffectKind)
    (occurrenceQuotientAdequate Run Slot Generation EffectKind)
    ()
    (occurrenceClassCodec Run Slot Generation EffectKind)
    binding occurrence

/-- The quotient codec derives exactly the independently defined structured key. -/
theorem occurrence_canonical_bytes_eq_key
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x}
    (occurrence : Occurrence Run Slot Generation EffectKind) :
    canonicalBytes
        (occurrenceIdentityDomain Run Slot Generation EffectKind)
        (occurrenceQuotientAdequate Run Slot Generation EffectKind)
        ()
        (occurrenceClassCodec Run Slot Generation EffectKind)
        occurrence =
      occurrenceKey occurrence := by
  rfl

/--
RCC-27 concrete bridge: under the explicit digest-range injectivity premise,
typed occurrence-address equality is exactly logical-occurrence equality.
-/
theorem occurrence_address_exact
    {Run : Type u} {Slot : Type v} {Generation : Type w}
    {EffectKind : Type x} {Wire : Type y}
    (binding : OccurrenceDigestBinding Run Slot Generation EffectKind Wire)
    (injective : DigestInjectiveOnCanonicalRange binding)
    (left right : Occurrence Run Slot Generation EffectKind) :
    occurrenceAddress binding left = occurrenceAddress binding right ↔
      SameLogicalOccurrence left right := by
  change
    binding.address
        (canonicalBytes
          (occurrenceIdentityDomain Run Slot Generation EffectKind)
          (occurrenceQuotientAdequate Run Slot Generation EffectKind)
          ()
          (occurrenceClassCodec Run Slot Generation EffectKind)
          left) =
        binding.address
          (canonicalBytes
            (occurrenceIdentityDomain Run Slot Generation EffectKind)
            (occurrenceQuotientAdequate Run Slot Generation EffectKind)
            ()
            (occurrenceClassCodec Run Slot Generation EffectKind)
            right) ↔
      SameLogicalOccurrence left right
  rw [occurrence_canonical_bytes_eq_key, occurrence_canonical_bytes_eq_key]
  exact
    (digest_address_eq_iff_bytes_eq
      binding injective (occurrenceKey left) (occurrenceKey right)).trans
      (occurrence_key_exact left right)

end Residua.RCC.OccurrenceExactness

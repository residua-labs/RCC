import RCC.CanonicalCodec

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.CanonicalCodec.Tests

/-!
# RCC AK-2 exact canonical codec tests

These fixtures pin the value quotient at the codec boundary.  They reject both
omitting semantic data from bytes and including nonsemantic occurrence data.
-/

structure PaymentOccurrence where
  amount : Nat
  occurrence : Nat
  deriving DecidableEq, Repr

def paymentValueDomain : IdentityDomain .value where
  Object := PaymentOccurrence
  Context := Unit
  Observation := Nat
  equivalent := fun _ left right => left.amount = right.amount
  observe := fun _ payment => payment.amount

def paymentValueAdequate : QuotientAdequate paymentValueDomain where
  equivalence := fun _ => ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
  observe_sound := fun equivalent => equivalent

def paymentClassAmount :
    Quotient (paymentValueDomain.setoid paymentValueAdequate ()) → Nat :=
  Quotient.lift (fun payment => payment.amount) (by
    intro left right equivalent
    exact equivalent)

def paymentValueCodec :
    ExactCanonicalCodec
      (Quotient (paymentValueDomain.setoid paymentValueAdequate ())) Nat where
  encode := paymentClassAmount
  decode := fun amount =>
    some (qAbs paymentValueDomain paymentValueAdequate () ⟨amount, 0⟩)
  decode_encode := by
    intro paymentClass
    refine Quotient.inductionOn paymentClass ?_
    intro payment
    simp only [paymentClassAmount, qAbs]
    congr 1
    apply Quotient.sound
    rfl
  encode_decode_canonical := by
    intro bytes paymentClass accepted
    change some (qAbs paymentValueDomain paymentValueAdequate () ⟨bytes, 0⟩) =
      some paymentClass at accepted
    have classEquality :
        qAbs paymentValueDomain paymentValueAdequate () ⟨bytes, 0⟩ =
          paymentClass :=
      Option.some.inj accepted
    rw [← classEquality]
    rfl

/-- The payment codec decodes each canonical encoding back to its exact class. -/
theorem payment_codec_roundtrip (payment : PaymentOccurrence) :
    paymentValueCodec.decode
        (paymentValueCodec.encode
          (qAbs paymentValueDomain paymentValueAdequate () payment)) =
      some (qAbs paymentValueDomain paymentValueAdequate () payment) := by
  exact paymentValueCodec.decode_encode _

/-- Two accepted encodings for one payment value class must be byte-identical. -/
theorem payment_codec_accepted_bytes_unique {left right : Nat}
    {paymentClass : Quotient (paymentValueDomain.setoid paymentValueAdequate ())}
    (leftAccepted : paymentValueCodec.decode left = some paymentClass)
    (rightAccepted : paymentValueCodec.decode right = some paymentClass) :
    left = right := by
  exact canonical_decoding_has_unique_bytes paymentValueCodec
    leftAccepted rightAccepted

/-- Canonical payment bytes are equal exactly for equal declared values. -/
theorem payment_canonical_bytes_eq_iff_value_equivalent
    (left right : PaymentOccurrence) :
    canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec left =
        canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec right ↔
      paymentValueDomain.equivalent () left right := by
  exact canonical_bytes_eq_iff_equivalent paymentValueDomain paymentValueAdequate ()
    paymentValueCodec left right

/-! ## CM-ADDR-01: omitting a semantic field cannot be exact -/

def semanticFieldOmitted (_ : PaymentOccurrence) : Nat := 0

def p250 : PaymentOccurrence := ⟨250, 0⟩

def p500 : PaymentOccurrence := ⟨500, 0⟩

theorem cm_addr_01_omitted_field_has_equal_bytes :
    semanticFieldOmitted p250 = semanticFieldOmitted p500 := by
  rfl

theorem cm_addr_01_omitted_field_changes_the_value_class :
    ¬ paymentValueDomain.equivalent () p250 p500 := by
  change ¬ (250 : Nat) = 500
  decide

/-- Exact quotient codecs cannot assign equal bytes to distinct value classes. -/
theorem cm_addr_01_equal_bytes_contradict_exactness
    (codec :
      ExactCanonicalCodec
        (Quotient (paymentValueDomain.setoid paymentValueAdequate ())) Nat)
    (equalBytes :
      codec.encode (qAbs paymentValueDomain paymentValueAdequate () p250) =
        codec.encode (qAbs paymentValueDomain paymentValueAdequate () p500)) :
    False := by
  apply cm_addr_01_omitted_field_changes_the_value_class
  apply (qAbs_eq_iff_equivalent
    paymentValueDomain paymentValueAdequate () p250 p500).1
  exact canonical_encode_injective codec equalBytes

/-! ## CM-ADDR-02: including a nonsemantic field cannot factor through value -/

def nonsemanticFieldIncluded (payment : PaymentOccurrence) : Nat :=
  payment.occurrence

def first : PaymentOccurrence := ⟨250, 0⟩

def retry : PaymentOccurrence := ⟨250, 1⟩

theorem cm_addr_02_values_are_equivalent :
    paymentValueDomain.equivalent () first retry := by
  rfl

theorem cm_addr_02_nonsemantic_field_changes :
    nonsemanticFieldIncluded first ≠ nonsemanticFieldIncluded retry := by
  decide

theorem cm_addr_02_nonsemantic_field_does_not_factor :
    ¬ ConsumerFactorsThroughQuotient
      paymentValueDomain () nonsemanticFieldIncluded := by
  intro factors
  exact cm_addr_02_nonsemantic_field_changes
    (factors cm_addr_02_values_are_equivalent)

/-- An exact quotient codec gives retry occurrences of one value equal bytes. -/
theorem cm_addr_02_exact_codec_identifies_equal_values :
    canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec first =
      canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec retry := by
  exact
    (payment_canonical_bytes_eq_iff_value_equivalent first retry).2
      cm_addr_02_values_are_equivalent

end Residua.RCC.Addressing.CanonicalCodec.Tests


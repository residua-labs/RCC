import RCCTests.CanonicalCodec

/-! RCC-100 candidate: exact canonical codec and semantic-field discipline. -/

namespace Residua.RCC.RCC100Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.CanonicalCodec.Tests

theorem paymentCodecRoundtrip (payment : PaymentOccurrence) :
    paymentValueCodec.decode
        (paymentValueCodec.encode
          (qAbs paymentValueDomain paymentValueAdequate () payment)) =
      some (qAbs paymentValueDomain paymentValueAdequate () payment) :=
  payment_codec_roundtrip payment

theorem paymentAcceptedBytesUnique {left right : Nat}
    {paymentClass : Quotient (paymentValueDomain.setoid paymentValueAdequate ())}
    (leftAccepted : paymentValueCodec.decode left = some paymentClass)
    (rightAccepted : paymentValueCodec.decode right = some paymentClass) :
    left = right :=
  payment_codec_accepted_bytes_unique leftAccepted rightAccepted

theorem paymentCanonicalBytesExact (left right : PaymentOccurrence) :
    canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec left =
        canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec right ↔
      paymentValueDomain.equivalent () left right :=
  payment_canonical_bytes_eq_iff_value_equivalent left right

def omittedSemanticFieldCollapses := cm_addr_01_omitted_field_has_equal_bytes
def omittedSemanticFieldRefused := cm_addr_01_equal_bytes_contradict_exactness
def valueClassesDiffer := cm_addr_01_omitted_field_changes_the_value_class
def nonsemanticFieldChanges := cm_addr_02_nonsemantic_field_changes
def nonsemanticFieldNotFactorable := cm_addr_02_nonsemantic_field_does_not_factor
def exactCodecIdentifiesEqualValues := cm_addr_02_exact_codec_identifies_equal_values

abbrev PaymentCodecRoundtrip : Prop :=
  ∀ payment : PaymentOccurrence,
    paymentValueCodec.decode
        (paymentValueCodec.encode
          (qAbs paymentValueDomain paymentValueAdequate () payment)) =
      some (qAbs paymentValueDomain paymentValueAdequate () payment)
abbrev PaymentAcceptedBytesUnique : Prop :=
  ∀ {left right : Nat}
    {paymentClass : Quotient (paymentValueDomain.setoid paymentValueAdequate ())},
    paymentValueCodec.decode left = some paymentClass →
    paymentValueCodec.decode right = some paymentClass →
    left = right
abbrev PaymentCanonicalBytesExact : Prop :=
  ∀ (left right : PaymentOccurrence),
    canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec left =
        canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec right ↔
      paymentValueDomain.equivalent () left right
abbrev OmittedSemanticFieldCollapses : Prop :=
  semanticFieldOmitted p250 = semanticFieldOmitted p500
abbrev OmittedSemanticFieldRefused : Prop :=
  ∀ (codec :
      ExactCanonicalCodec
        (Quotient (paymentValueDomain.setoid paymentValueAdequate ())) Nat)
    (equalBytes :
      codec.encode (qAbs paymentValueDomain paymentValueAdequate () p250) =
        codec.encode (qAbs paymentValueDomain paymentValueAdequate () p500)),
    False
abbrev ValueClassesDiffer : Prop :=
  ¬ paymentValueDomain.equivalent () p250 p500
abbrev NonsemanticFieldChanges : Prop :=
  nonsemanticFieldIncluded first ≠ nonsemanticFieldIncluded retry
abbrev NonsemanticFieldNotFactorable : Prop :=
  ¬ ConsumerFactorsThroughQuotient
      paymentValueDomain () nonsemanticFieldIncluded
abbrev ExactCodecIdentifiesEqualValues : Prop :=
  canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec first =
    canonicalBytes paymentValueDomain paymentValueAdequate () paymentValueCodec retry

structure Certificate where
  paymentCodecRoundtrip : PaymentCodecRoundtrip
  paymentAcceptedBytesUnique : PaymentAcceptedBytesUnique
  paymentCanonicalBytesExact : PaymentCanonicalBytesExact
  omittedSemanticFieldCollapses : OmittedSemanticFieldCollapses
  omittedSemanticFieldRefused : OmittedSemanticFieldRefused
  valueClassesDiffer : ValueClassesDiffer
  nonsemanticFieldChanges : NonsemanticFieldChanges
  nonsemanticFieldNotFactorable : NonsemanticFieldNotFactorable
  exactCodecIdentifiesEqualValues : ExactCodecIdentifiesEqualValues

def certificate : Certificate where
  paymentCodecRoundtrip := paymentCodecRoundtrip
  paymentAcceptedBytesUnique := paymentAcceptedBytesUnique
  paymentCanonicalBytesExact := paymentCanonicalBytesExact
  omittedSemanticFieldCollapses := cm_addr_01_omitted_field_has_equal_bytes
  omittedSemanticFieldRefused := cm_addr_01_equal_bytes_contradict_exactness
  valueClassesDiffer := cm_addr_01_omitted_field_changes_the_value_class
  nonsemanticFieldChanges := cm_addr_02_nonsemantic_field_changes
  nonsemanticFieldNotFactorable := cm_addr_02_nonsemantic_field_does_not_factor
  exactCodecIdentifiesEqualValues := cm_addr_02_exact_codec_identifies_equal_values

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC100Target

import RCC.AddressQuotient

/-!
# RCC exact canonical codec

An exact canonical codec is a bijection between quotient classes and the
accepted byte representations.  This module derives only the quotient-level
injectivity and exactness laws needed by AK-2.
-/

namespace Residua.RCC.Addressing

universe u v

/-- An exact encoder/decoder whose accepted encodings are canonical. -/
structure ExactCanonicalCodec (Class : Type u) (Bytes : Type v) where
  encode : Class → Bytes
  decode : Bytes → Option Class
  decode_encode : ∀ q, decode (encode q) = some q
  encode_decode_canonical :
    ∀ b q, decode b = some q → encode q = b

/--
Exact decoding makes the canonical encoder injective.  The injectivity
predicate is written out because Lean 4.14's `Init` does not yet export
`Function.Injective`; it is the same predicate under later Prelude versions.
-/
theorem canonical_encode_injective
    (codec : ExactCanonicalCodec Class Bytes) :
    ∀ ⦃left right⦄, codec.encode left = codec.encode right → left = right := by
  intro left right equalEncoding
  have equalDecoded := congrArg codec.decode equalEncoding
  rw [codec.decode_encode left, codec.decode_encode right] at equalDecoded
  exact Option.some.inj equalDecoded

/-- A decoded class has only one accepted canonical byte representation. -/
theorem canonical_decoding_has_unique_bytes
    (codec : ExactCanonicalCodec Class Bytes)
    {left right : Bytes} {q : Class}
    (leftAccepted : codec.decode left = some q)
    (rightAccepted : codec.decode right = some q) :
    left = right := by
  rw [← codec.encode_decode_canonical left q leftAccepted]
  exact codec.encode_decode_canonical right q rightAccepted

/-- Encode an object only after abstracting it into its declared class. -/
def canonicalBytes {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context)
    (codec :
      ExactCanonicalCodec
        (Quotient (domain.setoid adequate context)) Bytes)
    (object : domain.Object) : Bytes :=
  codec.encode (qAbs domain adequate context object)

/-- Canonical bytes are equal exactly on the declared quotient relation. -/
theorem canonical_bytes_eq_iff_equivalent {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context)
    (codec :
      ExactCanonicalCodec
        (Quotient (domain.setoid adequate context)) Bytes)
    (left right : domain.Object) :
    canonicalBytes domain adequate context codec left =
        canonicalBytes domain adequate context codec right ↔
      domain.equivalent context left right := by
  constructor
  · intro equalBytes
    apply (qAbs_eq_iff_equivalent domain adequate context left right).1
    apply canonical_encode_injective codec
    exact equalBytes
  · intro equivalent
    apply congrArg codec.encode
    exact
      (qAbs_eq_iff_equivalent domain adequate context left right).2 equivalent

end Residua.RCC.Addressing

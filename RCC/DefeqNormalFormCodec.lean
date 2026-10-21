import RCC.CanonicalCodec
import RCC.DefeqExactness

/-!
# RCC canonical codec for num/add normal forms

This file establishes DQ-6 for the `NumAddNormalForm` carrier produced by
DQ-2 and proved unique in DQ-5.  It supplies an exact, unambiguous octet
codec:

* the first octet is a disjoint nonnegative/negative sign tag;
* the remaining octets are a unary magnitude payload;
* the decoder accepts only the distinguished magnitude octet;
* decoding an encoding returns the original normal form;
* every accepted byte string is exactly the canonical re-encoding of the
  decoded normal form;
* consequently the encoder is injective.

The unary payload is intentionally small and proof-transparent.  DQ-6 is
about codec exactness, not compression.  This file does not construct a
typed address, apply a digest, or claim digest exactness; those remain DQ-7
and DQ-8.
-/

namespace Residua.RCC.DefeqNormalFormCodec

open Residua.RCC.Addressing
open Residua.RCC.DefeqNormalizer

/-! ## Frozen octet grammar -/

/-- Canonical bytes for the DQ-6 normal-form wire grammar. -/
abbrev NormalFormBytes := List UInt8

/-- Tag for `Int.ofNat`. -/
def nonnegativeTag : UInt8 := 0

/-- Tag for `Int.negSucc`. -/
def negativeTag : UInt8 := 1

/-- The sole octet accepted in a unary magnitude payload. -/
def magnitudeUnit : UInt8 := 2

/-- Encode a natural magnitude as exactly `n` distinguished payload octets. -/
def encodeMagnitude (magnitude : Nat) : NormalFormBytes :=
  List.replicate magnitude magnitudeUnit

/-- Decode the strict unary magnitude grammar.  Any other octet is refused. -/
def decodeMagnitude : NormalFormBytes → Option Nat
  | [] =>
      some 0
  | octet :: rest =>
      if octet = magnitudeUnit then
        match decodeMagnitude rest with
        | some magnitude => some (magnitude + 1)
        | none => none
      else
        none

/-- The strict magnitude decoder is a left inverse of its encoder. -/
@[simp]
theorem decodeMagnitude_encodeMagnitude (magnitude : Nat) :
    decodeMagnitude (encodeMagnitude magnitude) = some magnitude := by
  induction magnitude with
  | zero =>
      rfl
  | succ magnitude inductionHypothesis =>
      change
        decodeMagnitude (magnitudeUnit :: encodeMagnitude magnitude) =
          some (magnitude + 1)
      simp [decodeMagnitude, inductionHypothesis]

/-- Every accepted magnitude payload is already the unique canonical unary
encoding of the decoded magnitude. -/
theorem encodeMagnitude_decodeMagnitude_canonical
    (bytes : NormalFormBytes)
    (magnitude : Nat)
    (accepted : decodeMagnitude bytes = some magnitude) :
    encodeMagnitude magnitude = bytes := by
  induction bytes generalizing magnitude with
  | nil =>
      simp [decodeMagnitude] at accepted
      cases accepted
      rfl
  | cons octet rest inductionHypothesis =>
      simp only [decodeMagnitude] at accepted
      split at accepted
      next octetIsUnit =>
        cases decodedRest : decodeMagnitude rest with
        | none =>
            simp [decodedRest] at accepted
        | some restMagnitude =>
            simp [decodedRest] at accepted
            cases accepted
            rw [encodeMagnitude, List.replicate_succ]
            congr 1
            · exact Eq.symm octetIsUnit
            · exact
                inductionHypothesis restMagnitude decodedRest
      next octetIsNotUnit =>
        simp at accepted

/-! ## Exact normal-form codec -/

/-- Encode a canonical normal form with a disjoint sign tag and strict
magnitude payload.  `negSucc n` encodes the negative integer `-(n+1)`, so the
two sign branches are disjoint even at zero payload length. -/
def encode : NumAddNormalForm → NormalFormBytes
  | .int (.ofNat magnitude) =>
      nonnegativeTag :: encodeMagnitude magnitude
  | .int (.negSucc magnitude) =>
      negativeTag :: encodeMagnitude magnitude

/-- Decode only the frozen DQ-6 canonical byte grammar. -/
def decode : NormalFormBytes → Option NumAddNormalForm
  | [] =>
      none
  | tag :: payload =>
      match decodeMagnitude payload with
      | none =>
          none
      | some magnitude =>
          if tag = nonnegativeTag then
            some (.int (.ofNat magnitude))
          else if tag = negativeTag then
            some (.int (.negSucc magnitude))
          else
            none

/-- DQ-6 roundtrip: every canonical normal form survives encoding and
decoding exactly. -/
@[simp]
theorem decode_encode (normalForm : NumAddNormalForm) :
    decode (encode normalForm) = some normalForm := by
  cases normalForm with
  | int value =>
      cases value with
      | ofNat magnitude =>
          simp [encode, decode, nonnegativeTag]
      | negSucc magnitude =>
          simp [encode, decode, nonnegativeTag, negativeTag]

/-- DQ-6 canonical decoding: the decoder accepts no alternate byte string
for a normal form. -/
theorem encode_decode_canonical
    (bytes : NormalFormBytes)
    (normalForm : NumAddNormalForm)
    (accepted : decode bytes = some normalForm) :
    encode normalForm = bytes := by
  cases bytes with
  | nil =>
      simp [decode] at accepted
  | cons tag payload =>
      simp only [decode] at accepted
      cases decodedMagnitude : decodeMagnitude payload with
      | none =>
          simp [decodedMagnitude] at accepted
      | some magnitude =>
          simp [decodedMagnitude] at accepted
          split at accepted
          next isNonnegative =>
            cases accepted
            simp only [encode]
            congr 1
            · exact Eq.symm isNonnegative
            · exact
                encodeMagnitude_decodeMagnitude_canonical
                  payload magnitude decodedMagnitude
          next isNotNonnegative =>
            split at accepted
            next isNegative =>
              cases accepted
              simp only [encode]
              congr 1
              · exact Eq.symm isNegative
              · exact
                  encodeMagnitude_decodeMagnitude_canonical
                    payload magnitude decodedMagnitude
            next isNotNegative =>
              simp at accepted

/-- The DQ-6 codec packaged as the generic RCC exact canonical-codec
contract. -/
def exactCodec :
    ExactCanonicalCodec NumAddNormalForm NormalFormBytes where
  encode := encode
  decode := decode
  decode_encode := decode_encode
  encode_decode_canonical := encode_decode_canonical

/-- Canonical normal-form bytes are injective. -/
theorem encode_injective :
    ∀ ⦃left right : NumAddNormalForm⦄,
      encode left = encode right → left = right := by
  exact canonical_encode_injective exactCodec

/-- Two accepted byte strings for one normal form are byte-identical. -/
theorem accepted_bytes_unique
    {left right : NormalFormBytes}
    {normalForm : NumAddNormalForm}
    (leftAccepted : decode left = some normalForm)
    (rightAccepted : decode right = some normalForm) :
    left = right := by
  exact
    canonical_decoding_has_unique_bytes
      exactCodec leftAccepted rightAccepted

end Residua.RCC.DefeqNormalFormCodec

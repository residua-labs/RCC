import RCC.DefeqNormalFormCodec

/-!
# Tests and load-bearing mutants for DQ-6

The positive witnesses exercise both signed branches, exact roundtrip,
canonical decoding, and encoder injectivity.  The mutants expose:

* ambiguous framing that omits the sign tag and merges `0` with `-1`;
* a permissive decoder that accepts arbitrary payload octets, so alternate
  bytes decode to the same normal form.
-/

namespace Residua.RCC.DefeqNormalFormCodec.Tests

open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqNormalFormCodec

/-! ## Positive witnesses -/

theorem positive_roundtrip :
    decode (encode (.int 3)) = some (.int 3) := by
  rfl

theorem negative_roundtrip :
    decode (encode (.int (-4))) = some (.int (-4)) := by
  rfl

theorem empty_bytes_refused :
    decode [] = none := by
  rfl

theorem unknown_tag_refused :
    decode [3] = none := by
  rfl

theorem malformed_payload_refused :
    decode [nonnegativeTag, 9] = none := by
  rfl

theorem concrete_canonical_decoding :
    ∀ bytes,
      decode bytes = some (.int 2) →
      bytes = [nonnegativeTag, magnitudeUnit, magnitudeUnit] := by
  intro bytes accepted
  exact Eq.symm (encode_decode_canonical bytes (.int 2) accepted)

theorem concrete_encoder_injective
    {left right : NumAddNormalForm}
    (sameBytes : encode left = encode right) :
    left = right := by
  exact encode_injective sameBytes

/-! ## Mutant 1: signless framing is ambiguous -/

/-- Forbidden encoder: omitting the sign tag collapses equal magnitudes from
the two disjoint `Int` branches. -/
def signlessEncodingMutant : NumAddNormalForm → NormalFormBytes
  | .int (.ofNat magnitude) =>
      encodeMagnitude magnitude
  | .int (.negSucc magnitude) =>
      encodeMagnitude magnitude

theorem signless_framing_mutant_exposed :
    signlessEncodingMutant (.int 0) =
        signlessEncodingMutant (.int (-1)) ∧
      (.int 0 : NumAddNormalForm) ≠ .int (-1) := by
  decide

/-! ## Mutant 2: permissive payload decoding admits alternate bytes -/

/-- Forbidden decoder: it treats every payload octet as a magnitude unit
instead of checking the frozen payload grammar. -/
def permissiveDecodeMutant : NormalFormBytes → Option NumAddNormalForm
  | [] =>
      none
  | tag :: payload =>
      if tag = nonnegativeTag then
        some (.int (.ofNat payload.length))
      else if tag = negativeTag then
        some (.int (.negSucc payload.length))
      else
        none

def canonicalOneBytes : NormalFormBytes :=
  [nonnegativeTag, magnitudeUnit]

def alternateOneBytes : NormalFormBytes :=
  [nonnegativeTag, 9]

theorem permissive_decoder_mutant_exposed :
    canonicalOneBytes ≠ alternateOneBytes ∧
      permissiveDecodeMutant canonicalOneBytes = some (.int 1) ∧
      permissiveDecodeMutant alternateOneBytes = some (.int 1) ∧
      decode canonicalOneBytes = some (.int 1) ∧
      decode alternateOneBytes = none := by
  decide

#print axioms decodeMagnitude_encodeMagnitude
#print axioms encodeMagnitude_decodeMagnitude_canonical
#print axioms decode_encode
#print axioms encode_decode_canonical
#print axioms encode_injective
#print axioms accepted_bytes_unique
#print axioms signless_framing_mutant_exposed
#print axioms permissive_decoder_mutant_exposed

end Residua.RCC.DefeqNormalFormCodec.Tests

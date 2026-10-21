import RCC.AddressKernel

/-!
# RCC-0 AddressKernel tests

The positive fixture has a one-element quotient and a constant consumer.  The
negative fixture uses a universal quotient with a non-constant consumer; its
consumer-factorization certificate is provably unavailable.
-/

namespace Residua.RCC.Addressing.AddressKernel.Tests

open Residua.RCC.Addressing

universe u

def UnitDomain : IdentityDomain .value where
  Object := Unit
  Context := Unit
  Observation := Unit
  equivalent := fun _ _ _ => True
  observe := fun _ _ => ()

def unitAdequate : QuotientAdequate UnitDomain where
  equivalence := by
    intro _
    exact {
      refl := fun _ => trivial
      symm := by
        intro _ _ _
        trivial
      trans := by
        intro _ _ _ _ _
        trivial
    }
  observe_sound := by
    intro _ _ _ _
    rfl

abbrev UnitClass :=
  Quotient (UnitDomain.setoid unitAdequate ())

def unitCodec : ExactCanonicalCodec UnitClass UnitClass where
  encode := id
  decode := some
  decode_encode := by intro q; rfl
  encode_decode_canonical := by
    intro _ q decoded
    cases decoded
    rfl

def unitFrame : ExactFrame UnitClass (DigestPreimage UnitClass) where
  encode := id
  encode_injective := by
    intro left right equal
    exact equal

def unitDigest : DigestBinding .value UnitClass (DigestPreimage UnitClass) where
  algorithm := ⟨"unit-test-hash"⟩
  domainQ := ⟨"unit-test-value"⟩
  schemaQ := ⟨"unit-test-value:v1"⟩
  frame := unitFrame
  hash := fun _ => ⟨"unit-test-digest"⟩

theorem unit_digest_injective :
    DigestInjectiveOnCanonicalRange unitDigest := by
  intro left right _
  have classEqual : left = right := by
    refine Quotient.inductionOn left (fun leftRep => ?_)
    refine Quotient.inductionOn right (fun rightRep => ?_)
    exact Quotient.sound trivial
  cases classEqual
  rfl

def unitKernel : AddressKernel UnitDomain () Nat UnitClass
    (DigestPreimage UnitClass) where
  adequate := unitAdequate
  codec := unitCodec
  digest := unitDigest
  digestInjective := unit_digest_injective
  consumer := fun _ => 0
  consumerFactors := by
    intro _ _ _
    rfl

theorem unit_kernel_substitutes_by_address (left right : Unit) :
    unitKernel.address left = unitKernel.address right →
      unitKernel.consumer left = unitKernel.consumer right := by
  intro equalAddress
  exact unitKernel.consumer_substitutability equalAddress

/-! A non-degenerate two-class fixture for address exactness. -/

def TwoClassDomain : IdentityDomain .value where
  Object := Bool
  Context := Unit
  Observation := Bool
  equivalent := fun _ left right => left = right
  observe := fun _ value => value

def twoClassAdequate : QuotientAdequate TwoClassDomain where
  equivalence := by
    intro _
    exact {
      refl := by intro value; rfl
      symm := by intro left right equal; exact equal.symm
      trans := by
        intro left middle right leftMiddle middleRight
        exact leftMiddle.trans middleRight
    }
  observe_sound := by
    intro _ left right equal
    exact equal

abbrev TwoClass :=
  Quotient (TwoClassDomain.setoid twoClassAdequate ())

def twoClassEncode : TwoClass → Bool :=
  Quotient.lift id (by
    intro left right equal
    exact equal)

def twoClassDecode : Bool → Option TwoClass :=
  fun value => some (Quotient.mk _ value)

def twoClassCodec : ExactCanonicalCodec TwoClass Bool where
  encode := twoClassEncode
  decode := twoClassDecode
  decode_encode := by
    intro q
    refine Quotient.inductionOn q (fun value => ?_)
    rfl
  encode_decode_canonical := by
    intro value q decoded
    simp [twoClassDecode] at decoded
    cases decoded
    rfl

def twoClassFrame : ExactFrame Bool (DigestPreimage Bool) where
  encode := fun preimage => preimage
  encode_injective := by
    intro left right equal
    exact equal

def twoClassDigest : DigestBinding .value Bool (DigestPreimage Bool) where
  algorithm := ⟨"two-class-test-hash"⟩
  domainQ := ⟨"two-class-value"⟩
  schemaQ := ⟨"two-class-value:v1"⟩
  frame := twoClassFrame
  hash := fun preimage => ⟨if preimage.canonicalBytes then "true" else "false"⟩

theorem twoClass_digest_injective :
    DigestInjectiveOnCanonicalRange twoClassDigest := by
  intro left right equal
  cases left <;> cases right <;>
    simp [twoClassDigest, DigestBinding.framedWire, twoClassFrame] at equal ⊢

def twoClassKernel : AddressKernel TwoClassDomain () Bool Bool
    (DigestPreimage Bool) where
  adequate := twoClassAdequate
  codec := twoClassCodec
  digest := twoClassDigest
  digestInjective := twoClass_digest_injective
  consumer := id
  consumerFactors := by
    intro left right equal
    exact equal

theorem twoClass_kernel_address_exact (left right : Bool) :
    twoClassKernel.address left = twoClassKernel.address right ↔
      left = right := by
  exact twoClassKernel.address_eq_iff_equivalent left right

theorem twoClass_kernel_consumer_exact (left right : Bool) :
    twoClassKernel.address left = twoClassKernel.address right →
      twoClassKernel.consumer left = twoClassKernel.consumer right := by
  intro equalAddress
  exact twoClassKernel.consumer_substitutability equalAddress

theorem twoClass_kernel_separates_classes :
    twoClassKernel.address false ≠ twoClassKernel.address true := by
  intro equalAddress
  have equalValues : false = true :=
    (twoClassKernel.address_eq_iff_equivalent false true).1 equalAddress
  cases equalValues

/-! A consumer that distinguishes equivalent objects cannot be certified. -/

def BooleanDomain : IdentityDomain .value where
  Object := Bool
  Context := Unit
  Observation := Unit
  equivalent := fun _ _ _ => True
  observe := fun _ _ => ()

theorem nonconstant_consumer_not_factorable :
    ¬ ConsumerFactorsThroughQuotient
      BooleanDomain () (fun value : Bool => value) := by
  intro factors
  have same : BooleanDomain.equivalent () false true := trivial
  have equalValues : false = true := factors same
  cases equalValues

end Residua.RCC.Addressing.AddressKernel.Tests

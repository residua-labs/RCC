import RCC.AddressResolution
import RCC.AddressUseRegistry
import RCC.AddressSchemeTransport

/-!
# RCC-0 AddressKernel

The RCC-0 safety triangle is now one reusable object rather than three
unrelated premises:

* `QuotientAdequate` chooses the identity relation;
* `ExactCanonicalCodec` realizes its quotient classes as canonical bytes;
* `DigestBinding` gives those bytes a typed, framed address; and
* `ConsumerFactorsThroughQuotient` proves the consumer is allowed to use that
  address as its sole identity input.

The digest injectivity premise is explicit and domain-indexed.  No concrete
hash is treated as mathematically injective by this file.  Store resolution,
collision refusal, registry coverage, and scheme transport remain additional
use-site certificates consumed by the surrounding RCC-0 gate.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.Addressing

universe u v w z

structure AddressKernel
    {kind : AddressKind}
    (domain : IdentityDomain kind)
    (context : domain.Context)
    (Result : Type z) (Bytes : Type u) (Wire : Type v) where
  adequate : QuotientAdequate domain
  codec :
    ExactCanonicalCodec
      (Quotient (domain.setoid adequate context)) Bytes
  digest : DigestBinding kind Bytes Wire
  digestInjective : DigestInjectiveOnCanonicalRange digest
  consumer : domain.Object → Result
  consumerFactors :
    ConsumerFactorsThroughQuotient domain context consumer

def AddressKernel.address
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    (kernel : AddressKernel domain context Result Bytes Wire)
    (object : domain.Object) : Address kind :=
  canonicalObjectAddress domain kernel.adequate context kernel.codec
    kernel.digest object

theorem AddressKernel.address_eq_iff_equivalent
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    (kernel : AddressKernel domain context Result Bytes Wire)
    (left right : domain.Object) :
    kernel.address left = kernel.address right ↔
      domain.equivalent context left right := by
  exact canonical_object_address_eq_iff_equivalent
    domain kernel.adequate context kernel.codec kernel.digest
      kernel.digestInjective left right

theorem AddressKernel.consumer_substitutability
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    (kernel : AddressKernel domain context Result Bytes Wire)
    {left right : domain.Object}
    (equalAddress : kernel.address left = kernel.address right) :
    kernel.consumer left = kernel.consumer right := by
  exact typed_address_substitutability
    domain kernel.adequate context kernel.address kernel.consumer
      (fun {left right} equal =>
        (kernel.address_eq_iff_equivalent left right).1 equal)
      kernel.consumerFactors equalAddress

theorem AddressKernel.quotient_identity_is_exact
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    (kernel : AddressKernel domain context Result Bytes Wire)
    (left right : domain.Object) :
    kernel.address left = kernel.address right ↔
      domain.equivalent context left right ∧
        kernel.consumer left = kernel.consumer right := by
  constructor
  · intro equalAddress
    exact ⟨(kernel.address_eq_iff_equivalent left right).1 equalAddress,
      kernel.consumer_substitutability equalAddress⟩
  · rintro ⟨equivalent, _consumerEqual⟩
    exact (kernel.address_eq_iff_equivalent left right).2 equivalent

end Residua.RCC.Addressing


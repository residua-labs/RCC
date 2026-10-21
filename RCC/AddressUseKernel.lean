import RCC.AddressKernel
import RCC.AddressUseRegistry

/-!
# RCC-0 address-use kernel

`AddressKernel` proves that one address domain is safe to use.  The sealed
use registry proves that every q-bearing field in an epoch's declared surface
actually supplies the required typed envelope, consumer-factorization, and
collision-policy evidence.  This adapter combines the two without allowing an
instance to report registry completeness directly: completeness is still the
derived fold over the sealed universe.

Prelude-only Lean 4.14; no proof placeholders.
-/

namespace Residua.RCC.Addressing

open AddressUseRegistry

universe u v w z

structure AddressUseKernel
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    (base : AddressKernel domain context Result Bytes Wire)
    (TypedEnvelopeCertificate : AddressUseRequirement → Type w)
    (ConsumerFactorizationCertificate : AddressUseRequirement → Type w)
    (CollisionPolicyCertificate : AddressUseRequirement → Type w) where
  boundRequirement : AddressUseRequirement
  kindBound : boundRequirement.kind = kind
  domainBound : boundRequirement.domainQ = base.digest.domainQ
  schemaBound : boundRequirement.schemaQ = base.digest.schemaQ
  sealedUniverse : SealedAddressUseUniverse
  registry :
    AddressUseRegistry
      TypedEnvelopeCertificate
      ConsumerFactorizationCertificate
      CollisionPolicyCertificate
  derivedComplete :
    assessAddressUseRegistry sealedUniverse registry =
      AddressUseRegistryAssessment.complete

theorem AddressUseKernel.every_declared_use_justified
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    {base : AddressKernel domain context Result Bytes Wire}
    {TypedEnvelopeCertificate : AddressUseRequirement → Type w}
    {ConsumerFactorizationCertificate : AddressUseRequirement → Type w}
    {CollisionPolicyCertificate : AddressUseRequirement → Type w}
    (kernel :
      AddressUseKernel base
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate)
    (requirement : AddressUseRequirement)
    (inUniverse : kernel.sealedUniverse.InUniverse requirement) :
    assessAddressUse kernel.registry requirement =
      AddressUseAssessment.justified := by
  exact complete_registry_justifies_every_use
    kernel.sealedUniverse kernel.registry kernel.derivedComplete
      requirement inUniverse

theorem AddressUseKernel.complete_is_derived
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    {base : AddressKernel domain context Result Bytes Wire}
    {TypedEnvelopeCertificate : AddressUseRequirement → Type w}
    {ConsumerFactorizationCertificate : AddressUseRequirement → Type w}
    {CollisionPolicyCertificate : AddressUseRequirement → Type w}
    (kernel :
      AddressUseKernel base
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) :
    assessAddressUseRegistry kernel.sealedUniverse kernel.registry =
      AddressUseRegistryAssessment.complete :=
  kernel.derivedComplete

theorem AddressUseKernel.bound_requirement_matches_base
    {kind : AddressKind}
    {domain : IdentityDomain kind}
    {context : domain.Context}
    {Result : Type z} {Bytes : Type u} {Wire : Type v}
    {base : AddressKernel domain context Result Bytes Wire}
    {TypedEnvelopeCertificate : AddressUseRequirement → Type w}
    {ConsumerFactorizationCertificate : AddressUseRequirement → Type w}
    {CollisionPolicyCertificate : AddressUseRequirement → Type w}
    (kernel :
      AddressUseKernel base
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) :
    kernel.boundRequirement.kind = kind ∧
      kernel.boundRequirement.domainQ = base.digest.domainQ ∧
      kernel.boundRequirement.schemaQ = base.digest.schemaQ :=
  ⟨kernel.kindBound, kernel.domainBound, kernel.schemaBound⟩

end Residua.RCC.Addressing

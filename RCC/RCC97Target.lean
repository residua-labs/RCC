import RCCTests.AddressKernel

/-! RCC-97 candidate: AddressKernel quotient and consumer-factorization laws. -/

namespace Residua.RCC.RCC97Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressKernel.Tests

theorem twoClassDigestInjective :
    DigestInjectiveOnCanonicalRange twoClassDigest :=
  twoClass_digest_injective
def nonconstantConsumerRefused := nonconstant_consumer_not_factorable

theorem twoClassKernelSubstitutesByAddress (left right : Bool) :
    twoClassKernel.address left = twoClassKernel.address right →
      twoClassKernel.consumer left = twoClassKernel.consumer right := by
  intro equalAddress
  exact twoClassKernel.consumer_substitutability equalAddress

theorem twoClassKernelSeparatesClasses :
    twoClassKernel.address false ≠ twoClassKernel.address true := by
  intro equalAddress
  have equalValues : false = true :=
    (twoClassKernel.address_eq_iff_equivalent false true).1 equalAddress
  cases equalValues

abbrev NonconstantConsumerRefused : Prop :=
  ¬ ConsumerFactorsThroughQuotient
      BooleanDomain () (fun value : Bool => value)

structure Certificate where
  twoClassDigestInjective : DigestInjectiveOnCanonicalRange twoClassDigest
  nonconstantConsumerRefused : NonconstantConsumerRefused
  twoClassKernelSubstitutesByAddress :
    ∀ left right : Bool,
      twoClassKernel.address left = twoClassKernel.address right →
        twoClassKernel.consumer left = twoClassKernel.consumer right
  twoClassKernelSeparatesClasses :
    twoClassKernel.address false ≠ twoClassKernel.address true

def certificate : Certificate where
  twoClassDigestInjective := twoClassDigestInjective
  nonconstantConsumerRefused := nonconstant_consumer_not_factorable
  twoClassKernelSubstitutesByAddress := twoClassKernelSubstitutesByAddress
  twoClassKernelSeparatesClasses := twoClassKernelSeparatesClasses

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC97Target

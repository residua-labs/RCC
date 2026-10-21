import RCC.KeyRoleSeparation
import RCCTests.KeyRoleSeparation

/-!
# RCC-26 target package

This independently buildable candidate packages the typed key-role criterion.
It separates content, occurrence, and finer identity kernels, and includes the
anti-mutants for using content identity as occurrence identity or treating
coincident role relations as sufficient for an arbitrary key.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC26Target

open Residua.RCC.KeyRoles
open Residua.RCC.KeyRoles.Tests

universe u v w

theorem generic_exact_roles_imply_safe
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {roles : List Role} {key : Object → Key}
    (exact : KeyExactForRoles system roles key) :
    KeyKernelIncludedForRoles system roles key :=
  key_exact_for_roles_implies_kernel_inclusion system exact

theorem generic_one_key_multi_role_criterion
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {roles : List Role} {key : Object → Key}
    (exact : KeyExactForRoles system roles key)
    {first second : Role}
    (firstMember : first ∈ roles) (secondMember : second ∈ roles) :
    RoleRelationsCoincide system first second :=
  one_key_multi_role_criterion system exact firstMember secondMember

structure ConcreteWitness : Prop where
  identicalContentDistinctOccurrences :
    paymentRoles.equivalent .content firstPayment secondPayment ∧
      ¬ paymentRoles.equivalent .occurrence firstPayment secondPayment
  contentKeyExactForContent :
    KeyExactForRole paymentRoles .content paymentContentKey
  contentKeyUnsafeForOccurrence :
    ¬ KeySafeForRole paymentRoles .occurrence paymentContentKey
  finerIdentityKeySafeForBoth :
    KeyKernelIncludedForRoles
      paymentRoles [.content, .occurrence] paymentIdentityKey
  exactnessForCoincidentRoles :
    KeyExactForRoles computationRoles replayAndCacheRoles
      computationContentKey
  roleRelationsCoincide :
    RoleRelationsCoincide computationRoles .replay .cache

structure MutantRefusal : Prop where
  oneKeyCannotBeExactForDistinctPaymentRoles :
    ∀ key : Payment → Nat,
      ¬ KeyExactForRoles paymentRoles [.content, .occurrence] key
  arbitraryKeyNotExactForCoincidentRoles :
    ¬ KeyExactForRoles
      computationRoles replayAndCacheRoles constantComputationKey

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { identicalContentDistinctOccurrences :=
        two_identical_payments_separate_roles
      contentKeyExactForContent := payment_content_key_exact_for_content
      contentKeyUnsafeForOccurrence := payment_content_key_unsafe_for_occurrence
      finerIdentityKeySafeForBoth := payment_identity_key_safe_for_both_roles
      exactnessForCoincidentRoles := one_key_multi_role_safe_positive
      roleRelationsCoincide := replay_and_cache_relations_coincide }
  mutants :=
    { oneKeyCannotBeExactForDistinctPaymentRoles := by
        intro key
        exact no_single_exact_key_for_payment_content_and_occurrence key
      arbitraryKeyNotExactForCoincidentRoles :=
        coincident_roles_do_not_make_arbitrary_key_exact }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC26Target


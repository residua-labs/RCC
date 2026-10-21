import RCC.KeyRoleSeparation

/-!
# RCC-26 Key Role Separation Witnesses

RED-first tests for ADR §21.1. A key is safe for a set of roles only when its
kernel is included in every role equivalence. A key can be exact for several
roles only when those role equivalences coincide.

The headline countermodel contains two intentional payments with identical
content and distinct occurrences. It does not assume a digest collision.
Content-idempotence is deliberately outside this module; RCC-27/RCC-28 own that
follow-on contract.
-/

open Residua.RCC.KeyRoles

namespace Residua.RCC.KeyRoles.Tests

/-! ## CM-KEY-ROLE-01: identical content is not identical occurrence -/

inductive PaymentRole
  | content
  | occurrence
  deriving DecidableEq, Repr

structure Payment where
  amount : Nat
  occurrence : Nat
  deriving DecidableEq, Repr

def paymentRoles : RoleEquivalenceSystem PaymentRole Payment where
  equivalent
    | .content => fun left right => left.amount = right.amount
    | .occurrence => fun left right => left.occurrence = right.occurrence
  equivalence
    | .content => ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    | .occurrence => ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def firstPayment : Payment :=
  ⟨250, 40⟩

def secondPayment : Payment :=
  ⟨250, 41⟩

def paymentContentKey (payment : Payment) : Nat :=
  payment.amount

def paymentIdentityKey (payment : Payment) : Payment :=
  payment

/-- The two intentional payments have the same content but distinct occurrences. -/
theorem two_identical_payments_separate_roles :
    paymentRoles.equivalent .content firstPayment secondPayment ∧
      ¬ paymentRoles.equivalent .occurrence firstPayment secondPayment := by
  constructor
  · rfl
  · intro sameOccurrence
    change (40 : Nat) = 41 at sameOccurrence
    exact (by decide : (40 : Nat) ≠ 41) sameOccurrence

/-- The content key exactly realizes content equivalence. -/
theorem payment_content_key_exact_for_content :
    KeyExactForRole paymentRoles .content paymentContentKey := by
  intro left right
  rfl

/--
The same content key is unsafe for occurrence dedup: it aliases the two
intentional payments.
-/
theorem payment_content_key_unsafe_for_occurrence :
    ¬ KeySafeForRole paymentRoles .occurrence paymentContentKey := by
  intro safe
  have sameOccurrence :=
    safe (left := firstPayment) (right := secondPayment) rfl
  exact two_identical_payments_separate_roles.2 sameOccurrence

/--
A finer injective key is safe for both roles even though it is exact for
neither content nor occurrence.  Different role relations therefore forbid one
shared exact identity, not every shared safety key.
-/
theorem payment_identity_key_safe_for_both_roles :
    KeyKernelIncludedForRoles
      paymentRoles [.content, .occurrence] paymentIdentityKey := by
  intro role roleMember left right equalPayment
  change left = right at equalPayment
  cases equalPayment
  cases roleMember with
  | head =>
      rfl
  | tail _ tailMember =>
      cases tailMember with
      | head =>
          rfl
      | tail _ emptyMember =>
          cases emptyMember

/-- Content and occurrence equivalence are extensionally different relations. -/
theorem payment_content_and_occurrence_roles_differ :
    RoleRelationsDiffer paymentRoles .content .occurrence := by
  intro coincide
  exact two_identical_payments_separate_roles.2
    ((coincide firstPayment secondPayment).1
      two_identical_payments_separate_roles.1)

/--
RCC-26 headline: because the role relations differ, no key of any carrier type
can be exact for both payment content and payment occurrence.
-/
theorem no_single_exact_key_for_payment_content_and_occurrence
    {Key : Type} (key : Payment → Key) :
    ¬ KeyExactForRoles paymentRoles [.content, .occurrence] key := by
  exact differing_roles_forbid_one_exact_key
    paymentRoles payment_content_and_occurrence_roles_differ key
    (List.Mem.head _)
    (List.Mem.tail _ (List.Mem.head _))

/-! ## Positive control: one key is safe when the role relations coincide -/

inductive ComputationRole
  | replay
  | cache
  deriving DecidableEq, Repr

structure Computation where
  payload : Nat
  attempt : Nat
  deriving DecidableEq, Repr

def computationRoles : RoleEquivalenceSystem ComputationRole Computation where
  equivalent
    | .replay => fun left right => left.payload = right.payload
    | .cache => fun left right => left.payload = right.payload
  equivalence
    | .replay => ⟨fun _ => rfl, Eq.symm, Eq.trans⟩
    | .cache => ⟨fun _ => rfl, Eq.symm, Eq.trans⟩

def computationContentKey (computation : Computation) : Nat :=
  computation.payload

def constantComputationKey (_ : Computation) : Unit :=
  ()

def computationOne : Computation :=
  ⟨1, 0⟩

def computationTwo : Computation :=
  ⟨2, 0⟩

def replayAndCacheRoles : List ComputationRole :=
  [.replay, .cache]

/--
Coincident role relations alone do not make an arbitrary key exact.  This is
the anti-vacuity witness for the anchor-exactness premise in the iff theorem.
-/
theorem coincident_roles_do_not_make_arbitrary_key_exact :
    ¬ KeyExactForRoles
        computationRoles replayAndCacheRoles constantComputationKey := by
  intro exact
  have replayEquivalent :=
    (exact .replay (List.Mem.head _) computationOne computationTwo).1 rfl
  change (1 : Nat) = 2 at replayEquivalent
  exact (by decide : (1 : Nat) ≠ 2) replayEquivalent

/-- The payload key is exact for both roles because their equivalences coincide. -/
theorem one_key_multi_role_safe_positive :
    KeyExactForRoles computationRoles replayAndCacheRoles computationContentKey := by
  intro role roleMember left right
  cases roleMember with
  | head =>
      rfl
  | tail _ tailMember =>
      cases tailMember with
      | head =>
          rfl
      | tail _ emptyMember =>
          cases emptyMember

/-- Exactness supplies the required kernel inclusion for the entire role set. -/
theorem one_key_multi_role_kernel_inclusion_positive :
    KeyKernelIncludedForRoles
      computationRoles replayAndCacheRoles computationContentKey := by
  exact key_exact_for_roles_implies_kernel_inclusion
    computationRoles one_key_multi_role_safe_positive

/--
The general One-Key Multi-Role Criterion recovers extensional coincidence of
the replay and cache relations.
-/
theorem replay_and_cache_relations_coincide :
    RoleRelationsCoincide computationRoles .replay .cache := by
  exact one_key_multi_role_criterion
    computationRoles one_key_multi_role_safe_positive
    (List.Mem.head _)
    (List.Mem.tail _ (List.Mem.head _))

/--
The exact iff form needs both the anchor exactness witness and relation
coincidence; the positive control supplies both.
-/
theorem replay_and_cache_exact_criterion :
    KeyExactForRoles
        computationRoles replayAndCacheRoles computationContentKey ↔
      KeyExactForRole computationRoles .replay computationContentKey ∧
        RoleRelationsCoincideWith
          computationRoles replayAndCacheRoles .replay := by
  exact key_exact_for_roles_iff_anchor_exact_and_relations_coincide
    computationRoles (List.Mem.head _)

#print axioms two_identical_payments_separate_roles
#print axioms payment_content_key_unsafe_for_occurrence
#print axioms payment_identity_key_safe_for_both_roles
#print axioms no_single_exact_key_for_payment_content_and_occurrence
#print axioms coincident_roles_do_not_make_arbitrary_key_exact
#print axioms one_key_multi_role_safe_positive
#print axioms replay_and_cache_relations_coincide
#print axioms key_exact_for_roles_implies_kernel_inclusion
#print axioms key_exact_for_roles_iff_anchor_exact_and_relations_coincide
#print axioms replay_and_cache_exact_criterion

end Residua.RCC.KeyRoles.Tests


import Init

/-!
# RCC-26 Key Role Separation

A key induces an equality kernel. It is safe for a role only when that kernel
is included in the role's required equivalence relation. A key is exact for a
role when kernel equality and role equivalence coincide.

The One-Key Multi-Role Criterion proved here says that one key can be exact for
several roles only when every selected role has the same equivalence relation.
This module does not model content-idempotent effects or derive an exactly-once
protocol; those are the RCC-27/RCC-28 follow-ons.

Prelude-only Lean 4.14; no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.KeyRoles

universe u v w

/-- Every key role declares the equivalence relation it genuinely requires. -/
structure RoleEquivalenceSystem (Role : Type u) (Object : Type v) where
  equivalent : Role → Object → Object → Prop
  equivalence : ∀ role, Equivalence (equivalent role)

/-- Equality induced by a concrete key. -/
def KeyKernel {Object : Type v} {Key : Type w}
    (key : Object → Key) (left right : Object) : Prop :=
  key left = key right

/-- Single-role safety: the key kernel is included in the role equivalence. -/
def KeySafeForRole {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    (role : Role) (key : Object → Key) : Prop :=
  ∀ ⦃left right⦄,
    KeyKernel key left right → system.equivalent role left right

/-- A key serving a role set is safe only when it is safe for every member. -/
def KeyKernelIncludedForRoles
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    (roles : List Role) (key : Object → Key) : Prop :=
  ∀ role, role ∈ roles → KeySafeForRole system role key

/-- Exact role identity: key equality iff the role requires equivalence. -/
def KeyExactForRole {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    (role : Role) (key : Object → Key) : Prop :=
  ∀ left right,
    KeyKernel key left right ↔ system.equivalent role left right

/-- A key is exact for a role set only when it is exact for every member. -/
def KeyExactForRoles {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    (roles : List Role) (key : Object → Key) : Prop :=
  ∀ role, role ∈ roles → KeyExactForRole system role key

/-- Two roles coincide when their required relations are extensionally equal. -/
def RoleRelationsCoincide {Role : Type u} {Object : Type v}
    (system : RoleEquivalenceSystem Role Object)
    (first second : Role) : Prop :=
  ∀ left right,
    system.equivalent first left right ↔
      system.equivalent second left right

/-- Roles differ exactly when their equivalence relations do not coincide. -/
def RoleRelationsDiffer {Role : Type u} {Object : Type v}
    (system : RoleEquivalenceSystem Role Object)
    (first second : Role) : Prop :=
  ¬ RoleRelationsCoincide system first second

/--
Every selected role relation coincides with an anchor relation.  The anchor
keeps the converse criterion honest: coincident role relations alone do not
prove that an arbitrary key realizes any of them exactly.
-/
def RoleRelationsCoincideWith
    {Role : Type u} {Object : Type v}
    (system : RoleEquivalenceSystem Role Object)
    (roles : List Role) (anchor : Role) : Prop :=
  ∀ role, role ∈ roles → RoleRelationsCoincide system anchor role

/-- Exactness is stronger than the role-set kernel-inclusion safety floor. -/
theorem key_exact_for_roles_implies_kernel_inclusion
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {roles : List Role} {key : Object → Key}
    (exact : KeyExactForRoles system roles key) :
    KeyKernelIncludedForRoles system roles key := by
  intro role roleMember left right equalKey
  exact (exact role roleMember left right).1 equalKey

/--
RCC-26 One-Key Multi-Role Criterion: if one key is exact for two selected
roles, their equivalence relations necessarily coincide.
-/
theorem one_key_multi_role_criterion
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {roles : List Role} {key : Object → Key}
    (exact : KeyExactForRoles system roles key)
    {first second : Role}
    (firstMember : first ∈ roles) (secondMember : second ∈ roles) :
    RoleRelationsCoincide system first second := by
  intro left right
  constructor
  · intro firstEquivalent
    have equalKey : KeyKernel key left right :=
      (exact first firstMember left right).2 firstEquivalent
    exact (exact second secondMember left right).1 equalKey
  · intro secondEquivalent
    have equalKey : KeyKernel key left right :=
      (exact second secondMember left right).2 secondEquivalent
    exact (exact first firstMember left right).1 equalKey

/--
Exact One-Key Multi-Role Criterion.  Once a selected anchor role is known to be
realized exactly by `key`, exactness for every selected role is equivalent to
all selected role relations coinciding with the anchor relation.

The anchor exactness premise is load-bearing: relation coincidence by itself
cannot make an arbitrary constant or otherwise under-discriminating key exact.
-/
theorem key_exact_for_roles_iff_anchor_exact_and_relations_coincide
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {roles : List Role} {anchor : Role} {key : Object → Key}
    (anchorMember : anchor ∈ roles) :
    KeyExactForRoles system roles key ↔
      KeyExactForRole system anchor key ∧
        RoleRelationsCoincideWith system roles anchor := by
  constructor
  · intro exact
    refine ⟨exact anchor anchorMember, ?_⟩
    intro role roleMember
    exact one_key_multi_role_criterion
      system exact anchorMember roleMember
  · rintro ⟨anchorExact, coincide⟩
    intro role roleMember left right
    exact (anchorExact left right).trans
      (coincide role roleMember left right)

/--
Contrapositive criterion: extensionally different role relations forbid any
single key from being exact for both selected roles.
-/
theorem differing_roles_forbid_one_exact_key
    {Role : Type u} {Object : Type v} {Key : Type w}
    (system : RoleEquivalenceSystem Role Object)
    {first second : Role}
    (differ : RoleRelationsDiffer system first second)
    (key : Object → Key) {roles : List Role}
    (firstMember : first ∈ roles) (secondMember : second ∈ roles) :
    ¬ KeyExactForRoles system roles key := by
  intro exact
  exact differ
    (one_key_multi_role_criterion
      system exact firstMember secondMember)

end Residua.RCC.KeyRoles


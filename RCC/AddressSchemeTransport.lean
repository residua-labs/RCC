import RCC.AddressQuotient

/-!
# AK-7 Rooted Address-Scheme Transport

Address schemas may not bootstrap or migrate themselves.  The first scheme is
anchored by an external root.  Every successor is authorized by the old
scheme, strictly increases the reflection level, and carries a conservative
transport for one complete affected-address universe.

Each transported address retains:

* the old canonical bytes;
* the new canonical bytes;
* definitional binding to both scheme implementations; and
* an explicit cross-schema equivalence witness.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.Addressing

universe u v w

/-- One canonical-address scheme at one reflection level. -/
structure AddressScheme
    (AddressId : Type u)
    (Bytes : Type v) where
  schemaQ : SchemaQ
  level : Nat
  canonicalBytes : AddressId → Bytes

/-- The trust root is external to the schemes it anchors. -/
structure ExternalRootProtocol
    (Root : Type w)
    (AddressId : Type u)
    (Bytes : Type v) where
  Anchors : Root → AddressScheme AddressId Bytes → Prop

/-- Proof that one scheme is the externally anchored level-zero root. -/
structure ExternalSchemeAnchor
    {Root : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    (protocol : ExternalRootProtocol Root AddressId Bytes)
    (scheme : AddressScheme AddressId Bytes) where
  root : Root
  anchored : protocol.Anchors root scheme
  levelZero : scheme.level = 0

/--
Admission protocol for schema successors.  Authorization is indexed by a
scheme, so a post-state authority token cannot be silently used at the old
scheme.
-/
structure SchemeApprovalProtocol
    (Authority Receipt : Type w)
    (AddressId : Type u)
    (Bytes : Type v) where
  AuthorizedAt :
    AddressScheme AddressId Bytes → Authority → Prop
  Approves :
    Receipt → Authority →
      AddressScheme AddressId Bytes →
      AddressScheme AddressId Bytes →
      Prop

/-- Cross-schema semantic equivalence for one affected address. -/
structure SchemaEquivalenceProtocol
    (AddressId : Type u)
    (Bytes : Type v) where
  Equivalent : AddressId → Bytes → Bytes → Prop

/--
One conservative old/new byte transport.  Callers cannot supply bytes that
are detached from either scheme's actual canonicalizer.
-/
structure AddressTransportEntry
    {AddressId : Type u}
    {Bytes : Type v}
    (equivalence : SchemaEquivalenceProtocol AddressId Bytes)
    (oldScheme newScheme : AddressScheme AddressId Bytes)
    (address : AddressId) where
  oldBytes : Bytes
  newBytes : Bytes
  oldBytesBound :
    oldScheme.canonicalBytes address = oldBytes
  newBytesBound :
    newScheme.canonicalBytes address = newBytes
  equivalent :
    equivalence.Equivalent address oldBytes newBytes

/--
Complete conservative migration from `oldScheme` to `newScheme`.

`Affected` is the policy-declared universe.  `affectedAddresses` is merely its
finite realization, with exactness preventing omission.  `transport` then
provides an equivalence-bearing entry for every enumerated address.
-/
structure ConservativeSchemaTransport
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    (approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes)
    (equivalence : SchemaEquivalenceProtocol AddressId Bytes)
    (oldScheme newScheme : AddressScheme AddressId Bytes)
    (Affected : AddressId → Prop)
    (affectedAddresses : List AddressId) where
  levelIncreases :
    oldScheme.level < newScheme.level
  authority : Authority
  approvalReceipt : Receipt
  authorizedByOld :
    approval.AuthorizedAt oldScheme authority
  successorApprovedByOld :
    approval.Approves approvalReceipt authority oldScheme newScheme
  affectedExact :
    ∀ address,
      address ∈ affectedAddresses ↔ Affected address
  transport :
    ∀ address,
      address ∈ affectedAddresses →
      AddressTransportEntry equivalence oldScheme newScheme address

/--
Rooted schemes have exactly two lawful origins: an external root, or an
old-rooted predecessor plus a conservative pre-state-approved transport.
-/
inductive RootedAddressScheme
    {Root : Type w}
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    (rootProtocol : ExternalRootProtocol Root AddressId Bytes)
    (approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes)
    (equivalence : SchemaEquivalenceProtocol AddressId Bytes) :
    AddressScheme AddressId Bytes → Type (max u v w)
  | external
      {scheme : AddressScheme AddressId Bytes}
      (anchor : ExternalSchemeAnchor rootProtocol scheme) :
      RootedAddressScheme rootProtocol approval equivalence scheme
  | successor
      {oldScheme newScheme : AddressScheme AddressId Bytes}
      (oldRooted :
        RootedAddressScheme rootProtocol approval equivalence oldScheme)
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId}
      (migration :
        ConservativeSchemaTransport
          approval equivalence oldScheme newScheme Affected affectedAddresses) :
      RootedAddressScheme rootProtocol approval equivalence newScheme

/-- Every policy-declared affected address is present in the sealed list. -/
theorem ConservativeSchemaTransport.affectedEnumerated
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    {approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes}
    {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
    {oldScheme newScheme : AddressScheme AddressId Bytes}
    {Affected : AddressId → Prop}
    {affectedAddresses : List AddressId}
    (migration :
      ConservativeSchemaTransport
        approval equivalence oldScheme newScheme Affected affectedAddresses)
    {address : AddressId}
    (affected : Affected address) :
    address ∈ affectedAddresses :=
  (migration.affectedExact address).mpr affected

/--
No-drop transport: every declared affected address has bound old/new canonical
bytes and an explicit equivalence witness.
-/
theorem ConservativeSchemaTransport.noDrop
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    {approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes}
    {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
    {oldScheme newScheme : AddressScheme AddressId Bytes}
    {Affected : AddressId → Prop}
    {affectedAddresses : List AddressId}
    (migration :
      ConservativeSchemaTransport
        approval equivalence oldScheme newScheme Affected affectedAddresses)
    {address : AddressId}
    (affected : Affected address) :
    ∃ oldBytes newBytes,
      oldScheme.canonicalBytes address = oldBytes ∧
        newScheme.canonicalBytes address = newBytes ∧
        equivalence.Equivalent address oldBytes newBytes := by
  have enumerated : address ∈ affectedAddresses :=
    migration.affectedEnumerated affected
  let entry := migration.transport address enumerated
  exact
    ⟨entry.oldBytes, entry.newBytes, entry.oldBytesBound,
      entry.newBytesBound, entry.equivalent⟩

/-- Successor admission is always backed by authority at the old scheme. -/
theorem ConservativeSchemaTransport.usesPreStateAuthority
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    {approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes}
    {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
    {oldScheme newScheme : AddressScheme AddressId Bytes}
    {Affected : AddressId → Prop}
    {affectedAddresses : List AddressId}
    (migration :
      ConservativeSchemaTransport
        approval equivalence oldScheme newScheme Affected affectedAddresses) :
    approval.AuthorizedAt oldScheme migration.authority :=
  migration.authorizedByOld

/--
A scheme cannot certify itself as its own successor: strict level increase
would require `level < level`.
-/
theorem same_scheme_cannot_self_certify
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    {approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes}
    {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
    {scheme : AddressScheme AddressId Bytes}
    {Affected : AddressId → Prop}
    {affectedAddresses : List AddressId} :
    ¬ Nonempty
      (ConservativeSchemaTransport
        approval equivalence scheme scheme Affected affectedAddresses) := by
  rintro ⟨migration⟩
  exact (Nat.lt_irrefl scheme.level) migration.levelIncreases

/-- A rooted successor exposes its actual conservative predecessor migration. -/
theorem rooted_successor_has_pre_state_authority
    {Root : Type w}
    {Authority Receipt : Type w}
    {AddressId : Type u}
    {Bytes : Type v}
    {rootProtocol : ExternalRootProtocol Root AddressId Bytes}
    {approval :
      SchemeApprovalProtocol Authority Receipt AddressId Bytes}
    {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
    {oldScheme newScheme : AddressScheme AddressId Bytes}
    (oldRooted :
      RootedAddressScheme rootProtocol approval equivalence oldScheme)
    {Affected : AddressId → Prop}
    {affectedAddresses : List AddressId}
    (migration :
      ConservativeSchemaTransport
        approval equivalence oldScheme newScheme Affected affectedAddresses) :
    ∃ _rooted :
        RootedAddressScheme rootProtocol approval equivalence newScheme,
      approval.AuthorizedAt oldScheme migration.authority :=
  ⟨.successor oldRooted migration, migration.authorizedByOld⟩

end Residua.RCC.Addressing

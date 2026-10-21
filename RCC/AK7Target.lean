import RCC.AddressSchemeTransport

/-!
# AK-7 candidate: rooted bootstrap and conservative schema transport

AK-7's obligation is that an address scheme has exactly two lawful origins —
an externally anchored level-zero root, or an old-rooted predecessor plus a
conservative transport authorized by the old scheme — and that the transport
keeps every declared affected address with bound old/new canonical bytes and
an explicit cross-schema equivalence witness.

The content lives in the Prelude module
`RCC.AddressSchemeTransport` (proved for independent
reasons): `RootedAddressScheme.external`, `ConservativeSchemaTransport`
(`affectedEnumerated`, `noDrop`, `usesPreStateAuthority`), and the refusal
`same_scheme_cannot_self_certify`.  This Target only connects that content to
the obligation: it restates the parametric laws as certificate fields, pins
their non-vacuity on one finite fixture world (a level-0 root scheme, a
level-1 successor with one affected address), and instantiates the refusal at
both fixture schemes.

Scope honesty: the fixture (`Nat` addresses, one-element affected universe,
`Unit` authority) pins non-vacuity of the two lawful origins; it is not a
production migration.  The parametric fields are the Prelude theorems
themselves, by import.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.AK7Target

open Residua.RCC.Addressing

/-! ## Fixture: one external root and one authorized successor -/

/-- The trust root is external to the schemes it anchors. -/
def demoRootProtocol : ExternalRootProtocol Unit Nat Nat where
  Anchors := fun _ scheme => scheme.level = 0

/-- The externally anchored first scheme: level zero, identity bytes. -/
def rootScheme : AddressScheme Nat Nat where
  schemaQ := { value := "ak7-demo-root-schema" }
  level := 0
  canonicalBytes := fun address => address

/-- The successor: strictly higher reflection level, changed canonicalizer. -/
def successorScheme : AddressScheme Nat Nat where
  schemaQ := { value := "ak7-demo-successor-schema" }
  level := 1
  canonicalBytes := fun address => address + 1

/-- Authorization is indexed by scheme; the fixture grants it trivially. -/
def demoApproval : SchemeApprovalProtocol Unit Unit Nat Nat where
  AuthorizedAt := fun _ _ => True
  Approves := fun _ _ _ _ => True

/-- Cross-schema equivalence: both byte images are bound to their schemes. -/
def demoEquivalence : SchemaEquivalenceProtocol Nat Nat where
  Equivalent := fun address oldBytes newBytes =>
    oldBytes = rootScheme.canonicalBytes address ∧
      newBytes = successorScheme.canonicalBytes address

/-- The policy-declared affected universe: exactly address 0. -/
def demoAffected : Nat → Prop :=
  fun address => address = 0

def demoAffectedAddresses : List Nat :=
  [0]

/-- One complete conservative migration with exact enumeration. -/
def demoMigration :
    ConservativeSchemaTransport demoApproval demoEquivalence
      rootScheme successorScheme demoAffected demoAffectedAddresses where
  levelIncreases := Nat.lt_succ_self 0
  authority := ()
  approvalReceipt := ()
  authorizedByOld := trivial
  successorApprovedByOld := trivial
  affectedExact := by
    intro address
    simp [demoAffected, demoAffectedAddresses]
  transport := by
    intro address member
    have addressZero : address = 0 := by
      simpa [demoAffectedAddresses] using member
    subst addressZero
    exact
      { oldBytes := 0
      , newBytes := 1
      , oldBytesBound := rfl
      , newBytesBound := rfl
      , equivalent := ⟨rfl, rfl⟩ }

/-- The first scheme's only lawful origin here: an external root anchor. -/
def demoAnchor : ExternalSchemeAnchor demoRootProtocol rootScheme where
  root := ()
  anchored := rfl
  levelZero := rfl

def demoRootRooted :
    RootedAddressScheme demoRootProtocol demoApproval demoEquivalence rootScheme :=
  .external demoAnchor

def demoSuccessorRooted :
    RootedAddressScheme demoRootProtocol demoApproval demoEquivalence successorScheme :=
  .successor demoRootRooted demoMigration

/-! ## The certificate -/

structure Certificate : Prop where
  /-- Prelude `ConservativeSchemaTransport.affectedEnumerated`: no declared
  affected address may be omitted from the sealed list. -/
  affectedEnumerated :
    ∀ {Authority Receipt AddressId Bytes : Type}
      {approval : SchemeApprovalProtocol Authority Receipt AddressId Bytes}
      {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
      {oldScheme newScheme : AddressScheme AddressId Bytes}
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId}
      (_migration :
        ConservativeSchemaTransport
          approval equivalence oldScheme newScheme Affected affectedAddresses)
      {address : AddressId}
      (_affected : Affected address),
      address ∈ affectedAddresses
  /-- Prelude `ConservativeSchemaTransport.noDrop`: every affected address
  keeps bound old/new canonical bytes and an equivalence witness. -/
  noDropTransport :
    ∀ {Authority Receipt AddressId Bytes : Type}
      {approval : SchemeApprovalProtocol Authority Receipt AddressId Bytes}
      {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
      {oldScheme newScheme : AddressScheme AddressId Bytes}
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId}
      (_migration :
        ConservativeSchemaTransport
          approval equivalence oldScheme newScheme Affected affectedAddresses)
      {address : AddressId}
      (_affected : Affected address),
      ∃ oldBytes newBytes : Bytes,
        oldScheme.canonicalBytes address = oldBytes ∧
          newScheme.canonicalBytes address = newBytes ∧
          equivalence.Equivalent address oldBytes newBytes
  /-- Prelude `ConservativeSchemaTransport.usesPreStateAuthority`: successor
  admission is always backed by authority at the old scheme. -/
  successorUsesPreStateAuthority :
    ∀ {Authority Receipt AddressId Bytes : Type}
      {approval : SchemeApprovalProtocol Authority Receipt AddressId Bytes}
      {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
      {oldScheme newScheme : AddressScheme AddressId Bytes}
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId}
      (migration :
        ConservativeSchemaTransport
          approval equivalence oldScheme newScheme Affected affectedAddresses),
      approval.AuthorizedAt oldScheme migration.authority
  /-- Prelude `rooted_successor_has_pre_state_authority`: a rooted successor
  exposes its actual conservative predecessor migration. -/
  rootedSuccessorExposesPreStateAuthority :
    ∀ {Root Authority Receipt AddressId Bytes : Type}
      {rootProtocol : ExternalRootProtocol Root AddressId Bytes}
      {approval : SchemeApprovalProtocol Authority Receipt AddressId Bytes}
      {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
      {oldScheme newScheme : AddressScheme AddressId Bytes}
      (_oldRooted :
        RootedAddressScheme rootProtocol approval equivalence oldScheme)
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId}
      (migration :
        ConservativeSchemaTransport
          approval equivalence oldScheme newScheme Affected affectedAddresses),
      ∃ _rooted :
          RootedAddressScheme rootProtocol approval equivalence newScheme,
        approval.AuthorizedAt oldScheme migration.authority
  /-- Fixture: the first scheme is the externally anchored level-zero root. -/
  externalRootAnchorsFirstScheme :
    rootScheme.level = 0 ∧
      Nonempty
        (RootedAddressScheme demoRootProtocol demoApproval demoEquivalence
          rootScheme)
  /-- Fixture: the successor is admitted by a complete conservative transport
  and is rooted through its predecessor. -/
  successorAuthorizedAndRooted :
    Nonempty
        (ConservativeSchemaTransport demoApproval demoEquivalence rootScheme
          successorScheme demoAffected demoAffectedAddresses) ∧
      Nonempty
        (RootedAddressScheme demoRootProtocol demoApproval demoEquivalence
          successorScheme)
  /-- Fixture: the one declared affected address is transported with both
  byte bindings and the equivalence witness. -/
  affectedAddressTransported :
    ∀ address,
      demoAffected address →
      ∃ oldBytes newBytes : Nat,
        rootScheme.canonicalBytes address = oldBytes ∧
          successorScheme.canonicalBytes address = newBytes ∧
          demoEquivalence.Equivalent address oldBytes newBytes
  /-- Refusal (Prelude `same_scheme_cannot_self_certify`): no scheme can
  authorize itself as its own successor — strict level increase would require
  `level < level`. -/
  selfCertificationRefused :
    ∀ {Authority Receipt AddressId Bytes : Type}
      {approval : SchemeApprovalProtocol Authority Receipt AddressId Bytes}
      {equivalence : SchemaEquivalenceProtocol AddressId Bytes}
      {scheme : AddressScheme AddressId Bytes}
      {Affected : AddressId → Prop}
      {affectedAddresses : List AddressId},
      ¬ Nonempty
        (ConservativeSchemaTransport
          approval equivalence scheme scheme Affected affectedAddresses)
  /-- Refusal (fixture, root side): the root scheme cannot transport to
  itself. -/
  rootSelfTransportRefused :
    ¬ Nonempty
      (ConservativeSchemaTransport demoApproval demoEquivalence rootScheme
        rootScheme demoAffected demoAffectedAddresses)
  /-- Refusal (fixture, successor side): the successor scheme cannot transport
  to itself either. -/
  successorSelfTransportRefused :
    ¬ Nonempty
      (ConservativeSchemaTransport demoApproval demoEquivalence successorScheme
        successorScheme demoAffected demoAffectedAddresses)

def certificate : Certificate where
  affectedEnumerated := by
    intro Authority Receipt AddressId Bytes approval equivalence oldScheme
      newScheme Affected affectedAddresses _migration address _affected
    exact _migration.affectedEnumerated _affected
  noDropTransport := by
    intro Authority Receipt AddressId Bytes approval equivalence oldScheme
      newScheme Affected affectedAddresses _migration address _affected
    exact _migration.noDrop _affected
  successorUsesPreStateAuthority := by
    intro Authority Receipt AddressId Bytes approval equivalence oldScheme
      newScheme Affected affectedAddresses migration
    exact migration.usesPreStateAuthority
  rootedSuccessorExposesPreStateAuthority := by
    intro Root Authority Receipt AddressId Bytes rootProtocol approval
      equivalence oldScheme newScheme oldRooted Affected affectedAddresses
      migration
    exact rooted_successor_has_pre_state_authority oldRooted migration
  externalRootAnchorsFirstScheme :=
    ⟨rfl, ⟨demoRootRooted⟩⟩
  successorAuthorizedAndRooted :=
    ⟨⟨demoMigration⟩, ⟨demoSuccessorRooted⟩⟩
  affectedAddressTransported := by
    intro address affected
    exact demoMigration.noDrop affected
  selfCertificationRefused := by
    intro Authority Receipt AddressId Bytes approval equivalence scheme
      Affected affectedAddresses nonempty
    exact same_scheme_cannot_self_certify nonempty
  rootSelfTransportRefused := same_scheme_cannot_self_certify
  successorSelfTransportRefused := same_scheme_cannot_self_certify

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.AK7Target

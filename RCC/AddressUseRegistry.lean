import RCC.AddressQuotient

/-!
# RCC AK-8 complete address-use registry

An epoch does not gain authority from a bag of digest strings.  Its sealed
schema first enumerates every q-bearing field at every consumer use site.
Each registration must then agree with that use's address kind, quotient
domain, and canonical schema, and must carry:

* a typed-envelope certificate (a naked digest is not authority);
* a consumer-factorization certificate; and
* a collision-policy certificate.

The instance supplies only these certificate families.  This module derives
the registry result by one fixed decision tree.  Missing fields and mismatched
metadata are named refusals; they can never be interpreted as a complete
registry.

Prelude-only Lean 4.14; no Mathlib or proof placeholders.
-/

namespace Residua.RCC.Addressing.AddressUseRegistry

open Residua.RCC.Addressing

universe u

/-- One q-bearing field at one concrete consumer use site. -/
structure AddressUseCoordinate where
  fieldPath : String
  consumerQ : String
  deriving DecidableEq, Repr

/--
The address identity that the sealed schema requires at one use coordinate.
The kind, domain, and schema are independently checked.
-/
structure AddressUseRequirement where
  coordinate : AddressUseCoordinate
  kind : AddressKind
  domainQ : DomainQ
  schemaQ : SchemaQ
  deriving DecidableEq, Repr

/--
A closed-world projection of all q-bearing schema fields and their use sites.

`complete` is the load-bearing direction: an in-scope q use cannot disappear
merely because the executable enumeration omitted it.
-/
structure SealedAddressUseUniverse where
  surfaceSchemaQ : SchemaQ
  InUniverse : AddressUseRequirement → Prop
  enumeration : List AddressUseRequirement
  sound :
    ∀ requirement,
      requirement ∈ enumeration → InUniverse requirement
  complete :
    ∀ requirement,
      InUniverse requirement → requirement ∈ enumeration

/--
One raw registry row.

Certificate types are supplied by the address domain.  Keeping the three
fields optional lets the common validator distinguish an absent proof from a
certified negative fact; no absence is inferred from a failed search.
-/
structure AddressUseEntry
    (TypedEnvelopeCertificate :
      AddressUseRequirement → Type u)
    (ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u)
    (CollisionPolicyCertificate :
      AddressUseRequirement → Type u) where
  requirement : AddressUseRequirement
  typedEnvelope :
    Option (TypedEnvelopeCertificate requirement)
  consumerFactorization :
    Option (ConsumerFactorizationCertificate requirement)
  collisionPolicy :
    Option (CollisionPolicyCertificate requirement)

/-- A registry is only the supplied evidence rows, never a supplied verdict. -/
structure AddressUseRegistry
    (TypedEnvelopeCertificate :
      AddressUseRequirement → Type u)
    (ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u)
    (CollisionPolicyCertificate :
      AddressUseRequirement → Type u) where
  entries :
    List
      (AddressUseEntry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate)

/-- Every way an address use can fail the fixed AK-8 validation sequence. -/
inductive AddressUseResidue
  | unregistered (coordinate : AddressUseCoordinate)
  | coordinateMismatch
      (expected actual : AddressUseCoordinate)
  | kindMismatch
      (coordinate : AddressUseCoordinate)
      (expected actual : AddressKind)
  | domainMismatch
      (coordinate : AddressUseCoordinate)
      (expected actual : DomainQ)
  | schemaMismatch
      (coordinate : AddressUseCoordinate)
      (expected actual : SchemaQ)
  | nakedDigestAuthority (coordinate : AddressUseCoordinate)
  | consumerFactorizationMissing (coordinate : AddressUseCoordinate)
  | collisionPolicyMissing (coordinate : AddressUseCoordinate)
  deriving DecidableEq, Repr

/-- One use is either fully justified or refused with one named residue. -/
inductive AddressUseAssessment
  | justified
  | refuse (residue : AddressUseResidue)
  deriving DecidableEq, Repr

/-- The sealed registry is complete, or its first canonical residue is named. -/
inductive AddressUseRegistryAssessment
  | complete
  | refuse (residue : AddressUseResidue)
  deriving DecidableEq, Repr

/-- Find the first row for the exact field/use-site coordinate. -/
def findEntry
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (coordinate : AddressUseCoordinate) :
    List
      (AddressUseEntry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) →
      Option
        (AddressUseEntry
          TypedEnvelopeCertificate
          ConsumerFactorizationCertificate
          CollisionPolicyCertificate)
  | [] => none
  | entry :: remaining =>
      if entry.requirement.coordinate = coordinate then
        some entry
      else
        findEntry coordinate remaining

/--
The single AK-8 use-site validator.

The order is deliberate: identity metadata is checked before any proof object
can be consumed.  A proof for a value address therefore cannot authorize an
occurrence address, nor can a proof for one domain/schema authorize another.
-/
def validateEntry
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (expected : AddressUseRequirement)
    (entry :
      AddressUseEntry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) :
    AddressUseAssessment :=
  if entry.requirement.coordinate ≠ expected.coordinate then
    .refuse
      (.coordinateMismatch
        expected.coordinate entry.requirement.coordinate)
  else if entry.requirement.kind ≠ expected.kind then
    .refuse
      (.kindMismatch
        expected.coordinate expected.kind entry.requirement.kind)
  else if entry.requirement.domainQ ≠ expected.domainQ then
    .refuse
      (.domainMismatch
        expected.coordinate expected.domainQ entry.requirement.domainQ)
  else if entry.requirement.schemaQ ≠ expected.schemaQ then
    .refuse
      (.schemaMismatch
        expected.coordinate expected.schemaQ entry.requirement.schemaQ)
  else
    match entry.typedEnvelope with
    | none =>
        .refuse (.nakedDigestAuthority expected.coordinate)
    | some _ =>
        match entry.consumerFactorization with
        | none =>
            .refuse
              (.consumerFactorizationMissing expected.coordinate)
        | some _ =>
            match entry.collisionPolicy with
            | none =>
                .refuse (.collisionPolicyMissing expected.coordinate)
            | some _ =>
                .justified

/-- Validate one required q use by deriving its row from the registry. -/
def assessAddressUse
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (registry :
      AddressUseRegistry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate)
    (requirement : AddressUseRequirement) :
    AddressUseAssessment :=
  match findEntry requirement.coordinate registry.entries with
  | none => .refuse (.unregistered requirement.coordinate)
  | some entry => validateEntry requirement entry

/-- Fold the fixed single-use validator over the sealed canonical universe. -/
def assessRequirements
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (registry :
      AddressUseRegistry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) :
    List AddressUseRequirement → AddressUseRegistryAssessment
  | [] => .complete
  | requirement :: remaining =>
      match assessAddressUse registry requirement with
      | .refuse residue => .refuse residue
      | .justified => assessRequirements registry remaining

/--
The registry verdict is mechanically derived from the sealed schema
enumeration.  The instance cannot supply `complete` directly.
-/
def assessAddressUseRegistry
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (sealedUniverse : SealedAddressUseUniverse)
    (registry :
      AddressUseRegistry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate) :
    AddressUseRegistryAssessment :=
  assessRequirements registry sealedUniverse.enumeration

/-- A complete fold is exactly pointwise justification of its enumeration. -/
theorem assess_requirements_complete_iff
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (registry :
      AddressUseRegistry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate)
    (requirements : List AddressUseRequirement) :
    assessRequirements registry requirements =
        AddressUseRegistryAssessment.complete ↔
      ∀ requirement,
        requirement ∈ requirements →
          assessAddressUse registry requirement =
            AddressUseAssessment.justified := by
  induction requirements with
  | nil =>
      simp [assessRequirements]
  | cons requirement remaining inductionHypothesis =>
      cases assessed : assessAddressUse registry requirement with
      | justified =>
          simp [assessRequirements, assessed, inductionHypothesis]
      | refuse residue =>
          simp [assessRequirements, assessed]

/--
Closed-world completeness: if the derived registry fold is complete, every
use in the sealed schema universe has a fully justified row.
-/
theorem complete_registry_justifies_every_use
    {TypedEnvelopeCertificate :
      AddressUseRequirement → Type u}
    {ConsumerFactorizationCertificate :
      AddressUseRequirement → Type u}
    {CollisionPolicyCertificate :
      AddressUseRequirement → Type u}
    (sealedUniverse : SealedAddressUseUniverse)
    (registry :
      AddressUseRegistry
        TypedEnvelopeCertificate
        ConsumerFactorizationCertificate
        CollisionPolicyCertificate)
    (complete :
      assessAddressUseRegistry sealedUniverse registry =
        AddressUseRegistryAssessment.complete)
    (requirement : AddressUseRequirement)
    (inUniverse : sealedUniverse.InUniverse requirement) :
    assessAddressUse registry requirement =
      AddressUseAssessment.justified := by
  exact
    (assess_requirements_complete_iff
      registry sealedUniverse.enumeration).1 complete
      requirement (sealedUniverse.complete requirement inUniverse)

end Residua.RCC.Addressing.AddressUseRegistry

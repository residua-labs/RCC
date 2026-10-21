import RCC.AddressUseRegistry

/-!
# RCC AK-8 address-use registry countermodels

The fixture seals two q-bearing use sites:

* a value field consumed by a value cache; and
* an occurrence field consumed by an exactly-once receiver.

Only a complete registry with matching kind/domain/schema metadata, a typed
envelope, consumer factorization, and collision policy is accepted.
-/

namespace Residua.RCC.Addressing.AddressUseRegistry.Tests

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressUseRegistry

def surfaceSchema : SchemaQ :=
  ⟨"residua:event-surface:v1"⟩

def valueCoordinate : AddressUseCoordinate where
  fieldPath := "event.payload.value_q"
  consumerQ := "consumer:value-cache:v1"

def occurrenceCoordinate : AddressUseCoordinate where
  fieldPath := "event.occurrence_q"
  consumerQ := "consumer:exactly-once-receiver:v1"

def valueRequirement : AddressUseRequirement where
  coordinate := valueCoordinate
  kind := .value
  domainQ := ⟨"residua:runtime-value"⟩
  schemaQ := ⟨"residua:runtime-value:v1"⟩

def occurrenceRequirement : AddressUseRequirement where
  coordinate := occurrenceCoordinate
  kind := .occurrence
  domainQ := ⟨"residua:effect-occurrence"⟩
  schemaQ := ⟨"residua:effect-occurrence:v1"⟩

def addressUseUniverse : SealedAddressUseUniverse where
  surfaceSchemaQ := surfaceSchema
  InUniverse requirement :=
    requirement = valueRequirement ∨
      requirement = occurrenceRequirement
  enumeration := [valueRequirement, occurrenceRequirement]
  sound := by
    intro requirement member
    simp at member
    exact member
  complete := by
    intro requirement inUniverse
    simp [inUniverse]

/--
Concrete proof families stand in for the already checked AK-1/AK-4 and
collision-policy artifacts.  AK-8 consumes their inhabitants; it does not
manufacture them from a registry row.
-/
inductive TypedEnvelopeCertificate : AddressUseRequirement → Type
  | value :
      TypedEnvelopeCertificate valueRequirement
  | occurrence :
      TypedEnvelopeCertificate occurrenceRequirement

inductive ConsumerFactorizationCertificate :
    AddressUseRequirement → Type
  | valueCache :
      ConsumerFactorizationCertificate valueRequirement
  | occurrenceReceiver :
      ConsumerFactorizationCertificate occurrenceRequirement

inductive CollisionPolicyCertificate :
    AddressUseRequirement → Type
  | valueStore :
      CollisionPolicyCertificate valueRequirement
  | occurrenceStore :
      CollisionPolicyCertificate occurrenceRequirement

abbrev Entry :=
  AddressUseEntry
    TypedEnvelopeCertificate
    ConsumerFactorizationCertificate
    CollisionPolicyCertificate

abbrev Registry :=
  AddressUseRegistry
    TypedEnvelopeCertificate
    ConsumerFactorizationCertificate
    CollisionPolicyCertificate

def valueEntry : Entry where
  requirement := valueRequirement
  typedEnvelope := some .value
  consumerFactorization := some .valueCache
  collisionPolicy := some .valueStore

def occurrenceEntry : Entry where
  requirement := occurrenceRequirement
  typedEnvelope := some .occurrence
  consumerFactorization := some .occurrenceReceiver
  collisionPolicy := some .occurrenceStore

def completeRegistry : Registry where
  entries := [valueEntry, occurrenceEntry]

theorem complete_registry_is_accepted :
    assessAddressUseRegistry addressUseUniverse completeRegistry =
      AddressUseRegistryAssessment.complete := by
  rfl

theorem complete_registry_justifies_occurrence_receiver :
    assessAddressUse completeRegistry occurrenceRequirement =
      AddressUseAssessment.justified :=
  complete_registry_justifies_every_use
    addressUseUniverse completeRegistry
    complete_registry_is_accepted occurrenceRequirement
    (Or.inr rfl)

/-! ## Mutant 1: the sealed schema contains an omitted q field. -/

def missingOccurrenceRegistry : Registry where
  entries := [valueEntry]

theorem omitted_q_field_is_refused :
    assessAddressUseRegistry addressUseUniverse missingOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.unregistered occurrenceCoordinate) := by
  rfl

/-! ## Mutant 2: a value address is supplied to an occurrence consumer. -/

def valueAsOccurrenceRequirement : AddressUseRequirement where
  coordinate := occurrenceCoordinate
  kind := .value
  domainQ := occurrenceRequirement.domainQ
  schemaQ := occurrenceRequirement.schemaQ

def valueAsOccurrenceEntry : Entry where
  requirement := valueAsOccurrenceRequirement
  typedEnvelope := none
  consumerFactorization := none
  collisionPolicy := none

def valueAsOccurrenceRegistry : Registry where
  entries := [valueEntry, valueAsOccurrenceEntry]

theorem value_q_cannot_authorize_occurrence_q :
    assessAddressUseRegistry
        addressUseUniverse valueAsOccurrenceRegistry =
      AddressUseRegistryAssessment.refuse
        (.kindMismatch occurrenceCoordinate .occurrence .value) := by
  rfl

/-! ## Mutant 3: a naked digest tries to cross an address-domain boundary. -/

def nakedValueEntry : Entry where
  requirement := valueRequirement
  typedEnvelope := none
  consumerFactorization := some .valueCache
  collisionPolicy := some .valueStore

def nakedDigestRegistry : Registry where
  entries := [nakedValueEntry, occurrenceEntry]

theorem cross_domain_naked_digest_has_no_authority :
    assessAddressUseRegistry addressUseUniverse nakedDigestRegistry =
      AddressUseRegistryAssessment.refuse
        (.nakedDigestAuthority valueCoordinate) := by
  rfl

/-! ## Mutant 4: a typed use claims the wrong quotient domain. -/

def foreignValueRequirement : AddressUseRequirement where
  coordinate := valueCoordinate
  kind := .value
  domainQ := ⟨"residua:foreign-value"⟩
  schemaQ := valueRequirement.schemaQ

def foreignDomainEntry : Entry where
  requirement := foreignValueRequirement
  typedEnvelope := none
  consumerFactorization := none
  collisionPolicy := none

def foreignDomainRegistry : Registry where
  entries := [foreignDomainEntry, occurrenceEntry]

theorem cross_domain_registration_is_refused :
    assessAddressUseRegistry addressUseUniverse foreignDomainRegistry =
      AddressUseRegistryAssessment.refuse
        (.domainMismatch
          valueCoordinate valueRequirement.domainQ
            foreignValueRequirement.domainQ) := by
  rfl

/-! ## Mutant 5: the field is registered under a stale canonical schema. -/

def staleValueRequirement : AddressUseRequirement where
  coordinate := valueCoordinate
  kind := .value
  domainQ := valueRequirement.domainQ
  schemaQ := ⟨"residua:runtime-value:v0"⟩

def staleSchemaEntry : Entry where
  requirement := staleValueRequirement
  typedEnvelope := none
  consumerFactorization := none
  collisionPolicy := none

def staleSchemaRegistry : Registry where
  entries := [staleSchemaEntry, occurrenceEntry]

theorem schema_mismatch_is_refused :
    assessAddressUseRegistry addressUseUniverse staleSchemaRegistry =
      AddressUseRegistryAssessment.refuse
        (.schemaMismatch
          valueCoordinate valueRequirement.schemaQ
            staleValueRequirement.schemaQ) := by
  rfl

/-! ## Mutant 6: address fidelity is present but consumer use is unjustified. -/

def missingFactorizationEntry : Entry where
  requirement := valueRequirement
  typedEnvelope := some .value
  consumerFactorization := none
  collisionPolicy := some .valueStore

def missingFactorizationRegistry : Registry where
  entries := [missingFactorizationEntry, occurrenceEntry]

theorem missing_consumer_factorization_is_refused :
    assessAddressUseRegistry
        addressUseUniverse missingFactorizationRegistry =
      AddressUseRegistryAssessment.refuse
        (.consumerFactorizationMissing valueCoordinate) := by
  rfl

/-! ## Additional safety: collision policy is independently load-bearing. -/

def missingCollisionPolicyEntry : Entry where
  requirement := valueRequirement
  typedEnvelope := some .value
  consumerFactorization := some .valueCache
  collisionPolicy := none

def missingCollisionPolicyRegistry : Registry where
  entries := [missingCollisionPolicyEntry, occurrenceEntry]

theorem missing_collision_policy_is_refused :
    assessAddressUseRegistry
        addressUseUniverse missingCollisionPolicyRegistry =
      AddressUseRegistryAssessment.refuse
        (.collisionPolicyMissing valueCoordinate) := by
  rfl

end Residua.RCC.Addressing.AddressUseRegistry.Tests

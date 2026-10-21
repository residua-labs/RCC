import RCC.GlobalSerializability

/-!
# RCC-48 Sealed Transaction-Footprint Completeness

`CompleteFootprint` states the desired four-dimensional exactness, but a
runtime adapter must not obtain it from an unsealed or shortened coordinate
list.  This module derives that exactness from four proof-carrying universe
seals: reads, writes, effects, and invariant domains.

For each dimension:

* `semanticInUniverse` prevents an under-quotiented universe;
* `claimedCovered` prevents a footprint from inventing unsealed coordinates;
* `classifiedAtCoordinate` checks every coordinate in the sealed enumeration;
* `CoverageCertificate.complete` prevents a shortened enumeration.

The resulting `CompleteFootprint` is a theorem, not a caller-supplied status
bit.  Universe discovery and host/runtime enumeration remain adapter
obligations.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.TransactionFootprint

open Residua.RCC.AuthorizationFinality
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability

universe u

/-- One finite, proof-carrying semantic-coordinate universe. -/
structure SealedDomainUniverse (Domain : Type u) where
  InUniverse : Domain → Prop
  coordinates : List Domain
  coverage : CoverageCertificate InUniverse coordinates

/--
Exact classification of one claimed footprint list against one sealed domain.
The classifier is required only on the finite sealed enumeration; coverage
lifts it to every semantic coordinate.
-/
structure DomainFootprintSeal
    {Domain : Type u}
    (domainUniverse : SealedDomainUniverse Domain)
    (semantic : Domain → Prop)
    (claimed : List Domain) : Prop where
  semanticInUniverse :
    ∀ domain, semantic domain → domainUniverse.InUniverse domain
  claimedCovered :
    ∀ domain, domain ∈ claimed → domain ∈ domainUniverse.coordinates
  classifiedAtCoordinate :
    ∀ domain,
      domain ∈ domainUniverse.coordinates →
      (domain ∈ claimed ↔ semantic domain)

/-- Every claimed coordinate is declared by the sealed universe predicate. -/
theorem DomainFootprintSeal.claimedInUniverse
    {Domain : Type u}
    {domainUniverse : SealedDomainUniverse Domain}
    {semantic : Domain → Prop}
    {claimed : List Domain}
    (certificate : DomainFootprintSeal domainUniverse semantic claimed)
    {domain : Domain}
    (claimedMember : domain ∈ claimed) :
    domainUniverse.InUniverse domain :=
  domainUniverse.coverage.sound domain
    (certificate.claimedCovered domain claimedMember)

/--
A sealed domain footprint is globally exact.  The reverse direction consumes
the universe coverage theorem, so an empty or shortened enumeration is not a
proof of absence.
-/
theorem DomainFootprintSeal.exact
    {Domain : Type u}
    {domainUniverse : SealedDomainUniverse Domain}
    {semantic : Domain → Prop}
    {claimed : List Domain}
    (certificate : DomainFootprintSeal domainUniverse semantic claimed)
    (domain : Domain) :
    domain ∈ claimed ↔ semantic domain := by
  constructor
  · intro claimedMember
    exact
      (certificate.classifiedAtCoordinate domain
        (certificate.claimedCovered domain claimedMember)).mp claimedMember
  · intro semanticMember
    have inUniverse : domainUniverse.InUniverse domain :=
      certificate.semanticInUniverse domain semanticMember
    have enumerated : domain ∈ domainUniverse.coordinates :=
      domainUniverse.coverage.complete domain inUniverse
    exact
      (certificate.classifiedAtCoordinate domain enumerated).mpr semanticMember

/-- The four independently sealed coordinate universes of one transaction. -/
structure TransactionUniverses
    (ReadDomain WriteDomain EffectDomain InvariantDomain : Type u) where
  reads : SealedDomainUniverse ReadDomain
  writes : SealedDomainUniverse WriteDomain
  effects : SealedDomainUniverse EffectDomain
  invariantDomains : SealedDomainUniverse InvariantDomain

/--
RCC-48 certificate from which footprint completeness is mechanically derived.
No field accepts a pre-existing `CompleteFootprint`.
-/
structure UniverseCompleteFootprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain)
    (state : State)
    (proposal : Proposal Slot Head Judgment)
    (universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain)
    (footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain) : Prop where
  reads :
    DomainFootprintSeal
      universes.reads (surface.Reads state proposal) footprint.reads
  writes :
    DomainFootprintSeal
      universes.writes (surface.Writes state proposal) footprint.writes
  effects :
    DomainFootprintSeal
      universes.effects (surface.Effects state proposal) footprint.effects
  invariantDomains :
    DomainFootprintSeal
      universes.invariantDomains
      (surface.InvariantDomains state proposal) footprint.invariantDomains

/-- Forget the seals only after deriving the existing RCC-48 exactness type. -/
theorem UniverseCompleteFootprint.toCompleteFootprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {state : State}
    {proposal : Proposal Slot Head Judgment}
    {universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    {footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    (sealed :
      UniverseCompleteFootprint surface state proposal universes footprint) :
    CompleteFootprint surface state proposal footprint where
  readsExact := sealed.reads.exact
  writesExact := sealed.writes.exact
  effectsExact := sealed.effects.exact
  invariantDomainsExact := sealed.invariantDomains.exact

/-- Every semantic read coordinate occurs in the certified footprint. -/
theorem semantic_read_is_in_footprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {state : State}
    {proposal : Proposal Slot Head Judgment}
    {universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    {footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    (sealed :
      UniverseCompleteFootprint surface state proposal universes footprint)
    {domain : ReadDomain}
    (semantic : surface.Reads state proposal domain) :
    domain ∈ footprint.reads :=
  (sealed.toCompleteFootprint.readsExact domain).mpr semantic

/-- Every semantic write coordinate occurs in the certified footprint. -/
theorem semantic_write_is_in_footprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {state : State}
    {proposal : Proposal Slot Head Judgment}
    {universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    {footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    (sealed :
      UniverseCompleteFootprint surface state proposal universes footprint)
    {domain : WriteDomain}
    (semantic : surface.Writes state proposal domain) :
    domain ∈ footprint.writes :=
  (sealed.toCompleteFootprint.writesExact domain).mpr semantic

/-- Every semantic effect coordinate occurs in the certified footprint. -/
theorem semantic_effect_is_in_footprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {state : State}
    {proposal : Proposal Slot Head Judgment}
    {universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    {footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    (sealed :
      UniverseCompleteFootprint surface state proposal universes footprint)
    {domain : EffectDomain}
    (semantic : surface.Effects state proposal domain) :
    domain ∈ footprint.effects :=
  (sealed.toCompleteFootprint.effectsExact domain).mpr semantic

/-- Every semantic invariant coordinate occurs in the certified footprint. -/
theorem semantic_invariant_is_in_footprint
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain : Type u}
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {state : State}
    {proposal : Proposal Slot Head Judgment}
    {universes :
      TransactionUniverses
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    {footprint :
      TransactionFootprint
        ReadDomain WriteDomain EffectDomain InvariantDomain}
    (sealed :
      UniverseCompleteFootprint surface state proposal universes footprint)
    {domain : InvariantDomain}
    (semantic : surface.InvariantDomains state proposal domain) :
    domain ∈ footprint.invariantDomains :=
  (sealed.toCompleteFootprint.invariantDomainsExact domain).mpr semantic

end Residua.RCC.TransactionFootprint

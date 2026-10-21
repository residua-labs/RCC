import Init

/-!
# RCC FC-1 common sealed snapshot and carrier

RCC's facets are not independent proofs that may be assembled after the fact.
Every facet observation is bound to one semantic snapshot and one concrete
carrier.  The snapshot contains every coordinate whose variation can change an
RCC result:

* epoch;
* canonical history head;
* assumption root;
* address-use registry;
* sealed source window;
* failure model;
* sealed proposal window; and
* implementation bundle.

`CoherentFacetBundle` is indexed by one `SealedSnapshot` and one
`SnapshotCarrier`.  Its observations retain their original snapshot and
carrier, and `BoundFacetEvidence` requires equality to the bundle indices.
Consequently a reduction proof from `H₁`, a resource ledger from `H₂`, and a
reflection proof from `H₃` cannot be spliced into one bundle without first
proving those snapshots and carriers equal.

This module proves only FC-1 structural coherence.  The semantic cross-facet
laws over this common carrier are FC-2.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.FacetSnapshot

universe u

/-- The complete coordinate tuple of one RCC semantic snapshot. -/
structure SnapshotCoordinates
    (Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u) where
  epoch : Epoch
  historyHead : HistoryHead
  assumptionRoot : AssumptionRoot
  addressRegistry : AddressRegistry
  sourceWindow : SourceWindow
  failureModel : FailureModel
  proposalWindow : ProposalWindow
  implementationBundle : ImplementationBundle

/--
The epoch-specific sealing predicate.

FC-1 does not assume how a source/proposal window is sealed.  It consumes the
proof supplied by the corresponding source-window and candidate-window
facets, while making the resulting sealed tuple the common index.
-/
structure SnapshotSeal
    (Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u) where
  IsSealed :
    SnapshotCoordinates
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle →
      Prop

/-- One proof-carrying, immutable RCC snapshot. -/
structure SealedSnapshot
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    (sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle) where
  coordinates :
    SnapshotCoordinates
      Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle
  sealed : sealSpec.IsSealed coordinates

/--
All semantic coordinates projected from one concrete RCC carrier.

The carrier may contain more implementation state, but every coordinate that
can affect an RCC facet must be exposed here and bound to the sealed snapshot.
-/
structure CarrierProjection
    (Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u) where
  epoch : Carrier → Epoch
  historyHead : Carrier → HistoryHead
  assumptionRoot : Carrier → AssumptionRoot
  addressRegistry : Carrier → AddressRegistry
  sourceWindow : Carrier → SourceWindow
  failureModel : Carrier → FailureModel
  proposalWindow : Carrier → ProposalWindow
  implementationBundle : Carrier → ImplementationBundle

/--
One concrete carrier whose complete semantic projection is the sealed
snapshot.  These equalities prevent an untracked carrier from being paired
with a convenient snapshot.
-/
structure SnapshotCarrier
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec) where
  value : Carrier
  epochBound :
    projection.epoch value = snapshot.coordinates.epoch
  historyHeadBound :
    projection.historyHead value = snapshot.coordinates.historyHead
  assumptionRootBound :
    projection.assumptionRoot value = snapshot.coordinates.assumptionRoot
  addressRegistryBound :
    projection.addressRegistry value = snapshot.coordinates.addressRegistry
  sourceWindowBound :
    projection.sourceWindow value = snapshot.coordinates.sourceWindow
  failureModelBound :
    projection.failureModel value = snapshot.coordinates.failureModel
  proposalWindowBound :
    projection.proposalWindow value = snapshot.coordinates.proposalWindow
  implementationBundleBound :
    projection.implementationBundle value =
      snapshot.coordinates.implementationBundle

/-- The eight load-bearing facets of the calibrated RCC formal core. -/
inductive RCCFacet
  | addressKernel
  | groundedEvidence
  | noetherianReduction
  | resourceLedger
  | reflectionStrata
  | runtimeBinding
  | lineageCoalgebra
  | compositionKernel
  deriving DecidableEq, Repr

/--
A facet observation before FC-1 binding.

The observation retains the exact snapshot and carrier on which its payload
was produced.  A label or theorem name alone cannot erase those origins.
-/
structure RawFacetEvidence
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (Payload : RCCFacet → Type u)
    (facet : RCCFacet) where
  snapshot : SealedSnapshot sealSpec
  carrier : Carrier
  payload : Payload facet

/--
Proof that one raw facet observation belongs to the bundle's exact snapshot
and carrier.  Both equalities are required; matching only the history head is
not enough to authorize cross-facet composition.
-/
structure BoundFacetEvidence
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    {facet : RCCFacet}
    (raw : RawFacetEvidence Payload facet) : Prop where
  snapshotBound : raw.snapshot = snapshot
  carrierBound : raw.carrier = carrier.value

/-- A raw facet observation paired with its FC-1 origin proof. -/
structure FacetEvidenceAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    (Payload : RCCFacet → Type u)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    (facet : RCCFacet) where
  raw : RawFacetEvidence Payload facet
  bound : BoundFacetEvidence snapshot carrier raw

/--
The FC-1 bundle.  A total dependent function supplies exactly one evidence
object for every facet, all at the same snapshot and carrier indices.
-/
structure CoherentFacetBundle
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    (Payload : RCCFacet → Type u)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) where
  evidence : (facet : RCCFacet) → FacetEvidenceAt Payload snapshot carrier facet

/-- Every facet observation in a coherent bundle records the bundle snapshot. -/
theorem CoherentFacetBundle.facetSnapshotBound
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (bundle : CoherentFacetBundle Payload snapshot carrier)
    (facet : RCCFacet) :
    (bundle.evidence facet).raw.snapshot = snapshot :=
  (bundle.evidence facet).bound.snapshotBound

/-- Every facet observation in a coherent bundle records the bundle carrier. -/
theorem CoherentFacetBundle.facetCarrierBound
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (bundle : CoherentFacetBundle Payload snapshot carrier)
    (facet : RCCFacet) :
    (bundle.evidence facet).raw.carrier = carrier.value :=
  (bundle.evidence facet).bound.carrierBound

/-- Any two facet observations in a coherent bundle share one exact snapshot. -/
theorem CoherentFacetBundle.facetsShareSnapshot
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (bundle : CoherentFacetBundle Payload snapshot carrier)
    (left right : RCCFacet) :
    (bundle.evidence left).raw.snapshot =
      (bundle.evidence right).raw.snapshot :=
  (bundle.facetSnapshotBound left).trans
    (bundle.facetSnapshotBound right).symm

/-- Any two facet observations in a coherent bundle share one exact carrier. -/
theorem CoherentFacetBundle.facetsShareCarrier
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (bundle : CoherentFacetBundle Payload snapshot carrier)
    (left right : RCCFacet) :
    (bundle.evidence left).raw.carrier =
      (bundle.evidence right).raw.carrier :=
  (bundle.facetCarrierBound left).trans
    (bundle.facetCarrierBound right).symm

/--
The carrier used by any facet projects to all eight coordinates of the common
snapshot.  This is the full FC-1 binding, not merely a shared-head check.
-/
theorem CoherentFacetBundle.facetCarrierProjectsSnapshot
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (bundle : CoherentFacetBundle Payload snapshot carrier)
    (facet : RCCFacet) :
    projection.epoch (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.epoch ∧
      projection.historyHead (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.historyHead ∧
      projection.assumptionRoot (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.assumptionRoot ∧
      projection.addressRegistry (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.addressRegistry ∧
      projection.sourceWindow (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.sourceWindow ∧
      projection.failureModel (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.failureModel ∧
      projection.proposalWindow (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.proposalWindow ∧
      projection.implementationBundle (bundle.evidence facet).raw.carrier =
        snapshot.coordinates.implementationBundle := by
  have carrierBound :=
    (bundle.evidence facet).bound.carrierBound
  constructor
  · exact
      (congrArg projection.epoch carrierBound).trans carrier.epochBound
  constructor
  · exact
      (congrArg projection.historyHead carrierBound).trans
        carrier.historyHeadBound
  constructor
  · exact
      (congrArg projection.assumptionRoot carrierBound).trans
        carrier.assumptionRootBound
  constructor
  · exact
      (congrArg projection.addressRegistry carrierBound).trans
        carrier.addressRegistryBound
  constructor
  · exact
      (congrArg projection.sourceWindow carrierBound).trans
        carrier.sourceWindowBound
  constructor
  · exact
      (congrArg projection.failureModel carrierBound).trans
        carrier.failureModelBound
  constructor
  · exact
      (congrArg projection.proposalWindow carrierBound).trans
        carrier.proposalWindowBound
  · exact
      (congrArg projection.implementationBundle carrierBound).trans
        carrier.implementationBundleBound
  done

/--
General anti-splice theorem: evidence produced at a provably different
snapshot cannot be rebound to the target snapshot/carrier.
-/
theorem differentSnapshotCannotBind
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {targetSnapshot : SealedSnapshot sealSpec}
    {targetCarrier : SnapshotCarrier projection targetSnapshot}
    {facet : RCCFacet}
    {raw : RawFacetEvidence Payload facet}
    (different : raw.snapshot ≠ targetSnapshot) :
    ¬ BoundFacetEvidence targetSnapshot targetCarrier raw := by
  intro bound
  exact different bound.snapshotBound
  done

/--
General anti-splice theorem: evidence produced on a provably different
carrier cannot be rebound even when the semantic snapshot is the same.
-/
theorem differentCarrierCannotBind
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    {targetSnapshot : SealedSnapshot sealSpec}
    {targetCarrier : SnapshotCarrier projection targetSnapshot}
    {facet : RCCFacet}
    {raw : RawFacetEvidence Payload facet}
    (different : raw.carrier ≠ targetCarrier.value) :
    ¬ BoundFacetEvidence targetSnapshot targetCarrier raw := by
  intro bound
  exact different bound.carrierBound
  done

end Residua.RCC.FacetSnapshot

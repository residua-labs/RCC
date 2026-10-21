import RCC.ComponentClosureFamily
import RCC.EvidenceReplayability
import RCC.FacetCoherence
import RCC.GlobalIntentCoverage
import RCC.SeamIntegratedFamily

/-!
# C4 integrated composition gluing

C2 supplies exact integrated realizations for a sealed declared seam family.
C3 supplies the independent sufficiency theorem from local component/seam
claims to one fixed global intent.  C4 composes those layers.

This module does not add a second gluing premise.  It binds each coherence seam
to one concrete `SeamWorld`, derives the C3 local closure evidence from an
integrated family, and applies the existing C3 intent contract with
`world.globalClosed` as its conclusion.

The seam list remains the one declared by `CoherenceWorld`; production graph
extraction, runtime evidence stamps, support rooting, and evidence
replayability remain separate global-closure prerequisites.
-/

namespace Residua.RCC.CompositionGluing

open Residua.RCC.ComponentClosureFamily
open Residua.RCC.EvidenceReplayability
open Residua.RCC.FacetCoherence
open Residua.RCC.FacetSnapshot
open Residua.RCC.GlobalIntentCoverage
open Residua.RCC.SeamExactness
open Residua.RCC.SeamFamily
open Residua.RCC.SeamIntegratedFamily

universe u

/--
Interpret each declared coherence seam through one concrete seam world.

`exactSound` is the instance bridge from the concrete C2 certificate to
the local seam predicate consumed by C3.
-/
structure CoherenceSeamBinding (world : CoherenceWorld.{u}) where
  seamWorld : world.Seam → SeamWorld.{u}
  exactSound :
    ∀ seam,
      ExactSeamAt (seamWorld seam) →
      world.seamExact seam

/-- The declared coherence seam list as a C2 seam scope. -/
def CoherenceSeamBinding.scope
    {world : CoherenceWorld}
    (binding : CoherenceSeamBinding world) :
    SeamScope where
  Seam := world.Seam
  world := binding.seamWorld
  InScope := fun seam => seam ∈ world.seams
  enumeration := world.seams

/-- The derived scope is sealed by construction against the declared list. -/
def CoherenceSeamBinding.sealed
    {world : CoherenceWorld}
    (binding : CoherenceSeamBinding world) :
    SealedSeamUniverse binding.scope where
  sound := by
    intro seam listed
    exact listed
  complete := by
    intro seam inScope
    exact inScope

/--
The complete local evidence used by C4.

This is data rather than a Prop existential: every per-seam integrated
realization remains projectable from `seams`.
-/
structure IntegratedCompositionEvidence
    (world : CoherenceWorld)
    (binding : CoherenceSeamBinding world) where
  componentBinding : CoherenceComponentBinding world
  components : ClosedComponentFamily componentBinding
  seams :
    SealedIntegratedSeamFamily binding.scope

/--
Mechanical bridge from concrete integrated seams to C3 local closure
evidence.
-/
def IntegratedCompositionEvidence.toClosureEvidence
    {world : CoherenceWorld}
    {binding : CoherenceSeamBinding world}
    (evidence : IntegratedCompositionEvidence world binding) :
    CompositionClosureEvidence world where
  componentsClosed := evidence.components.componentsClosed
  seamsExact := by
    intro seam listed
    exact
      binding.exactSound seam
        (evidence.seams.inScopeExact seam listed)

/--
C4 headline: integrated C2 local evidence plus the C3 one-way global intent
coverage contract yields the declared global closure proposition.
-/
theorem IntegratedCompositionEvidence.gluesGlobalClosed
    {world : CoherenceWorld}
    {binding : CoherenceSeamBinding world}
    (evidence : IntegratedCompositionEvidence world binding)
    (contract :
      CompositionIntentContract
        world
        world.componentClosed
        world.seamExact
        world.globalClosed) :
    world.globalClosed :=
  evidence.toClosureEvidence.coversGlobalIntent contract

/-!
## FC-1-bound integrated composition

The legacy C4 theorem above accepts an independently supplied `world` and
intent contract.  The dependent bridge below is the load-bearing form used
when C4 is part of the facet calculus: both the composition law and the local
component/seam evidence are indexed by the world projected from one exact
FC-1 carrier.  No production closure claim is added; this only prevents a C4
proof assembled for one semantic carrier from being paired with an FC-2
composition surface decoded at another snapshot/carrier.
-/

/--
Integrated C4 evidence before FC-1 origin binding.  The evidence retains the
snapshot and concrete carrier at which it was produced; its semantic world is
therefore the world projected from that carrier.
-/
structure RawIntegratedCompositionEvidence
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {Payload : RCCFacet → Type u}
    (adapter : FacetSemanticAdapter Carrier Payload) where
  snapshot : SealedSnapshot sealSpec
  carrier : Carrier
  seamBinding :
    CoherenceSeamBinding (adapter.index.world carrier)
  integrated :
    IntegratedCompositionEvidence
      (adapter.index.world carrier) seamBinding

/-- Exact FC-1 origin proof for one raw integrated C4 evidence packet. -/
structure BoundIntegratedCompositionEvidence
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
    {adapter : FacetSemanticAdapter Carrier Payload}
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    (raw : RawIntegratedCompositionEvidence adapter) : Prop where
  snapshotBound : raw.snapshot = snapshot
  carrierBound : raw.carrier = carrier.value

/--
Integrated C4 evidence whose raw origin and FC-2 composition law are both
bound to one exact FC-1 bundle, snapshot, and carrier.
-/
structure SnapshotBoundIntegratedCompositionEvidence
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
    (adapter : FacetSemanticAdapter Carrier Payload) where
  coherence : FacetCoherenceCertificate bundle adapter
  raw : RawIntegratedCompositionEvidence adapter
  bound : BoundIntegratedCompositionEvidence snapshot carrier raw

/--
The C4 local families glue only through the composition law decoded from the
same FC-1 snapshot/carrier bundle.
-/
theorem SnapshotBoundIntegratedCompositionEvidence.gluesAtSnapshot
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (evidence :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter) :
    (adapter.index.world carrier.value).globalClosed := by
  have componentsClosed :=
    evidence.raw.integrated.components.componentsClosed
  have seamsExact :=
    evidence.raw.integrated.toClosureEvidence.seamsExact
  rw [evidence.bound.carrierBound] at componentsClosed seamsExact
  exact
    evidence.coherence.composition.glues
      componentsClosed
      seamsExact

/-!
## C4-R2 typed composition-universe coverage

An integrated family over a self-declared list proves only that list.  The
FC-1 composition surface carries the stronger typed coverage claim that every
component and seam inhabiting the carrier world occurs in those lists.  C4-R2
retains that claim in the global conclusion instead of silently discarding it.
-/

/-- Exact typed coverage of the component and seam universes at one carrier. -/
structure TypedCompositionUniverseCoverage
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (_composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter) : Prop where
  everyComponentListed :
    ∀ component,
      component ∈ (adapter.index.world carrier.value).components
  everySeamListed :
    ∀ seam,
      seam ∈ (adapter.index.world carrier.value).seams

/-- The snapshot-bound C4 result retaining typed universe coverage. -/
structure UniverseCoveredGlobalClosure
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter) : Prop where
  globalClosed : (adapter.index.world carrier.value).globalClosed
  universeCovered : TypedCompositionUniverseCoverage composition

/--
C4-R2 headline: the same FC-1 composition law supplies both gluing and exact
typed coverage; neither field is reconstructed from the self-declared family.
-/
theorem SnapshotBoundIntegratedCompositionEvidence.gluesWithUniverseCoverageAtSnapshot
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter) :
    UniverseCoveredGlobalClosure composition where
  globalClosed := composition.gluesAtSnapshot
  universeCovered :=
    { everyComponentListed :=
        composition.coherence.composition.componentCoverage
      everySeamListed :=
        composition.coherence.composition.seamCoverage }

/-!
## C4-R1 replay-gated integrated composition

FC-1 origin binding prevents snapshot splicing, but it does not by itself
prove that the terminal component/seam judgments consumed by C4 still have
live archive evidence.  The association below names one replay judgment for
every declared local conclusion and proves that each one is live mandatory in
the exact replay system indexed by the same snapshot and carrier.
-/

/-- Every local terminal conclusion consumed by C4 has a live mandatory key. -/
structure IntegratedCompositionReplayAssociation
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter)
    (replay : ReplaySystem snapshot carrier) where
  componentJudgment :
    (adapter.index.world carrier.value).Component → replay.Judgment
  seamJudgment :
    (adapter.index.world carrier.value).Seam → replay.Judgment
  componentLiveMandatory :
    ∀ component,
      component ∈ (adapter.index.world carrier.value).components →
        replay.LiveMandatoryAt (componentJudgment component)
  seamLiveMandatory :
    ∀ seam,
      seam ∈ (adapter.index.world carrier.value).seams →
        replay.LiveMandatoryAt (seamJudgment seam)

/--
The replay gate for one snapshot-bound C4 packet.  Merely retaining a receipt
address is insufficient: `EvidenceReplayabilityAt` requires present bytes,
closed dependencies, exact snapshot coordinates, and replay acceptance for
all and only live mandatory judgments.
-/
structure ReplayGatedIntegratedCompositionEvidence
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    (composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter)
    (replay : ReplaySystem snapshot carrier) where
  replayability : EvidenceReplayabilityAt replay
  association : IntegratedCompositionReplayAssociation composition replay

/-- A declared component conclusion has replayable evidence at this snapshot. -/
def ReplayGatedIntegratedCompositionEvidence.componentReplayable
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    {composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter}
    {replay : ReplaySystem snapshot carrier}
    (packet : ReplayGatedIntegratedCompositionEvidence composition replay)
    (component : (adapter.index.world carrier.value).Component)
    (listed : component ∈ (adapter.index.world carrier.value).components) :
    ReplayableJudgmentAt replay
      (packet.association.componentJudgment component) :=
  packet.replayability.replayable _
    (packet.association.componentLiveMandatory component listed)

/-- A declared seam conclusion has replayable evidence at this snapshot. -/
def ReplayGatedIntegratedCompositionEvidence.seamReplayable
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    {composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter}
    {replay : ReplaySystem snapshot carrier}
    (packet : ReplayGatedIntegratedCompositionEvidence composition replay)
    (seam : (adapter.index.world carrier.value).Seam)
    (listed : seam ∈ (adapter.index.world carrier.value).seams) :
    ReplayableJudgmentAt replay
      (packet.association.seamJudgment seam) :=
  packet.replayability.replayable _
    (packet.association.seamLiveMandatory seam listed)

/--
The replay-gated C4 conclusion.  Unlike bare `world.globalClosed`, this record
retains replay witnesses for every component and seam conclusion consumed by
the gluing proof.
-/
structure ReplayGatedGlobalClosure
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    {composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter}
    {replay : ReplaySystem snapshot carrier}
    (packet : ReplayGatedIntegratedCompositionEvidence composition replay) : Prop where
  globalClosed : (adapter.index.world carrier.value).globalClosed
  componentsReplayable :
    ∀ component,
      component ∈ (adapter.index.world carrier.value).components →
        Nonempty
          (ReplayableJudgmentAt replay
            (packet.association.componentJudgment component))
  seamsReplayable :
    ∀ seam,
      seam ∈ (adapter.index.world carrier.value).seams →
        Nonempty
          (ReplayableJudgmentAt replay
            (packet.association.seamJudgment seam))

/--
C4-R1 headline: construct the replay-gated global conclusion, materially
retaining every local replay witness rather than returning a bare legacy
closure proposition.
-/
theorem ReplayGatedIntegratedCompositionEvidence.gluesReplayableAtSnapshot
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
    {bundle : CoherentFacetBundle Payload snapshot carrier}
    {adapter : FacetSemanticAdapter Carrier Payload}
    {composition :
      SnapshotBoundIntegratedCompositionEvidence bundle adapter}
    {replay : ReplaySystem snapshot carrier}
    (packet : ReplayGatedIntegratedCompositionEvidence composition replay) :
    ReplayGatedGlobalClosure packet where
  globalClosed := composition.gluesAtSnapshot
  componentsReplayable := by
    intro component listed
    exact ⟨packet.componentReplayable component listed⟩
  seamsReplayable := by
    intro seam listed
    exact ⟨packet.seamReplayable seam listed⟩

end Residua.RCC.CompositionGluing

import RCC.FacetSnapshot

/-!
# RCC FC-2 cross-facet coherence

FC-1 places all RCC facet observations at one sealed snapshot and concrete
carrier.  That structural fact is necessary but not sufficient: unrelated
facet proofs at the same snapshot still form only a collage.

FC-2 adds seven proof-carrying bridge laws:

* address identity is respected by reduction;
* admitted evidence is grounded;
* every reduction has an explicit resource delta;
* verification is strictly reflection-stratified;
* migration terminates or carries every active resource;
* every runtime step refines a formal reduction; and
* complete local closure plus exact seams implies global closure.

Every bridge contains a `BoundFacetPairAt` origin.  Its two observations are
therefore bound to the same FC-1 snapshot and carrier.  A bridge assembled
from different snapshots cannot be certified, even if its semantic claim is
independently true.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.FacetCoherence

open Residua.RCC.FacetSnapshot

universe u

/--
The semantic vocabulary shared by the seven FC-2 bridge laws.

Migration is evaluated at the pre-state sealed snapshot.  Its successor state
is data certified by that snapshot; it is not evidence imported from an
unbound successor snapshot.
-/
structure CoherenceWorld where
  State : Type u
  Address : Type u
  stateEquivalent : State → State → Prop
  stateAddress : State → Address
  reduces : State → State → Prop

  Evidence : Type u
  AdmittedEvent : Type u
  grounded : Evidence → Prop
  admits : Evidence → AdmittedEvent → Prop

  ResourceToken : Type u
  activeResources : State → List ResourceToken

  Verifier : Type u
  Artifact : Type u
  verifierLevel : Verifier → Nat
  artifactLevel : Artifact → Nat
  verifies : Verifier → Artifact → Prop

  migrates : State → State → Prop
  terminalAt : State → ResourceToken → Prop
  carries : ResourceToken → ResourceToken → Prop

  RuntimeState : Type u
  runtimeStep : RuntimeState → RuntimeState → Prop
  abstractState : RuntimeState → State

  Component : Type u
  Seam : Type u
  components : List Component
  seams : List Seam
  componentClosed : Component → Prop
  seamExact : Seam → Prop
  globalClosed : Prop

/--
Two raw facet observations bound to one exact FC-1 snapshot and carrier.

This is the origin certificate shared by every semantic FC-2 law.
-/
structure BoundFacetPairAt
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
    {left right : RCCFacet}
    (leftRaw : RawFacetEvidence Payload left)
    (rightRaw : RawFacetEvidence Payload right) : Prop where
  leftBound : BoundFacetEvidence snapshot carrier leftRaw
  rightBound : BoundFacetEvidence snapshot carrier rightRaw

/-- Extract one same-index bridge origin from an FC-1 coherent bundle. -/
def CoherentFacetBundle.pairAt
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
    BoundFacetPairAt
      snapshot carrier
      (bundle.evidence left).raw
      (bundle.evidence right).raw where
  leftBound := (bundle.evidence left).bound
  rightBound := (bundle.evidence right).bound

/--
No bridge whose endpoints were observed at different snapshots has an FC-2
origin at any target snapshot/carrier.
-/
theorem differentPairSnapshotsCannotBind
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
    {left right : RCCFacet}
    {leftRaw : RawFacetEvidence Payload left}
    {rightRaw : RawFacetEvidence Payload right}
    (different : leftRaw.snapshot ≠ rightRaw.snapshot) :
    ∀ (snapshot : SealedSnapshot sealSpec)
      (carrier : SnapshotCarrier projection snapshot),
      ¬ BoundFacetPairAt snapshot carrier leftRaw rightRaw := by
  intro snapshot carrier pair
  exact
    different
      (pair.leftBound.snapshotBound.trans
        pair.rightBound.snapshotBound.symm)
  done

/-- Address identity is semantic identity, and reduction respects it. -/
structure AddressReductionLaw (world : CoherenceWorld) : Prop where
  addressSound :
    ∀ left right,
      world.stateAddress left = world.stateAddress right →
      world.stateEquivalent left right
  reductionCongruent :
    ∀ left right left' right',
      world.stateEquivalent left right →
      world.reduces left left' →
      world.reduces right right' →
      world.stateEquivalent left' right'

/-- No event can be admitted from evidence lacking a grounding proof. -/
structure EvidenceAdmissionLaw (world : CoherenceWorld) : Prop where
  admittedGrounded :
    ∀ evidence event,
      world.admits evidence event →
      world.grounded evidence

/--
A structural resource delta.  `retained` is the common ledger spine;
`consumed` is removed and `produced` is added.
-/
structure ResourceDelta (Token : Type u) where
  consumed : List Token
  retained : List Token
  produced : List Token

/-- The fixed ledger meaning of one proposed resource delta. -/
structure DeltaLedgerProof
    (world : CoherenceWorld)
    (before after : world.State)
    (delta : ResourceDelta world.ResourceToken) : Prop where
  beforeBound :
    world.activeResources before =
      delta.consumed ++ delta.retained
  afterBound :
    world.activeResources after =
      delta.produced ++ delta.retained

/--
One explicit resource-delta witness for a particular state transition.

The two decomposition equalities are the ledger semantics; an instance cannot
replace them with an arbitrary `deltaValid := True` predicate.
-/
structure ResourceDeltaCertificate
    (world : CoherenceWorld)
    (before after : world.State) where
  delta : ResourceDelta world.ResourceToken
  ledger : DeltaLedgerProof world before after delta

/-- Every formal reduction computes a proof-carrying resource delta. -/
structure ReductionResourceLaw (world : CoherenceWorld) where
  deltaFor :
    ∀ before after,
      world.reduces before after →
      ResourceDeltaCertificate world before after

/-- Verification authority is strictly above the artifact it certifies. -/
structure ReflectionVerificationLaw (world : CoherenceWorld) : Prop where
  verifierAboveArtifact :
    ∀ verifier artifact,
      world.verifies verifier artifact →
      world.artifactLevel artifact < world.verifierLevel verifier

/--
Every active resource of a migrating state is either terminal at the
pre-state or carried to an active successor token.
-/
structure MigrationResourceLaw (world : CoherenceWorld) : Prop where
  conserves :
    ∀ before after,
      world.migrates before after →
      ∀ token,
        token ∈ world.activeResources before →
        world.terminalAt before token ∨
          ∃ successor,
            successor ∈ world.activeResources after ∧
            world.carries token successor

/-- Every concrete runtime transition refines one formal reduction. -/
structure RuntimeRefinementLaw (world : CoherenceWorld) : Prop where
  refines :
    ∀ before after,
      world.runtimeStep before after →
      world.reduces
        (world.abstractState before)
        (world.abstractState after)

/--
The component and seam enumerations cover their declared universes, and
closed components plus exact seams entail the global closure claim.
-/
structure CompositionLaw (world : CoherenceWorld) : Prop where
  componentCoverage :
    ∀ component,
      component ∈ world.components
  seamCoverage :
    ∀ seam,
      seam ∈ world.seams
  glues :
    (∀ component,
      component ∈ world.components →
      world.componentClosed component) →
    (∀ seam,
      seam ∈ world.seams →
      world.seamExact seam) →
    world.globalClosed

/--
The type-level semantic adapter vocabulary.

The world is a function of the concrete FC-1 carrier.  Intermediate token
families force every bridge to consume proof produced by both endpoint
surfaces rather than accepting a detached theorem about another world.
-/
structure FacetSemanticIndex (Carrier : Type u) where
  world : Carrier → CoherenceWorld.{u}

  GroundingToken :
    (carrier : Carrier) →
    (world carrier).Evidence →
    Type u
  DeltaToken :
    (carrier : Carrier) →
    (before after : (world carrier).State) →
    ResourceDelta (world carrier).ResourceToken →
    Type u
  VerificationToken :
    (carrier : Carrier) →
    (world carrier).Verifier →
    (world carrier).Artifact →
    Type u
  MigrationToken :
    (carrier : Carrier) →
    (before after : (world carrier).State) →
    (world carrier).ResourceToken →
    Type u
  RuntimeToken :
    (carrier : Carrier) →
    (before after : (world carrier).RuntimeState) →
    Type u
  CompositionToken :
    (carrier : Carrier) →
    Type u

/-- Address-side proof surface. -/
structure AddressFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  addressSound :
    ∀ left right,
      (index.world carrier).stateAddress left =
          (index.world carrier).stateAddress right →
      (index.world carrier).stateEquivalent left right

/-- Grounding-side proof surface. -/
structure EvidenceFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  groundingSound :
    ∀ evidence,
      index.GroundingToken carrier evidence →
      (index.world carrier).grounded evidence
  verificationAccepted :
    ∀ verifier artifact,
      (index.world carrier).verifies verifier artifact →
      index.VerificationToken carrier verifier artifact
  compositionSound :
    index.CompositionToken carrier →
    (index.world carrier).globalClosed

/--
Reduction-side proof surface.  It creates the bridge tokens later checked by
the evidence, resource, and runtime endpoint surfaces.
-/
structure ReductionFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  reductionCongruent :
    ∀ left right left' right',
      (index.world carrier).stateEquivalent left right →
      (index.world carrier).reduces left left' →
      (index.world carrier).reduces right right' →
      (index.world carrier).stateEquivalent left' right'
  admissionGrounding :
    ∀ evidence event,
      (index.world carrier).admits evidence event →
      index.GroundingToken carrier evidence
  deltaFor :
    ∀ before after,
      (index.world carrier).reduces before after →
      Σ delta,
        index.DeltaToken carrier before after delta
  runtimeSound :
    ∀ before after,
      index.RuntimeToken carrier before after →
      (index.world carrier).reduces
        ((index.world carrier).abstractState before)
        ((index.world carrier).abstractState after)

/-- Resource-ledger proof surface. -/
structure ResourceFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  deltaSound :
    ∀ before after delta,
      index.DeltaToken carrier before after delta →
      DeltaLedgerProof (index.world carrier) before after delta
  migrationSound :
    ∀ before after token,
      index.MigrationToken carrier before after token →
      (index.world carrier).terminalAt before token ∨
        ∃ successor,
          successor ∈ (index.world carrier).activeResources after ∧
          (index.world carrier).carries token successor

/-- Reflection-side proof surface. -/
structure ReflectionFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  verificationStratified :
    ∀ verifier artifact,
      index.VerificationToken carrier verifier artifact →
      (index.world carrier).artifactLevel artifact <
        (index.world carrier).verifierLevel verifier

/-- Runtime-side proof surface. -/
structure RuntimeFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  refinementToken :
    ∀ before after,
      (index.world carrier).runtimeStep before after →
      index.RuntimeToken carrier before after

/-- Lineage/migration-side proof surface. -/
structure LineageFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  migrationToken :
    ∀ before after,
      (index.world carrier).migrates before after →
      ∀ token,
        token ∈ (index.world carrier).activeResources before →
        index.MigrationToken carrier before after token

/-- Composition-side proof surface. -/
structure CompositionFacetSurface
    {Carrier : Type u}
    (index : FacetSemanticIndex Carrier)
    (carrier : Carrier) : Type (u + 1) where
  componentCoverage :
    ∀ component,
      component ∈ (index.world carrier).components
  seamCoverage :
    ∀ seam,
      seam ∈ (index.world carrier).seams
  gluingToken :
    (∀ component,
      component ∈ (index.world carrier).components →
      (index.world carrier).componentClosed component) →
    (∀ seam,
      seam ∈ (index.world carrier).seams →
      (index.world carrier).seamExact seam) →
    index.CompositionToken carrier

/--
Decode raw facet payloads into carrier-indexed semantic proof surfaces.

Failure to decode is an evidence gap.  In particular, a payload for another
carrier/world cannot be ignored and replaced by an independently supplied
law.  The eight decoders are separate fields so no dependent pattern match
can silently transport a proof between facet kinds.
-/
structure FacetSemanticAdapter
    (Carrier : Type u)
    (Payload : RCCFacet → Type u) where
  index : FacetSemanticIndex Carrier
  decodeAddress :
    (carrier : Carrier) →
    Payload .addressKernel →
    Option (AddressFacetSurface index carrier)
  decodeEvidence :
    (carrier : Carrier) →
    Payload .groundedEvidence →
    Option (EvidenceFacetSurface index carrier)
  decodeReduction :
    (carrier : Carrier) →
    Payload .noetherianReduction →
    Option (ReductionFacetSurface index carrier)
  decodeResource :
    (carrier : Carrier) →
    Payload .resourceLedger →
    Option (ResourceFacetSurface index carrier)
  decodeReflection :
    (carrier : Carrier) →
    Payload .reflectionStrata →
    Option (ReflectionFacetSurface index carrier)
  decodeRuntime :
    (carrier : Carrier) →
    Payload .runtimeBinding →
    Option (RuntimeFacetSurface index carrier)
  decodeLineage :
    (carrier : Carrier) →
    Payload .lineageCoalgebra →
    Option (LineageFacetSurface index carrier)
  decodeComposition :
    (carrier : Carrier) →
    Payload .compositionKernel →
    Option (CompositionFacetSurface index carrier)

/--
The complete FC-2 certificate.

There are no independent `world` or law fields.  All eight surfaces must
decode from the exact payloads of one FC-1 bundle at `carrier.value`; the seven
laws below are then mechanically derived from those endpoint surfaces.
-/
structure FacetCoherenceCertificate
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
  addressSurface :
    AddressFacetSurface adapter.index carrier.value
  addressDecoded :
    adapter.decodeAddress
        carrier.value (bundle.evidence .addressKernel).raw.payload =
      some addressSurface

  evidenceSurface :
    EvidenceFacetSurface adapter.index carrier.value
  evidenceDecoded :
    adapter.decodeEvidence
        carrier.value (bundle.evidence .groundedEvidence).raw.payload =
      some evidenceSurface

  reductionSurface :
    ReductionFacetSurface adapter.index carrier.value
  reductionDecoded :
    adapter.decodeReduction
        carrier.value (bundle.evidence .noetherianReduction).raw.payload =
      some reductionSurface

  resourceSurface :
    ResourceFacetSurface adapter.index carrier.value
  resourceDecoded :
    adapter.decodeResource
        carrier.value (bundle.evidence .resourceLedger).raw.payload =
      some resourceSurface

  reflectionSurface :
    ReflectionFacetSurface adapter.index carrier.value
  reflectionDecoded :
    adapter.decodeReflection
        carrier.value (bundle.evidence .reflectionStrata).raw.payload =
      some reflectionSurface

  runtimeSurface :
    RuntimeFacetSurface adapter.index carrier.value
  runtimeDecoded :
    adapter.decodeRuntime
        carrier.value (bundle.evidence .runtimeBinding).raw.payload =
      some runtimeSurface

  lineageSurface :
    LineageFacetSurface adapter.index carrier.value
  lineageDecoded :
    adapter.decodeLineage
        carrier.value (bundle.evidence .lineageCoalgebra).raw.payload =
      some lineageSurface

  compositionSurface :
    CompositionFacetSurface adapter.index carrier.value
  compositionDecoded :
    adapter.decodeComposition
        carrier.value (bundle.evidence .compositionKernel).raw.payload =
      some compositionSurface

/-- Address/reduction law derived from the exact two endpoint payloads. -/
def FacetCoherenceCertificate.addressReduction
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    AddressReductionLaw (adapter.index.world carrier.value) where
  addressSound :=
    certificate.addressSurface.addressSound
  reductionCongruent :=
    certificate.reductionSurface.reductionCongruent

/-- Evidence/admission law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.evidenceAdmission
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    EvidenceAdmissionLaw (adapter.index.world carrier.value) where
  admittedGrounded := by
    intro evidence event admitted
    exact
      certificate.evidenceSurface.groundingSound
        evidence
        (certificate.reductionSurface.admissionGrounding
          evidence event admitted)

/-- Reduction/resource law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.reductionResource
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    ReductionResourceLaw (adapter.index.world carrier.value) where
  deltaFor := by
    intro before after step
    obtain ⟨delta, token⟩ :=
      certificate.reductionSurface.deltaFor
        before after step
    exact
      { delta := delta
        ledger :=
          certificate.resourceSurface.deltaSound
            before after delta token }

/-- Reflection/verification law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.reflectionVerification
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    ReflectionVerificationLaw (adapter.index.world carrier.value) where
  verifierAboveArtifact := by
    intro verifier artifact accepted
    exact
      certificate.reflectionSurface.verificationStratified
        verifier artifact
        (certificate.evidenceSurface.verificationAccepted
          verifier artifact accepted)

/-- Migration/resource law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.migrationResource
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    MigrationResourceLaw (adapter.index.world carrier.value) where
  conserves := by
    intro before after migration token active
    exact
      certificate.resourceSurface.migrationSound
        before after token
        (certificate.lineageSurface.migrationToken
          before after migration token active)

/-- Runtime refinement law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.runtimeRefinement
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    RuntimeRefinementLaw (adapter.index.world carrier.value) where
  refines := by
    intro before after step
    exact
      certificate.reductionSurface.runtimeSound
        before after
        (certificate.runtimeSurface.refinementToken
          before after step)

/-- Composition law derived from its two endpoint payloads. -/
def FacetCoherenceCertificate.composition
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
    (certificate : FacetCoherenceCertificate bundle adapter) :
    CompositionLaw (adapter.index.world carrier.value) where
  componentCoverage :=
    certificate.compositionSurface.componentCoverage
  seamCoverage :=
    certificate.compositionSurface.seamCoverage
  glues := by
    intro componentsClosed seamsExact
    exact
      certificate.evidenceSurface.compositionSound
        (certificate.compositionSurface.gluingToken
          componentsClosed seamsExact)

/-- Equal addresses produce semantically equivalent reduction successors. -/
theorem addressedReductionsRemainEquivalent
    {world : CoherenceWorld}
    (law : AddressReductionLaw world)
    {left right left' right' : world.State}
    (sameAddress : world.stateAddress left = world.stateAddress right)
    (leftStep : world.reduces left left')
    (rightStep : world.reduces right right') :
    world.stateEquivalent left' right' :=
  law.reductionCongruent
    left right left' right'
    (law.addressSound left right sameAddress)
    leftStep rightStep

/-- Admission exposes the grounding fact used by its certificate. -/
theorem admittedEvidenceIsGrounded
    {world : CoherenceWorld}
    (law : EvidenceAdmissionLaw world)
    {evidence : world.Evidence}
    {event : world.AdmittedEvent}
    (admitted : world.admits evidence event) :
    world.grounded evidence :=
  law.admittedGrounded evidence event admitted

/-- Every reduction computes its explicit resource-delta certificate. -/
def reductionResourceCertificate
    {world : CoherenceWorld}
    (law : ReductionResourceLaw world)
    {before after : world.State}
    (step : world.reduces before after) :
    ResourceDeltaCertificate world before after :=
  law.deltaFor before after step

/-- The computed resource certificate witnesses delta existence. -/
theorem reductionHasResourceDelta
    {world : CoherenceWorld}
    (law : ReductionResourceLaw world)
    {before after : world.State}
    (step : world.reduces before after) :
    ∃ delta : ResourceDelta world.ResourceToken,
      world.activeResources before =
          delta.consumed ++ delta.retained ∧
        world.activeResources after =
          delta.produced ++ delta.retained :=
  let certificate := reductionResourceCertificate law step
  ⟨certificate.delta,
    certificate.ledger.beforeBound,
    certificate.ledger.afterBound⟩

/-- Every accepted verification is strictly stratified. -/
theorem acceptedVerificationIsStratified
    {world : CoherenceWorld}
    (law : ReflectionVerificationLaw world)
    {verifier : world.Verifier}
    {artifact : world.Artifact}
    (accepted : world.verifies verifier artifact) :
    world.artifactLevel artifact < world.verifierLevel verifier :=
  law.verifierAboveArtifact verifier artifact accepted

/-- Migration exposes the terminal-or-carried disposition of each old token. -/
theorem migrationConservesResource
    {world : CoherenceWorld}
    (law : MigrationResourceLaw world)
    {before after : world.State}
    (migration : world.migrates before after)
    {token : world.ResourceToken}
    (active : token ∈ world.activeResources before) :
    world.terminalAt before token ∨
      ∃ successor,
        successor ∈ world.activeResources after ∧
        world.carries token successor :=
  law.conserves before after migration token active

/-- A runtime transition always projects to the certified formal reduction. -/
theorem runtimeTransitionRefinesFormal
    {world : CoherenceWorld}
    (law : RuntimeRefinementLaw world)
    {before after : world.RuntimeState}
    (step : world.runtimeStep before after) :
    world.reduces
      (world.abstractState before)
      (world.abstractState after) :=
  law.refines before after step

/-- Complete local closure and exact seams glue to the global closure claim. -/
theorem componentsAndSeamsGlue
    {world : CoherenceWorld}
    (law : CompositionLaw world)
    (componentsClosed :
      ∀ component,
        component ∈ world.components →
        world.componentClosed component)
    (seamsExact :
      ∀ seam,
        seam ∈ world.seams →
        world.seamExact seam) :
    world.globalClosed :=
  law.glues componentsClosed seamsExact

/-- A named FC-2 refusal for a reduction missing its resource delta. -/
inductive ResourceBridgeResidue
  | resourceDeltaMissing
  deriving DecidableEq, Repr

/-- A reduction is certified only together with its resource delta. -/
structure CertifiedReductionResource
    (world : CoherenceWorld)
    (before after : world.State) where
  step : world.reduces before after
  delta : ResourceDeltaCertificate world before after

/-- Total validation of one candidate reduction/resource bridge. -/
inductive ResourceBridgeValidation
    (world : CoherenceWorld)
    (before after : world.State)
  | certified :
      CertifiedReductionResource world before after →
      ResourceBridgeValidation world before after
  | refused :
      ResourceBridgeResidue →
      ResourceBridgeValidation world before after

/--
Absence of a resource delta is a named refusal, never an implicitly conserved
transition.
-/
def validateResourceBridge
    {world : CoherenceWorld}
    {before after : world.State}
    (step : world.reduces before after)
    (candidate : Option (ResourceDeltaCertificate world before after)) :
    ResourceBridgeValidation world before after :=
  match candidate with
  | some delta =>
      .certified { step := step, delta := delta }
  | none =>
      .refused .resourceDeltaMissing

theorem missingResourceDeltaRefused
    {world : CoherenceWorld}
    {before after : world.State}
    (step : world.reduces before after) :
    validateResourceBridge step none =
      ResourceBridgeValidation.refused .resourceDeltaMissing :=
  rfl

end Residua.RCC.FacetCoherence

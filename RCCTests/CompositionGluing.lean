import RCC.CompositionGluing
import RCCTests.ComponentClosureFamily
import RCCTests.FacetCoherence
import RCCTests.SeamIntegratedFamily

namespace Residua.RCC.CompositionGluing.Tests

open Residua.RCC.CompositionGluing
open Residua.RCC.ComponentClosureFamily
open Residua.RCC.EvidenceReplayability
open Residua.RCC.FacetCoherence
open Residua.RCC.FacetSnapshot
open Residua.RCC.GlobalIntentCoverage
open Residua.RCC.SeamExactness
open Residua.RCC.SeamIntegratedFamily

namespace Positive

abbrev World := FacetCoherence.Tests.world

def seamBinding : CoherenceSeamBinding World where
  seamWorld := fun _ =>
    SeamExactness.Tests.Identity.world
  exactSound := by
    intro seam exact
    cases seam
    exact .shared

def seamRealization :
    IntegratedSeamRealization
      (seamBinding.scope.world FacetCoherence.Tests.Seam.shared) :=
  SeamIntegratedFamily.Tests.Positive.realization

def seamFamily :
    SealedIntegratedSeamFamily seamBinding.scope where
  sealed := seamBinding.sealed
  realization := by
    intro seam listed
    cases seam
    exact seamRealization

def evidence :
    IntegratedCompositionEvidence World seamBinding where
  componentBinding := ComponentClosureFamily.Tests.Positive.binding
  components := ComponentClosureFamily.Tests.Positive.family
  seams := seamFamily

def globalContract :
    CompositionIntentContract
      World
      World.componentClosed
      World.seamExact
      World.globalClosed where
  componentClosedSound := by
    intro component listed closed
    exact closed
  seamExactSound := by
    intro seam listed exact
    exact exact
  localClaimsSuffice := by
    intro components seams
    exact .proven

end Positive

theorem integrated_local_evidence_constructs_c3_evidence :
    CompositionClosureEvidence Positive.World :=
  Positive.evidence.toClosureEvidence

theorem integrated_components_and_seams_glue_global_closed :
    Positive.World.globalClosed :=
  Positive.evidence.gluesGlobalClosed Positive.globalContract

def rawIntegratedH1 :
    RawIntegratedCompositionEvidence
      (sealSpec := FacetCoherence.Tests.sealSpec)
      FacetCoherence.Tests.adapter where
  snapshot := FacetCoherence.Tests.snapshotH1
  carrier := FacetCoherence.Tests.carrierH1Value
  seamBinding := Positive.seamBinding
  integrated := Positive.evidence

def snapshotBoundEvidence :
    SnapshotBoundIntegratedCompositionEvidence
      FacetCoherence.Tests.bundleH1 FacetCoherence.Tests.adapter where
  coherence := FacetCoherence.Tests.coherence
  raw := rawIntegratedH1
  bound :=
    { snapshotBound := rfl
      carrierBound := rfl }

/--
The integrated component/seam families and the gluing law are consumed at one
FC-1 carrier rather than through an independently supplied world contract.
-/
theorem integrated_evidence_glues_at_fc1_snapshot :
    (FacetCoherence.Tests.adapter.index.world
      FacetCoherence.Tests.carrierH1.value).globalClosed :=
  snapshotBoundEvidence.gluesAtSnapshot

def universeCoveredEvidence :
    UniverseCoveredGlobalClosure snapshotBoundEvidence :=
  snapshotBoundEvidence.gluesWithUniverseCoverageAtSnapshot

theorem fc1_coverage_lists_every_typed_component :
    ∀ component : FacetCoherence.Tests.Component,
      component ∈ Positive.World.components :=
  universeCoveredEvidence.universeCovered.everyComponentListed

theorem fc1_coverage_lists_every_typed_seam :
    ∀ seam : FacetCoherence.Tests.Seam,
      seam ∈ Positive.World.seams :=
  universeCoveredEvidence.universeCovered.everySeamListed

def rawIntegratedH2 :
    RawIntegratedCompositionEvidence
      (sealSpec := FacetCoherence.Tests.sealSpec)
      FacetCoherence.Tests.adapter where
  snapshot := FacetCoherence.Tests.snapshotH2
  carrier := FacetCoherence.Tests.carrierH2Value
  seamBinding := Positive.seamBinding
  integrated := Positive.evidence

/--
A composition payload produced at H2 cannot supply the composition facet of
the H1 bundle used by `snapshotBoundEvidence`.
-/
theorem mismatched_snapshot_composition_payload_refused :
    ¬ BoundIntegratedCompositionEvidence
      FacetCoherence.Tests.snapshotH1
      FacetCoherence.Tests.carrierH1
      rawIntegratedH2 := by
  intro bound
  exact
    FacetCoherence.Tests.snapshotH1_ne_snapshotH2
      bound.snapshotBound.symm

/-! ## C4-R2 mutant: self-declared lists can omit typed inhabitants -/

def omittedUniverseWorld : CoherenceWorld :=
  { FacetCoherence.Tests.world with
    components := [.left]
    seams := [] }

def omittedComponentBinding :
    CoherenceComponentBinding omittedUniverseWorld where
  sourceRel := fun _ =>
    ComponentClosurePreservation.Tests.source
  targetRel := fun _ =>
    ComponentClosurePreservation.Tests.source
  seam := fun _ =>
    ComponentClosurePreservation.Tests.identitySeam
  terminalSound := by
    intro component start finish trace
    cases component
    · exact .left
    · exact .right

def omittedComponentRealization
    (component : omittedUniverseWorld.Component) :
    ComponentClosureRealization omittedComponentBinding component where
  start := .zero
  finish := .one
  trace := ComponentClosurePreservation.Tests.sourceClosedTrace

def omittedComponentFamily :
    ClosedComponentFamily omittedComponentBinding where
  realization := by
    intro component listed
    exact omittedComponentRealization component

def omittedSeamBinding :
    CoherenceSeamBinding omittedUniverseWorld where
  seamWorld := fun _ =>
    SeamExactness.Tests.Identity.world
  exactSound := by
    intro seam exact
    cases seam
    exact .shared

def omittedSeamFamily :
    SealedIntegratedSeamFamily omittedSeamBinding.scope where
  sealed := omittedSeamBinding.sealed
  realization := by
    intro seam listed
    change seam ∈ [] at listed
    exact nomatch listed

def omittedLegacyEvidence :
    IntegratedCompositionEvidence
      omittedUniverseWorld omittedSeamBinding where
  componentBinding := omittedComponentBinding
  components := omittedComponentFamily
  seams := omittedSeamFamily

/--
Legacy self-declared families exist despite omitting `.right` and `.shared`,
but the FC-1 typed coverage law cannot exist for that world.
-/
theorem listed_family_with_omitted_typed_inhabitants_rejected_by_fc1_coverage :
    Nonempty
        (IntegratedCompositionEvidence
          omittedUniverseWorld omittedSeamBinding) ∧
      ¬ CompositionLaw omittedUniverseWorld := by
  refine ⟨⟨omittedLegacyEvidence⟩, ?_⟩
  intro law
  have rightListed :=
    law.componentCoverage FacetCoherence.Tests.Component.right
  change
    FacetCoherence.Tests.Component.right ∈
      [FacetCoherence.Tests.Component.left] at rightListed
  exact nomatch rightListed

theorem omitted_typed_seam_independently_rejected_by_fc1_coverage :
    ¬ CompositionLaw omittedUniverseWorld := by
  intro law
  have sharedListed :=
    law.seamCoverage FacetCoherence.Tests.Seam.shared
  change FacetCoherence.Tests.Seam.shared ∈ [] at sharedListed
  exact nomatch sharedListed

/-! ## C4-R1: the same local conclusions must remain replayable -/

inductive LocalReplayJudgment
  | componentLeft
  | componentRight
  | seamShared
  deriving DecidableEq

def localJudgmentBytes : LocalReplayJudgment → String
  | .componentLeft => "component-left"
  | .componentRight => "component-right"
  | .seamShared => "seam-shared"

def localJudgmentDigest : String → LocalReplayJudgment
  | "component-left" => .componentLeft
  | "component-right" => .componentRight
  | _ => .seamShared

def replaySystem :
    ReplaySystem
      FacetCoherence.Tests.snapshotH1 FacetCoherence.Tests.carrierH1 where
  Judgment := LocalReplayJudgment
  Receipt := LocalReplayJudgment
  Object := LocalReplayJudgment
  ObjectQ := LocalReplayJudgment
  mandatoryJudgments := [.componentLeft, .componentRight, .seamShared]
  LiveMandatoryAt := fun judgment =>
    judgment ∈ [.componentLeft, .componentRight, .seamShared]
  receiptFor := id
  receiptObjectQ := id
  lookup := some
  objectQ := id
  objectBytes := localJudgmentBytes
  digest := localJudgmentDigest
  decodeReceipt := some
  objectDependencies := fun _ => []
  objectRank := fun _ => 0
  receiptEpoch := fun _ => 7
  receiptHistoryHead := fun _ => .h1
  receiptAssumptionRoot := fun _ => 11
  receiptAddressRegistry := fun _ => 13
  receiptSourceWindow := fun _ => 1
  receiptFailureModel := fun _ => 17
  receiptProposalWindow := fun _ => 1
  receiptImplementationBundle := fun _ => 19
  verifyReplay := fun judgment receipt => judgment == receipt

def replayUniverseSeal : MandatoryJudgmentUniverseSeal replaySystem where
  nonempty := by simp [replaySystem]
  declaredSound := by
    intro judgment listed
    exact listed
  declaredComplete := by
    intro judgment live
    exact live

def localArchiveClosed
    (judgment : LocalReplayJudgment) :
    ArchiveObjectClosure replaySystem judgment :=
  ArchiveObjectClosure.checked (K := replaySystem)
    judgment judgment rfl rfl
    (by cases judgment <;> rfl)
    (by
      intro dependency member
      change dependency ∈ ([] : List LocalReplayJudgment) at member
      exact nomatch member)
    (by
      intro dependency member
      change dependency ∈ ([] : List LocalReplayJudgment) at member
      exact nomatch member)

def localReplayable
    (judgment : LocalReplayJudgment)
    (mandatory : replaySystem.LiveMandatoryAt judgment) :
    ReplayableJudgmentAt replaySystem judgment where
  mandatory := mandatory
  object := judgment
  found := rfl
  addressBound := rfl
  rehash := by cases judgment <;> rfl
  decoded := rfl
  epochBound := rfl
  historyHeadBound := rfl
  assumptionRootBound := rfl
  addressRegistryBound := rfl
  sourceWindowBound := rfl
  failureModelBound := rfl
  proposalWindowBound := rfl
  implementationBound := rfl
  archiveClosed := localArchiveClosed judgment
  replayAccepted := by cases judgment <;> rfl

def localReplayability : EvidenceReplayabilityAt replaySystem where
  universeSeal := replayUniverseSeal
  replayable := localReplayable

def replayAssociation :
    IntegratedCompositionReplayAssociation
      snapshotBoundEvidence replaySystem where
  componentJudgment
    | .left => .componentLeft
    | .right => .componentRight
  seamJudgment
    | .shared => .seamShared
  componentLiveMandatory := by
    intro component listed
    cases component <;> simp [replaySystem]
  seamLiveMandatory := by
    intro seam listed
    cases seam
    simp [replaySystem]

def replayGatedEvidence :
    ReplayGatedIntegratedCompositionEvidence
      snapshotBoundEvidence replaySystem where
  replayability := localReplayability
  association := replayAssociation

theorem integrated_evidence_glues_only_with_live_replay_gate :
    (FacetCoherence.Tests.adapter.index.world
      FacetCoherence.Tests.carrierH1.value).globalClosed :=
  replayGatedEvidence.gluesReplayableAtSnapshot.globalClosed

def ghostReplaySystem :
    ReplaySystem
      FacetCoherence.Tests.snapshotH1 FacetCoherence.Tests.carrierH1 :=
  { replaySystem with lookup := fun _ => none }

def ghostReplayAssociation :
    IntegratedCompositionReplayAssociation
      snapshotBoundEvidence ghostReplaySystem where
  componentJudgment
    | .left => .componentLeft
    | .right => .componentRight
  seamJudgment
    | .shared => .seamShared
  componentLiveMandatory := by
    intro component listed
    cases component <;> simp [ghostReplaySystem, replaySystem]
  seamLiveMandatory := by
    intro seam listed
    cases seam
    simp [ghostReplaySystem, replaySystem]

/--
Receipt identities without retained archive bytes cannot form the replay gate
required by the C4-R1 headline.
-/
theorem ghost_archive_cannot_gate_global_closure :
    (¬ Nonempty
      (ReplayGatedIntegratedCompositionEvidence
        snapshotBoundEvidence ghostReplaySystem)) ∧
    ¬ ∃ packet :
        ReplayGatedIntegratedCompositionEvidence
          snapshotBoundEvidence ghostReplaySystem,
      ReplayGatedGlobalClosure packet := by
  have noPacket :
      ¬ Nonempty
        (ReplayGatedIntegratedCompositionEvidence
          snapshotBoundEvidence ghostReplaySystem) := by
    intro ⟨packet⟩
    have replayable :=
      packet.componentReplayable
        FacetCoherence.Tests.Component.left
        (List.Mem.head _)
    cases replayable.found
  exact
    ⟨noPacket, by
      intro ⟨packet, gated⟩
      exact noPacket ⟨packet⟩⟩

/--
Even complete integrated local evidence cannot manufacture an arbitrary
false global intent contract.
-/
theorem local_evidence_does_not_manufacture_false_global_intent :
    ¬ CompositionIntentContract
      Positive.World
      Positive.World.componentClosed
      Positive.World.seamExact
      False := by
  intro contract
  exact
    contract.localClaimsSuffice
      Positive.evidence.components.componentsClosed
      Positive.evidence.toClosureEvidence.seamsExact

def falseSeamWorld : CoherenceWorld :=
  { FacetCoherence.Tests.world with
    seamExact := fun _ => False
    globalClosed := False }

/--
A supplied legacy seam predicate that is false cannot be manufactured from
an integrated family merely by packaging it in the C4 bridge.
-/
theorem integrated_evidence_cannot_realize_false_seam_predicate
    (binding : CoherenceSeamBinding falseSeamWorld) :
    IntegratedCompositionEvidence falseSeamWorld binding →
      False := by
  intro evidence
  exact
    evidence.toClosureEvidence.seamsExact
      FacetCoherence.Tests.Seam.shared
      (List.Mem.head [])

end Residua.RCC.CompositionGluing.Tests

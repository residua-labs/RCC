import RCCTests.CompositionGluing

/-! C4 candidate: integrated component and seam evidence at one FC-1
    snapshot glues to global closure only with exact universe coverage and
    replayability; mismatched snapshots and omitted typed inhabitants refuse. -/

namespace Residua.RCC.C4Target

open Residua.RCC.CompositionGluing.Tests
open Residua.RCC.CompositionGluing
open Residua.RCC.ComponentClosureFamily
open Residua.RCC.EvidenceReplayability
open Residua.RCC.FacetCoherence
open Residua.RCC.FacetSnapshot
open Residua.RCC.GlobalIntentCoverage
open Residua.RCC.SeamIntegratedFamily

structure Certificate where
  localEvidenceConstructsGlobalEvidence :
    Residua.RCC.GlobalIntentCoverage.CompositionClosureEvidence Positive.World
  integratedGlobalClosed :
    Positive.World.globalClosed
  snapshotBoundGlobalClosed :
    (Residua.RCC.FacetCoherence.Tests.adapter.index.world
      Residua.RCC.FacetCoherence.Tests.carrierH1.value).globalClosed
  everyComponentListed :
    ∀ component : Residua.RCC.FacetCoherence.Tests.Component,
      component ∈ Positive.World.components
  everySeamListed :
    ∀ seam : Residua.RCC.FacetCoherence.Tests.Seam,
      seam ∈ Positive.World.seams
  mismatchedSnapshotRejected :
    ¬ BoundIntegratedCompositionEvidence
      Residua.RCC.FacetCoherence.Tests.snapshotH1
      Residua.RCC.FacetCoherence.Tests.carrierH1
      rawIntegratedH2
  omittedComponentRejected :
    ¬ CompositionLaw omittedUniverseWorld

def certificate : Certificate where
  localEvidenceConstructsGlobalEvidence :=
    integrated_local_evidence_constructs_c3_evidence
  integratedGlobalClosed := integrated_components_and_seams_glue_global_closed
  snapshotBoundGlobalClosed := integrated_evidence_glues_at_fc1_snapshot
  everyComponentListed := fc1_coverage_lists_every_typed_component
  everySeamListed := fc1_coverage_lists_every_typed_seam
  mismatchedSnapshotRejected := mismatched_snapshot_composition_payload_refused
  omittedComponentRejected :=
    omitted_typed_seam_independently_rejected_by_fc1_coverage

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.C4Target

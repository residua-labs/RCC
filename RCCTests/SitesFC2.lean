import RCCTests.FacetCoherence

/-!
# Registration site for FC-2 (ResiduaRCCFacetCoherence + Tests)

The seven cross-facet bridge laws live in `ResiduaRCCFacetCoherence`; this site
re-cites them at the concrete `Tests` fixture (one sealed snapshot, one
carrier) and re-cites the three named refusals as the discriminating half.
Positive: all seven bridges are live at the fixture and the certified bundle
decodes every facet.  Refusals: a cross-snapshot pair cannot bind, a detached
payload cannot decode, and a reduction with a missing resource delta cannot be
certified.  The library theorems are untouched.
-/

open Residua.RCC.FacetSnapshot
open Residua.RCC.FacetCoherence
open Residua.RCC.FacetCoherence.Tests

namespace Residua.RCC.RegistrationSites.FC2

/-- Positive: all seven semantic bridges are live at the concrete fixture —
the certificate is not an empty structure. -/
theorem seven_bridges_live_at_fixture :
    (world.stateEquivalent .after .after) ∧
    (world.grounded .witness) ∧
    (∃ delta : ResourceDelta world.ResourceToken,
      world.activeResources .before =
          delta.consumed ++ delta.retained ∧
        world.activeResources .after =
          delta.produced ++ delta.retained) ∧
    (world.artifactLevel .rccSpec < world.verifierLevel .checker) ∧
    (world.terminalAt .before .oldGoal ∨
      ∃ successor,
        successor ∈ world.activeResources .after ∧
        world.carries .oldGoal successor) ∧
    (world.reduces
      (world.abstractState .runningBefore)
      (world.abstractState .runningAfter)) ∧
    world.globalClosed :=
  ⟨address_reduction_bridge_is_live,
   evidence_admission_bridge_is_live,
   reduction_resource_bridge_is_live,
   reflection_verification_bridge_is_live,
   migration_resource_bridge_is_live,
   runtime_refinement_bridge_is_live,
   composition_bridge_is_live⟩

/-- Discriminating refusal 1: a bridge assembled across two different sealed
snapshots cannot bind — the BoundFacetPairAt origin is load-bearing. -/
theorem cross_snapshot_bridge_refused_at_fixture :
    ∀ (snapshot : SealedSnapshot sealSpec)
      (carrier : SnapshotCarrier projection snapshot),
      ¬ BoundFacetPairAt
        snapshot carrier addressRawH1 reductionRawH2 :=
  cross_snapshot_address_reduction_bridge_refused

/-- Discriminating refusal 2: a facet payload detached from the FC-1 carrier
cannot decode as if it were bound there, and no certificate can ignore it. -/
theorem detached_payload_refused_at_fixture :
    (adapter.decodeAddress
      carrierH1Value
        (detachedPayloadBundle.evidence .addressKernel).raw.payload =
      none) ∧
    (FacetCoherenceCertificate detachedPayloadBundle adapter → False) :=
  ⟨detached_address_payload_decode_is_refused,
   ignored_payload_collage_cannot_certify⟩

/-- Discriminating refusal 3: a real reduction step with no resource delta is
refused as `resourceDeltaMissing`, and no certificate can be issued for it. -/
theorem missing_delta_refused_at_fixture :
    validateResourceBridge beforeAfterStep none =
        ResourceBridgeValidation.refused .resourceDeltaMissing ∧
      ∀ certificate :
        CertifiedReductionResource world .before .after,
        validateResourceBridge beforeAfterStep none ≠
          ResourceBridgeValidation.certified certificate :=
  ⟨missing_resource_delta_mutant_is_named,
   missing_resource_delta_mutant_cannot_certify⟩

#print axioms seven_bridges_live_at_fixture
#print axioms cross_snapshot_bridge_refused_at_fixture
#print axioms detached_payload_refused_at_fixture
#print axioms missing_delta_refused_at_fixture

end Residua.RCC.RegistrationSites.FC2

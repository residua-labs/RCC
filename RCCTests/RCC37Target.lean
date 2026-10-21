import RCC.RCC37Target

/-! Independent proof-level checks for the RCC-37 target certificate. -/

namespace Residua.RCC.RCC37Target.Tests

open Residua.RCC.TemporalValidity
open Residua.RCC.TrustTopologyInvalidation
open Residua.RCC.TrustTopologyInvalidation.Tests
open Residua.RCC.RCC37Target

theorem topology_delta_is_exact_and_fenced :
    (∀ slot, slot ∈ hostDelta.changedSlots ↔
      demoSystem.inScopeSlot oldSnapshot.context slot ∧
        demoSystem.valueAt oldSnapshot.context slot ≠
          demoSystem.valueAt successorSnapshot.context slot) ∧
      (∃ slot, slot ∈ hostDelta.changedSlots) ∧
      (∀ _delta : TopologyDelta demoSystem oldSnapshot staleParentSnapshot, False) :=
  ⟨Certificate.exactNonemptyDelta certificate |>.1,
    Certificate.exactNonemptyDelta certificate |>.2,
    Certificate.staleParentRejected certificate⟩

theorem invalidation_rejects_bad_transitions :
    (∀ {old new : SealedTopologySnapshot demoSystem},
      TopologyDelta demoSystem old new → new.epoch = old.epoch → False) ∧
      (∀ delta : TopologyDelta demoSystem oldSnapshot successorSnapshot,
        delta.authority = .rogue → False) ∧
      (∀ {old new : SealedTopologySnapshot demoSystem},
        TopologyDelta demoSystem old new →
        (∀ slot, demoSystem.valueAt old.context slot =
          demoSystem.valueAt new.context slot) → False) :=
  ⟨Certificate.sameEpochRejected certificate,
    Certificate.rogueAuthorityRejected certificate,
    Certificate.noOpRejected certificate⟩

theorem evidence_is_anchor_and_receipt_bound :
    successorEvidenceBundleAt successorAnchor ∧
      ¬ successorEvidenceBundleAt staleAssumptionAnchor ∧
      ¬ successorEvidenceBundleAt staleEpochAnchor ∧
      ¬ successorEvidenceBundleAt staleHeadAnchor ∧
      ¬ successorEvidenceBundleAt staleWindowAnchor ∧
      ¬ SemanticallyActiveAt demoSystem oldAnchor
        emptyHistoricalReceipt .rcc32 :=
  ⟨(Certificate.anchorEvidencePinned certificate).1,
    (Certificate.anchorEvidencePinned certificate).2.1,
    (Certificate.anchorEvidencePinned certificate).2.2.1,
    (Certificate.anchorEvidencePinned certificate).2.2.2.1,
    (Certificate.anchorEvidencePinned certificate).2.2.2.2,
    (Certificate.markerAndOldCertificateRejected certificate).1⟩

theorem transport_and_successor_state_are_explicit :
    SameClaim demoSystem .rcc35 .replacement ∧
      SemanticallyActiveAt demoSystem successorAnchor
        successorHistoricalReceipt .replacement ∧
      topologyPost.epoch = .successor ∧
      topologyPost.head = .successor ∧
      topologyPost.context = .successor :=
  ⟨(Certificate.transportBound certificate).2.1,
    (Certificate.transportBound certificate).2.2,
    (Certificate.successorStateBound certificate).1,
    (Certificate.successorStateBound certificate).2.1,
    (Certificate.successorStateBound certificate).2.2⟩

theorem no_stale_authority_or_kind_aliasing :
    (¬ FacetBoundAt demoSystem successorAnchor successorHistoricalReceipt
        .rcc32 .failureCoverage) ∧
      (¬ FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc32 .evidenceProfile) ∧
      demoSlot .host ≠ demoSlot .custody :=
  ⟨(Certificate.markerAndOldCertificateRejected certificate).2.1,
    (Certificate.markerAndOldCertificateRejected certificate).2.2,
    (Certificate.topologyKindIdentity certificate).1⟩

theorem affected_old_universe_is_not_usable :
    Affected oldSnapshot .rcc36 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc36 :=
  Certificate.activeUniverseInvalidated certificate

#print axioms topology_delta_is_exact_and_fenced
#print axioms invalidation_rejects_bad_transitions
#print axioms evidence_is_anchor_and_receipt_bound
#print axioms transport_and_successor_state_are_explicit
#print axioms no_stale_authority_or_kind_aliasing
#print axioms affected_old_universe_is_not_usable

end Residua.RCC.RCC37Target.Tests

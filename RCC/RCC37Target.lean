import RCCTests.TrustTopologyInvalidation

/-!
# RCC-37 target package

This target packages the concrete sealed trust-topology invalidation fixture
already present on `main`.  It covers the six typed topology kinds, exact
nonempty deltas, parent/epoch/authority fences, history preservation, full
anchor evidence binding, and successor transport/reopen behavior.

The target deliberately preserves RCC-37's scope boundary: it does not wire
the concrete RCC-32..36 artifacts into the generic facet adapter, and it does
not claim RCC-21 field-level dependency extraction completeness.  Those are
separate obligations, not hidden consequences of this finite instance.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC37Target

open Residua.RCC.TemporalValidity
open Residua.RCC.TrustTopologyInvalidation
open Residua.RCC.TrustTopologyInvalidation.Tests

structure Certificate : Prop where
  sixTopologyKinds :
    ∀ kind : TopologyTargetKind,
      kind = .custody ∨ kind = .host ∨ kind = .operator ∨
        kind = .generator ∨ kind = .keyLineage ∨ kind = .modelLineage
  exactNonemptyDelta :
    (∀ slot, slot ∈ hostDelta.changedSlots ↔
      demoSystem.inScopeSlot oldSnapshot.context slot ∧
        demoSystem.valueAt oldSnapshot.context slot ≠
          demoSystem.valueAt successorSnapshot.context slot) ∧
    ∃ slot, slot ∈ hostDelta.changedSlots
  staleParentRejected :
    ∀ _delta : TopologyDelta demoSystem oldSnapshot staleParentSnapshot, False
  sameEpochRejected :
    ∀ {old new : SealedTopologySnapshot demoSystem},
      TopologyDelta demoSystem old new → new.epoch = old.epoch → False
  rogueAuthorityRejected :
    ∀ delta : TopologyDelta demoSystem oldSnapshot successorSnapshot,
      delta.authority = .rogue → False
  noOpRejected :
    ∀ {old new : SealedTopologySnapshot demoSystem},
      TopologyDelta demoSystem old new →
      (∀ slot, demoSystem.valueAt old.context slot =
        demoSystem.valueAt new.context slot) → False
  outOfScopeRejected :
    ∀ {old new : SealedTopologySnapshot demoSystem},
      (delta : TopologyDelta demoSystem old new) →
      ∀ slot, slot ∈ delta.changedSlots →
        ¬ demoSystem.inScopeSlot old.context slot → False
  historyPreserved :
    topologyPost.historicalReceipt .rcc32 .current = some .rcc32
  anchorEvidencePinned :
    successorEvidenceBundleAt successorAnchor ∧
      ¬ successorEvidenceBundleAt staleAssumptionAnchor ∧
      ¬ successorEvidenceBundleAt staleEpochAnchor ∧
      ¬ successorEvidenceBundleAt staleHeadAnchor ∧
      ¬ successorEvidenceBundleAt staleWindowAnchor
  markerAndOldCertificateRejected :
    ¬ SemanticallyActiveAt demoSystem oldAnchor
        emptyHistoricalReceipt .rcc32 ∧
      ¬ FacetBoundAt demoSystem successorAnchor successorHistoricalReceipt
        .rcc32 .failureCoverage ∧
      ¬ FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc32 .evidenceProfile
  transportBound :
    topologyPost.currentState .rcc35 = .transported .replacement ∧
      SameClaim demoSystem .rcc35 .replacement ∧
      SemanticallyActiveAt demoSystem successorAnchor
        successorHistoricalReceipt .replacement
  activeUniverseInvalidated :
    Affected oldSnapshot .rcc36 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc36
  topologyKindIdentity :
    demoSlot .host ≠ demoSlot .custody ∧
      ∀ left right : TopologySlot DemoSlotQ,
        left = right → left.kind = right.kind
  successorStateBound :
    topologyPost.epoch = .successor ∧
      topologyPost.head = .successor ∧
      topologyPost.context = .successor

def certificate : Certificate where
  sixTopologyKinds := topology_kind_exactly_six
  exactNonemptyDelta := ⟨host_delta_is_exact, host_delta_is_nonempty⟩
  staleParentRejected := stale_parent_snapshot_cannot_form_delta
  sameEpochRejected := same_epoch_delta_is_rejected
  rogueAuthorityRejected := rogue_authority_is_rejected
  noOpRejected := no_op_snapshot_cannot_form_delta
  outOfScopeRejected := out_of_scope_delta_member_is_rejected
  historyPreserved := admitted_history_is_not_rewritten
  anchorEvidencePinned :=
    ⟨exact_successor_anchor_accepts_evidence_bundle,
      stale_assumption_root_rejects_evidence_bundle,
      stale_epoch_rejects_evidence_bundle,
      stale_head_rejects_evidence_bundle,
      stale_window_rejects_evidence_bundle⟩
  markerAndOldCertificateRejected :=
    ⟨marker_only_without_receipt_is_rejected,
      old_certificate_reuse_at_successor_is_rejected,
      wrong_facet_alias_is_rejected⟩
  transportBound :=
    ⟨rcc35_transport_state_is_exact,
      rcc35_transport_is_bound_to_successor.1,
      rcc35_transport_is_bound_to_successor.2⟩
  activeUniverseInvalidated :=
    ⟨old_active_rcc36_is_affected, old_active_rcc36_is_not_usable⟩
  topologyKindIdentity :=
    ⟨same_q_different_topology_kind_is_not_same_slot,
      topology_slot_equality_preserves_kind⟩
  successorStateBound := post_state_is_bound_to_successor

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC37Target

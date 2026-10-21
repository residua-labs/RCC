import RCCTests.TrustTopologyInvalidation

/-! RCC-67 candidate: trust-topology successor invalidation boundaries. -/

namespace Residua.RCC.RCC67Target

open Residua.RCC.TrustTopologyInvalidation.Tests
open Residua.RCC.TrustTopologyInvalidation

def oldAnchorAdmitted := old_anchor_admitted
def successorAnchorAdmitted := successor_anchor_admitted
def allKindsCovered := demo_all_kinds_covered
def topologyDeltaExact := host_delta_is_exact
def allOldFacetsLoseAuthority := all_five_facets_lose_old_current_authority
def staleParentRefused := stale_parent_snapshot_cannot_form_delta
theorem sameEpochRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot),
      successorSnapshot.epoch = oldSnapshot.epoch → False := by
  intro delta sameEpoch
  exact same_epoch_delta_is_rejected delta sameEpoch
def rogueAuthorityRefused := rogue_authority_is_rejected
theorem noOpRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot),
      (∀ slot,
        demoSystem.valueAt oldSnapshot.context slot =
          demoSystem.valueAt successorSnapshot.context slot) → False := by
  intro delta sameValues
  exact no_op_snapshot_cannot_form_delta delta sameValues
def externalSlotRefused := changed_external_slot_cannot_enter_lawful_delta
def historyRewriteRefused := history_rewrite_function_is_not_successor_history
def historicalReceiptPreserved := admitted_history_is_not_rewritten
def exactSuccessorAccepted := exact_successor_anchor_accepts_evidence_bundle
def staleRootRefused := stale_assumption_root_rejects_evidence_bundle
def staleEpochRefused := stale_epoch_rejects_evidence_bundle
def staleHeadRefused := stale_head_rejects_evidence_bundle
def staleWindowRefused := stale_window_rejects_evidence_bundle
def markerWithoutReceiptRefused := marker_only_without_receipt_is_rejected
def oldCertificateRefused := old_certificate_reuse_at_successor_is_rejected
def successorTransportBound := rcc35_transport_is_bound_to_successor
def postStateSuccessorBound := post_state_is_bound_to_successor

structure Certificate where
  oldAnchorAdmitted : demoAnchorClass oldAnchor ≠ none
  successorAnchorAdmitted : demoAnchorClass successorAnchor ≠ none
  allKindsCovered :
    ∀ (anchor :
      TopologyAnchor DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
      (anchorAdmitted : demoAnchorClass anchor ≠ none)
      (kind : TopologyTargetKind),
      ∃ observation,
        observation ∈ demoObservations anchor anchorAdmitted ∧
          observation.slot.kind = kind
  topologyDeltaExact :
    ∀ (slot : TopologySlot DemoSlotQ),
      slot ∈ hostDelta.changedSlots ↔
        demoSystem.inScopeSlot oldSnapshot.context slot ∧
          demoSystem.valueAt oldSnapshot.context slot ≠
            demoSystem.valueAt successorSnapshot.context slot
  allOldFacetsLoseAuthority :
    ¬ CurrentlyUsable demoSystem topologyPost .rcc32 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc33 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc34 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc35 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc36
  staleParentRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot staleParentSnapshot), False
  sameEpochRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot),
      successorSnapshot.epoch = oldSnapshot.epoch → False
  rogueAuthorityRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot),
      delta.authority = .rogue → False
  noOpRefused :
    ∀ {old new : SealedTopologySnapshot demoSystem},
      (delta : TopologyDelta demoSystem old new) →
      (∀ slot, demoSystem.valueAt old.context slot =
        demoSystem.valueAt new.context slot) → False
  externalSlotRefused :
    ∀ (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot),
      externalSlot ∈ delta.changedSlots → False
  historyRewriteRefused : successorSnapshot.historicalReceipt ≠ rewrittenHistoricalReceipt
  historicalReceiptPreserved :
    topologyPost.historicalReceipt .rcc32 .current = some .rcc32
  exactSuccessorAccepted : successorEvidenceBundleAt successorAnchor
  staleRootRefused : ¬ successorEvidenceBundleAt staleAssumptionAnchor
  staleEpochRefused : ¬ successorEvidenceBundleAt staleEpochAnchor
  staleHeadRefused : ¬ successorEvidenceBundleAt staleHeadAnchor
  staleWindowRefused : ¬ successorEvidenceBundleAt staleWindowAnchor
  markerWithoutReceiptRefused :
    ¬ SemanticallyActiveAt demoSystem oldAnchor emptyHistoricalReceipt .rcc32
  oldCertificateRefused :
    ¬ FacetBoundAt demoSystem successorAnchor successorHistoricalReceipt
        .rcc32 .failureCoverage
  successorTransportBound :
    SameClaim demoSystem .rcc35 .replacement ∧
      SemanticallyActiveAt demoSystem successorAnchor
        successorHistoricalReceipt .replacement
  postStateSuccessorBound :
    topologyPost.epoch = .successor ∧
      topologyPost.head = .successor ∧
      topologyPost.context = .successor

def certificate : Certificate where
  oldAnchorAdmitted := oldAnchorAdmitted
  successorAnchorAdmitted := successorAnchorAdmitted
  allKindsCovered := demo_all_kinds_covered
  topologyDeltaExact := host_delta_is_exact
  allOldFacetsLoseAuthority := all_five_facets_lose_old_current_authority
  staleParentRefused := fun delta => stale_parent_snapshot_cannot_form_delta delta
  sameEpochRefused := same_epoch_delta_is_rejected
  rogueAuthorityRefused := rogue_authority_is_rejected
  noOpRefused := no_op_snapshot_cannot_form_delta
  externalSlotRefused := changed_external_slot_cannot_enter_lawful_delta
  historyRewriteRefused := history_rewrite_function_is_not_successor_history
  historicalReceiptPreserved := admitted_history_is_not_rewritten
  exactSuccessorAccepted := exact_successor_anchor_accepts_evidence_bundle
  staleRootRefused := stale_assumption_root_rejects_evidence_bundle
  staleEpochRefused := stale_epoch_rejects_evidence_bundle
  staleHeadRefused := stale_head_rejects_evidence_bundle
  staleWindowRefused := stale_window_rejects_evidence_bundle
  markerWithoutReceiptRefused := marker_only_without_receipt_is_rejected
  oldCertificateRefused := old_certificate_reuse_at_successor_is_rejected
  successorTransportBound := rcc35_transport_is_bound_to_successor
  postStateSuccessorBound := post_state_is_bound_to_successor

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC67Target

import RCC.TrustTopologyInvalidation

/-!
# RCC-37 Sealed Trust-Topology Invalidation Witnesses

This finite instance pins all six topology kinds and all five RCC certificate
facets.  The old and successor snapshots are exact sealed universes.  A single
host-slot change invalidates the whole old topology-bound active universe,
preserves immutable receipts, and permits transport only to a same-claim
judgment carrying replayable successor evidence.

The countermodels reject stale-parent admission, a no-op masquerading as a
change, history rewriting, marker-only usability, old-certificate reuse, and
topology-kind aliasing.  A judgment whose dependency is discovered only after
the change is still invalidated because RCC-37 derives its affected universe
from the exact old active set rather than a caller-supplied dependency table.

Prelude-only Lean 4.14; no Mathlib, no proof holes, and no custom axioms.
-/

namespace Residua.RCC.TrustTopologyInvalidation.Tests

open Residua.RCC.TemporalValidity
open Residua.RCC.TrustTopologyInvalidation

inductive DemoContext
  | old
  | successor
  deriving DecidableEq, Repr

inductive DemoEpoch
  | old
  | successor
  deriving DecidableEq, Repr

inductive DemoHead
  | genesis
  | old
  | successor
  | stale
  deriving DecidableEq, Repr

inductive DemoWindow
  | current
  | stale
  deriving DecidableEq, Repr

inductive DemoAssumptionRoot
  | old
  | successor
  deriving DecidableEq, Repr

inductive DemoJudgment
  | rcc32
  | rcc33
  | rcc34
  | rcc35
  | rcc36
  | replacement
  | inactive
  deriving DecidableEq, Repr

inductive DemoClaimQ
  | rcc32
  | rcc33
  | rcc34
  | rcc35
  | rcc36
  | inactive
  deriving DecidableEq, Repr

inductive DemoReceipt
  | rcc32
  | rcc33
  | rcc34
  | rcc35
  | rcc36
  | replacement
  deriving DecidableEq, Repr

inductive DemoAuthority
  | governance
  | rogue
  deriving DecidableEq, Repr

inductive DemoValueQ
  | old
  | successor
  deriving DecidableEq, Repr

inductive DemoSlotQ
  | tracked
  | external
  deriving DecidableEq, Repr

abbrev DemoObservationQ := TopologyTargetKind
abbrev DemoAttestationQ := Unit
abbrev DemoCertificate (_facet : TopologyFacet) := Unit

def demoSlot (kind : TopologyTargetKind) : TopologySlot DemoSlotQ :=
  ⟨.tracked, kind⟩

def externalSlot : TopologySlot DemoSlotQ :=
  ⟨.external, .host⟩

def demoInScopeSlot
    (_context : DemoContext) (slot : TopologySlot DemoSlotQ) : Prop :=
  slot.q = .tracked

def demoValueAt
    (context : DemoContext) (slot : TopologySlot DemoSlotQ) : DemoValueQ :=
  match context, slot.kind with
  | .successor, _ =>
      match slot.q, slot.kind with
      | .external, _ => .successor
      | .tracked, .host => .successor
      | _, _ => .old
  | _, _ => .old

inductive DemoAnchorClass
  | old
  | successor
  deriving DecidableEq, Repr

def demoAnchorClass
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot) :
    Option DemoAnchorClass :=
  match anchor.context, anchor.epoch, anchor.head,
      anchor.window, anchor.assumptionRoot with
  | .old, .old, .old, .current, .old => some .old
  | .successor, .successor, .successor, .current, .successor =>
      some .successor
  | _, _, _, _, _ => none

def demoObservationAdmittedAt
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (observationQ : DemoObservationQ)
    (_attestationQ : DemoAttestationQ)
    (slot : TopologySlot DemoSlotQ)
    (value : DemoValueQ) : Prop :=
  demoAnchorClass anchor ≠ none ∧
    observationQ = slot.kind ∧ value = demoValueAt anchor.context slot

def oldActiveJudgments : List DemoJudgment :=
  [.rcc32, .rcc33, .rcc34, .rcc35, .rcc36]

def demoCertificateAcceptedAt
    (facet : TopologyFacet)
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (judgment : DemoJudgment)
    (_certificate : DemoCertificate facet) : Prop :=
  match demoAnchorClass anchor, judgment, facet with
  | some .old, .rcc32, .failureCoverage => True
  | some .old, .rcc33, .commonCauseIndependence => True
  | some .old, .rcc34, .effectiveAuthorityQuorum => True
  | some .old, .rcc35, .evidenceProfile => True
  | some .old, .rcc36, .canonicalContribution => True
  | some .successor, .replacement, .evidenceProfile => True
  | _, _, _ => False

def oldHistoricalReceipt :
    DemoJudgment → DemoWindow → Option DemoReceipt
  | .rcc32, .current => some .rcc32
  | .rcc33, .current => some .rcc33
  | .rcc34, .current => some .rcc34
  | .rcc35, .current => some .rcc35
  | .rcc36, .current => some .rcc36
  | _, _ => none

def successorHistoricalReceipt :
    DemoJudgment → DemoWindow → Option DemoReceipt
  | .rcc32, .current => some .rcc32
  | .rcc33, .current => some .rcc33
  | .rcc34, .current => some .rcc34
  | .rcc35, .current => some .rcc35
  | .rcc36, .current => some .rcc36
  | .replacement, .current => some .replacement
  | _, _ => none

def demoReceiptAt
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot) :
    DemoJudgment → DemoWindow → Option DemoReceipt :=
  match demoAnchorClass anchor with
  | some .old => oldHistoricalReceipt
  | some .successor => successorHistoricalReceipt
  | none => fun _ _ => none

def demoReplayableAt
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (judgment : DemoJudgment)
    (receipt : DemoReceipt) : Prop :=
  match demoAnchorClass anchor, judgment, receipt with
  | some .old, .rcc32, .rcc32 => True
  | some .old, .rcc33, .rcc33 => True
  | some .old, .rcc34, .rcc34 => True
  | some .old, .rcc35, .rcc35 => True
  | some .old, .rcc36, .rcc36 => True
  | some .successor, .replacement, .replacement => True
  | _, _, _ => False

def demoReceiptSupports
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (judgment : DemoJudgment)
    (receipt : DemoReceipt)
    (_facet : TopologyFacet)
    (_certificate : DemoCertificate _facet) : Prop :=
  demoReplayableAt anchor judgment receipt

def demoClaimOf : DemoJudgment → DemoClaimQ
  | .rcc32 => .rcc32
  | .rcc33 => .rcc33
  | .rcc34 => .rcc34
  | .rcc35 => .rcc35
  | .rcc36 => .rcc36
  | .replacement => .rcc35
  | .inactive => .inactive

def demoAuthorizedChange
    (authority : DemoAuthority)
    (source successor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot) : Prop :=
  authority = .governance ∧
    source.context = .old ∧ successor.context = .successor ∧
    source.epoch = .old ∧ successor.epoch = .successor ∧
    source.head = .old ∧ successor.head = .successor ∧
    source.window = .current ∧ successor.window = .current ∧
    source.assumptionRoot = .old ∧
      successor.assumptionRoot = .successor

def demoSuccessorEpoch (sourceEpoch nextEpoch : DemoEpoch) : Prop :=
  sourceEpoch = .old ∧ nextEpoch = .successor

def demoSystem : TrustTopologySystem where
  SlotQ := DemoSlotQ
  ValueQ := DemoValueQ
  ObservationQ := DemoObservationQ
  AttestationQ := DemoAttestationQ
  Context := DemoContext
  Epoch := DemoEpoch
  Head := DemoHead
  Window := DemoWindow
  AssumptionRoot := DemoAssumptionRoot
  Judgment := DemoJudgment
  ClaimQ := DemoClaimQ
  Receipt := DemoReceipt
  Authority := DemoAuthority
  Certificate := DemoCertificate
  slotDecidableEq := inferInstance
  judgmentDecidableEq := inferInstance
  inScopeSlot := demoInScopeSlot
  inScopeSlotDecidable := fun _ slot => by
    unfold demoInScopeSlot
    infer_instance
  valueAt := demoValueAt
  observationAdmittedAt := demoObservationAdmittedAt
  certificateAcceptedAt := demoCertificateAcceptedAt
  replayableAt := demoReplayableAt
  receiptAt := demoReceiptAt
  receiptSupports := demoReceiptSupports
  claimOf := demoClaimOf
  authorizedChange := demoAuthorizedChange
  successorEpoch := demoSuccessorEpoch
  successorEpochStrict := by
    intro sourceEpoch nextEpoch advance equal
    rcases advance with ⟨rfl, rfl⟩
    simp at equal

def oldAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot where
  context := .old
  epoch := .old
  head := .old
  window := .current
  assumptionRoot := .old

def successorAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot where
  context := .successor
  epoch := .successor
  head := .successor
  window := .current
  assumptionRoot := .successor

theorem old_anchor_admitted : demoAnchorClass oldAnchor ≠ none := by
  simp [demoAnchorClass, oldAnchor]

theorem successor_anchor_admitted :
    demoAnchorClass successorAnchor ≠ none := by
  simp [demoAnchorClass, successorAnchor]

theorem demo_rcc32_accepted_facet_exact
    (facet : TopologyFacet)
    (certificate : DemoCertificate facet)
    (accepted :
      demoCertificateAcceptedAt facet oldAnchor .rcc32 certificate) :
    facet = .failureCoverage := by
  cases facet <;>
    simp [demoCertificateAcceptedAt, oldAnchor] at accepted ⊢

def demoObservation
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none)
    (kind : TopologyTargetKind) :
    TopologyObservation demoSystem anchor where
  slot := demoSlot kind
  value := demoValueAt anchor.context (demoSlot kind)
  observationQ := kind
  attestationQ := ()
  admitted := ⟨anchorAdmitted, rfl, rfl⟩
  valueExact := rfl

def demoObservations
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none) :
    List (TopologyObservation demoSystem anchor) :=
  [demoObservation anchor anchorAdmitted .custody,
    demoObservation anchor anchorAdmitted .host,
    demoObservation anchor anchorAdmitted .operator,
    demoObservation anchor anchorAdmitted .generator,
    demoObservation anchor anchorAdmitted .keyLineage,
    demoObservation anchor anchorAdmitted .modelLineage]

theorem demo_observation_slots_nodup
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none) :
    List.Nodup
      ((demoObservations anchor anchorAdmitted).map
        fun observation => observation.slot) := by
  letI : DecidableEq (TopologySlot DemoSlotQ) :=
    demoSystem.slotDecidableEq
  simpa [demoObservations, demoObservation] using
    (by decide :
      List.Nodup
        [demoSlot .custody, demoSlot .host, demoSlot .operator,
          demoSlot .generator, demoSlot .keyLineage, demoSlot .modelLineage])

theorem demo_observation_sound
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none)
    (observation : TopologyObservation demoSystem anchor)
    (_member : observation ∈ demoObservations anchor anchorAdmitted) :
    demoSystem.inScopeSlot anchor.context observation.slot := by
  simp [demoObservations] at _member
  rcases _member with member | member | member | member | member | member <;>
    subst observation <;>
    rfl

theorem demo_observation_complete
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none)
    (slot : TopologySlot DemoSlotQ)
    (_scoped : demoSystem.inScopeSlot anchor.context slot) :
    ∃ observation,
      observation ∈ demoObservations anchor anchorAdmitted ∧
        observation.slot = slot := by
  rcases slot with ⟨q, kind⟩
  cases q with
  | external =>
      simp [demoSystem, demoInScopeSlot] at _scoped
  | tracked =>
      cases kind with
      | custody =>
          exact ⟨demoObservation anchor anchorAdmitted .custody,
            by simp [demoObservations, demoObservation, demoSlot]⟩
      | host =>
          exact ⟨demoObservation anchor anchorAdmitted .host,
            by simp [demoObservations, demoObservation, demoSlot]⟩
      | operator =>
          exact ⟨demoObservation anchor anchorAdmitted .operator,
            by simp [demoObservations, demoObservation, demoSlot]⟩
      | generator =>
          exact ⟨demoObservation anchor anchorAdmitted .generator,
            by simp [demoObservations, demoObservation, demoSlot]⟩
      | keyLineage =>
          exact ⟨demoObservation anchor anchorAdmitted .keyLineage,
            by simp [demoObservations, demoObservation, demoSlot]⟩
      | modelLineage =>
          exact ⟨demoObservation anchor anchorAdmitted .modelLineage,
            by simp [demoObservations, demoObservation, demoSlot]⟩

theorem demo_all_kinds_covered
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot)
    (anchorAdmitted : demoAnchorClass anchor ≠ none)
    (kind : TopologyTargetKind) :
    ∃ observation,
      observation ∈ demoObservations anchor anchorAdmitted ∧
        observation.slot.kind = kind := by
  cases kind with
  | custody =>
      exact ⟨demoObservation anchor anchorAdmitted .custody,
        by simp [demoObservations, demoObservation, demoSlot]⟩
  | host =>
      exact ⟨demoObservation anchor anchorAdmitted .host,
        by simp [demoObservations, demoObservation, demoSlot]⟩
  | operator =>
      exact ⟨demoObservation anchor anchorAdmitted .operator,
        by simp [demoObservations, demoObservation, demoSlot]⟩
  | generator =>
      exact ⟨demoObservation anchor anchorAdmitted .generator,
        by simp [demoObservations, demoObservation, demoSlot]⟩
  | keyLineage =>
      exact ⟨demoObservation anchor anchorAdmitted .keyLineage,
        by simp [demoObservations, demoObservation, demoSlot]⟩
  | modelLineage =>
      exact ⟨demoObservation anchor anchorAdmitted .modelLineage,
        by simp [demoObservations, demoObservation, demoSlot]⟩

def oldActiveWitness (judgment : DemoJudgment)
    (member : judgment ∈ oldActiveJudgments) :
    ActiveWitness demoSystem oldAnchor oldHistoricalReceipt judgment := by
  cases judgment with
  | rcc32 =>
      exact
        { facet := .failureCoverage
          receipt := .rcc32
          certificate := ()
          lookup := rfl
          replayable := trivial
          accepted := trivial
          supports := trivial }
  | rcc33 =>
      exact
        { facet := .commonCauseIndependence
          receipt := .rcc33
          certificate := ()
          lookup := rfl
          replayable := trivial
          accepted := trivial
          supports := trivial }
  | rcc34 =>
      exact
        { facet := .effectiveAuthorityQuorum
          receipt := .rcc34
          certificate := ()
          lookup := rfl
          replayable := trivial
          accepted := trivial
          supports := trivial }
  | rcc35 =>
      exact
        { facet := .evidenceProfile
          receipt := .rcc35
          certificate := ()
          lookup := rfl
          replayable := trivial
          accepted := trivial
          supports := trivial }
  | rcc36 =>
      exact
        { facet := .canonicalContribution
          receipt := .rcc36
          certificate := ()
          lookup := rfl
          replayable := trivial
          accepted := trivial
          supports := trivial }
  | replacement =>
      simp [oldActiveJudgments] at member
  | inactive =>
      simp [oldActiveJudgments] at member

theorem old_active_sound
    (judgment : DemoJudgment)
    (member : judgment ∈ oldActiveJudgments) :
    SemanticallyActiveAt demoSystem oldAnchor
      oldHistoricalReceipt judgment := by
  exact ⟨oldActiveWitness judgment member⟩

theorem old_active_complete
    (judgment : DemoJudgment)
    (active :
      SemanticallyActiveAt demoSystem oldAnchor
        oldHistoricalReceipt judgment) :
    judgment ∈ oldActiveJudgments := by
  obtain ⟨witness⟩ := active
  have accepted := witness.accepted
  cases judgment <;> cases witness.facet <;>
    simp [demoSystem, demoCertificateAcceptedAt, demoAnchorClass,
      oldAnchor, oldActiveJudgments] at accepted ⊢

def replacementActiveWitness :
    ActiveWitness demoSystem successorAnchor
      successorHistoricalReceipt .replacement where
  facet := .evidenceProfile
  receipt := .replacement
  certificate := ()
  lookup := rfl
  replayable := trivial
  accepted := trivial
  supports := trivial

theorem replacement_active :
    SemanticallyActiveAt demoSystem successorAnchor
      successorHistoricalReceipt .replacement := by
  exact ⟨replacementActiveWitness⟩

theorem successor_active_complete
    (judgment : DemoJudgment)
    (active :
      SemanticallyActiveAt demoSystem successorAnchor
        successorHistoricalReceipt judgment) :
    judgment ∈ [.replacement] := by
  obtain ⟨witness⟩ := active
  have accepted := witness.accepted
  cases judgment <;> cases witness.facet <;>
    simp [demoSystem, demoCertificateAcceptedAt, demoAnchorClass,
      successorAnchor] at accepted ⊢

def oldSnapshot : SealedTopologySnapshot demoSystem where
  anchor := oldAnchor
  parentHead := .genesis
  observations := demoObservations oldAnchor old_anchor_admitted
  observationSlotsNodup :=
    demo_observation_slots_nodup oldAnchor old_anchor_admitted
  observationSound :=
    demo_observation_sound oldAnchor old_anchor_admitted
  observationComplete :=
    demo_observation_complete oldAnchor old_anchor_admitted
  allKindsCovered :=
    demo_all_kinds_covered oldAnchor old_anchor_admitted
  activeJudgments := oldActiveJudgments
  activeJudgmentsNodup := by
    letI : DecidableEq DemoJudgment :=
      demoSystem.judgmentDecidableEq
    change List.Nodup
      ([DemoJudgment.rcc32, DemoJudgment.rcc33, DemoJudgment.rcc34,
        DemoJudgment.rcc35, DemoJudgment.rcc36] : List DemoJudgment)
    exact of_decide_eq_true rfl
  activeSound := old_active_sound
  activeComplete := old_active_complete

def successorSnapshot : SealedTopologySnapshot demoSystem where
  anchor := successorAnchor
  parentHead := .old
  observations := demoObservations successorAnchor successor_anchor_admitted
  observationSlotsNodup :=
    demo_observation_slots_nodup successorAnchor successor_anchor_admitted
  observationSound :=
    demo_observation_sound successorAnchor successor_anchor_admitted
  observationComplete :=
    demo_observation_complete successorAnchor successor_anchor_admitted
  allKindsCovered :=
    demo_all_kinds_covered successorAnchor successor_anchor_admitted
  activeJudgments := [.replacement]
  activeJudgmentsNodup := by simp
  activeSound := by
    intro judgment member
    simp at member
    subst judgment
    exact replacement_active
  activeComplete := successor_active_complete

def hostDelta : TopologyDelta demoSystem oldSnapshot successorSnapshot where
  changedSlots := [demoSlot .host]
  changedSlotsNodup := by simp
  scopeExact := by
    intro slot
    simp [demoSystem, demoInScopeSlot]
  changedSound := by
    intro slot member
    simp at member
    subst slot
    exact ⟨by
      simp [demoSystem, demoInScopeSlot, demoSlot],
      by
      simp [demoSystem, SealedTopologySnapshot.context,
        oldSnapshot, successorSnapshot, oldAnchor, successorAnchor,
        demoValueAt, demoSlot]⟩
  changedComplete := by
    intro slot _scoped changed
    rcases slot with ⟨q, kind⟩
    cases q with
    | external =>
        simp [demoSystem, demoInScopeSlot] at _scoped
    | tracked =>
        cases kind with
        | host =>
            exact List.Mem.head _
        | custody => exact False.elim (changed rfl)
        | operator => exact False.elim (changed rfl)
        | generator => exact False.elim (changed rfl)
        | keyLineage => exact False.elim (changed rfl)
        | modelLineage => exact False.elim (changed rfl)
  nonempty := by simp
  authority := .governance
  authorized :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  epochAdvance := by
    simp [demoSystem, demoSuccessorEpoch,
      SealedTopologySnapshot.epoch, oldSnapshot, successorSnapshot,
      oldAnchor, successorAnchor]
  expectedParent := rfl
  headChanged := by
    simp [SealedTopologySnapshot.head,
      oldSnapshot, successorSnapshot, oldAnchor, successorAnchor]
  historyExtends := by
    intro judgment window receipt oldLookup
    cases judgment <;> cases window <;> cases receipt <;>
      simp [demoSystem, demoReceiptAt, demoAnchorClass,
        oldSnapshot, successorSnapshot,
        oldAnchor, successorAnchor,
        oldHistoricalReceipt, successorHistoricalReceipt] at oldLookup ⊢

def topologyPlan :
    TopologyResolutionPlan demoSystem oldSnapshot successorSnapshot hostDelta where
  resolve := by
    intro judgment affected
    change judgment ∈ oldActiveJudgments at affected
    cases judgment with
    | rcc32 => exact .revalidate
    | rcc33 => exact .reopen
    | rcc34 => exact .revalidate
    | rcc35 =>
        exact .transport .replacement rfl replacement_active
    | rcc36 => exact .reopen
    | replacement =>
        have notMember :
            ¬ DemoJudgment.replacement ∈
              ([DemoJudgment.rcc32, DemoJudgment.rcc33, DemoJudgment.rcc34,
                DemoJudgment.rcc35, DemoJudgment.rcc36] :
                List DemoJudgment) := by
          letI : DecidableEq DemoJudgment :=
            demoSystem.judgmentDecidableEq
          exact of_decide_eq_true rfl
        exact False.elim (notMember affected)
    | inactive =>
        have notMember :
            ¬ DemoJudgment.inactive ∈
              ([DemoJudgment.rcc32, DemoJudgment.rcc33, DemoJudgment.rcc34,
                DemoJudgment.rcc35, DemoJudgment.rcc36] :
                List DemoJudgment) := by
          letI : DecidableEq DemoJudgment :=
            demoSystem.judgmentDecidableEq
          exact of_decide_eq_true rfl
        exact False.elim (notMember affected)

def topologyPost : TopologyPostSnapshot demoSystem :=
  applyTopologyChange
    demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan

/-! Exact sealed topology and delta witnesses. -/

theorem topology_kind_exactly_six (kind : TopologyTargetKind) :
    kind = .custody ∨
      kind = .host ∨
      kind = .operator ∨
      kind = .generator ∨
      kind = .keyLineage ∨
      kind = .modelLineage := by
  cases kind <;> simp

theorem host_delta_is_exact (slot : TopologySlot DemoSlotQ) :
    slot ∈ hostDelta.changedSlots ↔
      demoSystem.inScopeSlot oldSnapshot.context slot ∧
        demoSystem.valueAt oldSnapshot.context slot ≠
          demoSystem.valueAt successorSnapshot.context slot :=
  topology_delta_exact hostDelta slot

theorem host_delta_is_nonempty :
    ∃ slot, slot ∈ hostDelta.changedSlots :=
  topology_delta_has_changed_slot hostDelta

theorem all_five_facets_are_bound :
    FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc32 .failureCoverage ∧
      FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc33 .commonCauseIndependence ∧
      FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc34 .effectiveAuthorityQuorum ∧
      FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc35 .evidenceProfile ∧
      FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
        .rcc36 .canonicalContribution := by
  exact
    ⟨⟨oldActiveWitness .rcc32 (by simp [oldActiveJudgments]), rfl⟩,
      ⟨oldActiveWitness .rcc33 (by simp [oldActiveJudgments]), rfl⟩,
      ⟨oldActiveWitness .rcc34 (by simp [oldActiveJudgments]), rfl⟩,
      ⟨oldActiveWitness .rcc35 (by simp [oldActiveJudgments]), rfl⟩,
      ⟨oldActiveWitness .rcc36 (by simp [oldActiveJudgments]), rfl⟩⟩

theorem all_five_facets_lose_old_current_authority :
    ¬ CurrentlyUsable demoSystem topologyPost .rcc32 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc33 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc34 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc35 ∧
      ¬ CurrentlyUsable demoSystem topologyPost .rcc36 := by
  rcases all_five_facets_are_bound with
    ⟨rcc32Bound, rcc33Bound, rcc34Bound, rcc35Bound, rcc36Bound⟩
  exact
    ⟨affected_rcc32_not_currently_usable
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc32 rcc32Bound,
      affected_rcc33_not_currently_usable
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc33 rcc33Bound,
      affected_rcc34_not_currently_usable
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc34 rcc34Bound,
      affected_rcc35_not_currently_usable
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc35 rcc35Bound,
      affected_rcc36_not_currently_usable
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc36 rcc36Bound⟩

/-! CM-TOPOLOGY-01: a stale parent cannot pass the CAS fence. -/

def staleParentSnapshot : SealedTopologySnapshot demoSystem :=
  { successorSnapshot with parentHead := .stale }

theorem stale_parent_snapshot_cannot_form_delta
    (delta : TopologyDelta demoSystem oldSnapshot staleParentSnapshot) :
    False := by
  have impossible : DemoHead.stale = DemoHead.old := by
    simpa [staleParentSnapshot, oldSnapshot,
      SealedTopologySnapshot.head, oldAnchor] using delta.expectedParent
  cases impossible

theorem same_epoch_delta_is_rejected
    {old new : SealedTopologySnapshot demoSystem}
    (delta : TopologyDelta demoSystem old new)
    (sameEpoch : new.epoch = old.epoch) :
    False :=
  topology_change_epoch_changed delta sameEpoch

theorem rogue_authority_is_rejected
    (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot)
    (rogue : delta.authority = .rogue) :
    False := by
  have authorized := delta.authorized
  rw [rogue] at authorized
  simp [demoSystem, demoAuthorizedChange] at authorized

/-! CM-TOPOLOGY-02: a no-op topology transition cannot supply a nonempty delta. -/

theorem no_op_snapshot_cannot_form_delta
    {old new : SealedTopologySnapshot demoSystem}
    (delta : TopologyDelta demoSystem old new)
    (sameValues :
      ∀ slot,
        demoSystem.valueAt old.context slot =
          demoSystem.valueAt new.context slot) :
    False := by
  obtain ⟨slot, member, _scoped, changed⟩ :=
    topology_delta_has_changed_in_scope_slot delta
  exact changed (sameValues slot)

/-! CM-TOPOLOGY-02b: an out-of-scope slot cannot populate a lawful delta. -/

theorem out_of_scope_delta_member_is_rejected
    {old new : SealedTopologySnapshot demoSystem}
    (delta : TopologyDelta demoSystem old new)
    (slot : TopologySlot DemoSlotQ)
    (member : slot ∈ delta.changedSlots)
    (outOfScope : ¬ demoSystem.inScopeSlot old.context slot) :
    False :=
  outOfScope (delta.changedSound slot member).1

theorem external_slot_is_really_out_of_scope :
    ¬ demoSystem.inScopeSlot oldSnapshot.context externalSlot := by
  simp [demoSystem, demoInScopeSlot, externalSlot]

theorem external_slot_really_changes :
    demoSystem.valueAt oldSnapshot.context externalSlot ≠
      demoSystem.valueAt successorSnapshot.context externalSlot := by
  simp [demoSystem, demoValueAt, externalSlot,
    SealedTopologySnapshot.context, oldSnapshot, successorSnapshot,
    oldAnchor, successorAnchor]

theorem changed_external_slot_cannot_enter_lawful_delta
    (delta : TopologyDelta demoSystem oldSnapshot successorSnapshot)
    (member : externalSlot ∈ delta.changedSlots) :
    False :=
  out_of_scope_delta_member_is_rejected
    delta externalSlot member external_slot_is_really_out_of_scope

/-! CM-TOPOLOGY-03: successor history cannot erase an old mandatory receipt. -/

def rewrittenHistoricalReceipt :
    DemoJudgment → DemoWindow → Option DemoReceipt
  | .replacement, .current => some .replacement
  | _, _ => none

theorem successor_receipts_are_anchor_derived :
    successorSnapshot.historicalReceipt = successorHistoricalReceipt := by
  funext judgment window
  cases judgment <;> cases window <;>
    rfl

theorem history_rewrite_function_is_not_successor_history :
    successorSnapshot.historicalReceipt ≠ rewrittenHistoricalReceipt := by
  intro equal
  have missing :=
    congrFun (congrFun equal .rcc32) .current
  simp [SealedTopologySnapshot.historicalReceipt,
    demoSystem, demoReceiptAt, demoAnchorClass,
    successorSnapshot, successorAnchor,
    successorHistoricalReceipt, rewrittenHistoricalReceipt] at missing

theorem admitted_history_is_not_rewritten :
    topologyPost.historicalReceipt .rcc32 .current = some .rcc32 := by
  exact historical_validity_preserved
    demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
      .rcc32 .current .rcc32 rfl

/-! CM-TOPOLOGY-03b: every evidence predicate is pinned to the full anchor. -/

def staleAssumptionAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot :=
  { successorAnchor with assumptionRoot := .old }

def staleEpochAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot :=
  { successorAnchor with epoch := .old }

def staleHeadAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot :=
  { successorAnchor with head := .stale }

def staleWindowAnchor :
    TopologyAnchor
      DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot :=
  { successorAnchor with window := .stale }

def successorEvidenceBundleAt
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot) : Prop :=
  demoObservationAdmittedAt anchor .host () (demoSlot .host) .successor ∧
    demoCertificateAcceptedAt
      .evidenceProfile anchor .replacement () ∧
    demoReplayableAt anchor .replacement .replacement ∧
    demoReceiptAt anchor .replacement .current = some .replacement ∧
    demoReceiptSupports
      anchor .replacement .replacement .evidenceProfile ()

/--
Each evidence relation is rejected independently at a malformed anchor.  This
prevents a conjunction test from staying green merely because a different
relation still rejects the bundle.
-/
def successorEvidenceIndividuallyRejectedAt
    (anchor :
      TopologyAnchor
        DemoContext DemoEpoch DemoHead DemoWindow DemoAssumptionRoot) : Prop :=
  (¬ demoObservationAdmittedAt
      anchor .host () (demoSlot .host) .successor) ∧
    (¬ demoCertificateAcceptedAt
      .evidenceProfile anchor .replacement ()) ∧
    (¬ demoReplayableAt anchor .replacement .replacement) ∧
    demoReceiptAt anchor .replacement .current ≠ some .replacement ∧
    (¬ demoReceiptSupports
      anchor .replacement .replacement .evidenceProfile ())

theorem exact_successor_anchor_accepts_evidence_bundle :
    successorEvidenceBundleAt successorAnchor := by
  simp [successorEvidenceBundleAt, demoObservationAdmittedAt,
    demoCertificateAcceptedAt, demoReplayableAt, demoReceiptAt,
    demoReceiptSupports, demoAnchorClass, demoValueAt,
    successorAnchor, successorHistoricalReceipt, demoSlot]

theorem stale_assumption_root_rejects_evidence_bundle :
    ¬ successorEvidenceBundleAt staleAssumptionAnchor := by
  simp [successorEvidenceBundleAt, demoObservationAdmittedAt,
    demoCertificateAcceptedAt, demoReplayableAt, demoReceiptAt,
    demoReceiptSupports, demoAnchorClass, staleAssumptionAnchor,
    successorAnchor]

theorem stale_epoch_rejects_evidence_bundle :
    ¬ successorEvidenceBundleAt staleEpochAnchor := by
  simp [successorEvidenceBundleAt, demoObservationAdmittedAt,
    demoCertificateAcceptedAt, demoReplayableAt, demoReceiptAt,
    demoReceiptSupports, demoAnchorClass, staleEpochAnchor,
    successorAnchor]

theorem stale_head_rejects_evidence_bundle :
    ¬ successorEvidenceBundleAt staleHeadAnchor := by
  simp [successorEvidenceBundleAt, demoObservationAdmittedAt,
    demoCertificateAcceptedAt, demoReplayableAt, demoReceiptAt,
    demoReceiptSupports, demoAnchorClass, staleHeadAnchor,
    successorAnchor]

theorem stale_window_rejects_evidence_bundle :
    ¬ successorEvidenceBundleAt staleWindowAnchor := by
  simp [successorEvidenceBundleAt, demoObservationAdmittedAt,
    demoCertificateAcceptedAt, demoReplayableAt, demoReceiptAt,
    demoReceiptSupports, demoAnchorClass, staleWindowAnchor,
    successorAnchor]

theorem stale_assumption_root_rejects_each_evidence_relation :
    successorEvidenceIndividuallyRejectedAt staleAssumptionAnchor := by
  simp [successorEvidenceIndividuallyRejectedAt,
    demoObservationAdmittedAt, demoCertificateAcceptedAt,
    demoReplayableAt, demoReceiptAt, demoReceiptSupports,
    demoAnchorClass, staleAssumptionAnchor, successorAnchor]

theorem stale_epoch_rejects_each_evidence_relation :
    successorEvidenceIndividuallyRejectedAt staleEpochAnchor := by
  simp [successorEvidenceIndividuallyRejectedAt,
    demoObservationAdmittedAt, demoCertificateAcceptedAt,
    demoReplayableAt, demoReceiptAt, demoReceiptSupports,
    demoAnchorClass, staleEpochAnchor, successorAnchor]

theorem stale_head_rejects_each_evidence_relation :
    successorEvidenceIndividuallyRejectedAt staleHeadAnchor := by
  simp [successorEvidenceIndividuallyRejectedAt,
    demoObservationAdmittedAt, demoCertificateAcceptedAt,
    demoReplayableAt, demoReceiptAt, demoReceiptSupports,
    demoAnchorClass, staleHeadAnchor, successorAnchor]

theorem stale_window_rejects_each_evidence_relation :
    successorEvidenceIndividuallyRejectedAt staleWindowAnchor := by
  simp [successorEvidenceIndividuallyRejectedAt,
    demoObservationAdmittedAt, demoCertificateAcceptedAt,
    demoReplayableAt, demoReceiptAt, demoReceiptSupports,
    demoAnchorClass, staleWindowAnchor, successorAnchor]

/-! CM-TOPOLOGY-04: a marker without a receipt is not semantic authority. -/

def emptyHistoricalReceipt :
    DemoJudgment → DemoWindow → Option DemoReceipt :=
  fun _ _ => none

theorem marker_only_without_receipt_is_rejected :
    ¬ SemanticallyActiveAt demoSystem oldAnchor
      emptyHistoricalReceipt .rcc32 := by
  rintro ⟨witness⟩
  have lookup := witness.lookup
  simp [emptyHistoricalReceipt] at lookup

/-! CM-TOPOLOGY-05: an old certificate cannot be reused at the successor context. -/

theorem old_certificate_reuse_at_successor_is_rejected :
    ¬ FacetBoundAt demoSystem successorAnchor successorHistoricalReceipt
      .rcc32 .failureCoverage := by
  rintro ⟨witness, _facet⟩
  have accepted := witness.accepted
  simp [demoSystem, demoCertificateAcceptedAt, demoAnchorClass,
    successorAnchor] at accepted

theorem wrong_facet_alias_is_rejected :
    ¬ FacetBoundAt demoSystem oldAnchor oldHistoricalReceipt
      .rcc32 .evidenceProfile := by
  rintro ⟨witness, facet⟩
  have mustBeFailure :=
    demo_rcc32_accepted_facet_exact
      witness.facet witness.certificate witness.accepted
  have impossible :
      TopologyFacet.failureCoverage = .evidenceProfile :=
    mustBeFailure.symm.trans facet
  cases impossible

/-! Transport is bound to a same-claim, replayable successor judgment. -/

theorem rcc35_transport_state_is_exact :
    topologyPost.currentState .rcc35 = .transported .replacement := by
  rfl

theorem rcc35_is_affected : Affected oldSnapshot .rcc35 := by
  change .rcc35 ∈ oldActiveJudgments
  exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))

theorem rcc35_transport_is_bound_to_successor :
    SameClaim demoSystem .rcc35 .replacement ∧
      SemanticallyActiveAt demoSystem successorAnchor
        successorHistoricalReceipt .replacement := by
  have bound :=
    transport_bound_to_successor_topology
      demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
        .rcc35 rcc35_is_affected
  simpa [topologyPost, rcc35_transport_state_is_exact] using bound

theorem replacement_without_successor_certificate_is_rejected :
    ¬ SemanticallyActiveAt demoSystem successorAnchor
      successorHistoricalReceipt .rcc35 := by
  rintro ⟨witness⟩
  have accepted := witness.accepted
  cases witness.facet <;>
    simp [demoSystem, demoCertificateAcceptedAt, demoAnchorClass,
      successorAnchor] at accepted

/-!
The authoritative RCC-37 kernel invalidates the exact old active universe.
Selective field-level dependency extraction is an explicit nonclaim owned by
RCC-21; these witnesses do not present an omitted dependency as newly derived.
-/

theorem old_active_rcc36_is_affected :
    Affected oldSnapshot .rcc36 :=
  old_active_universe_is_affected
    oldSnapshot .rcc36
      (old_active_sound .rcc36 (by simp [oldActiveJudgments]))

theorem old_active_rcc36_is_not_usable :
    ¬ CurrentlyUsable demoSystem topologyPost .rcc36 :=
  affected_not_currently_usable
    demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan
      .rcc36 old_active_rcc36_is_affected

/-!
CM-TOPOLOGY-07: topology kind is part of the stable slot identity.  The old
arbitrary registry relabeling countermodel is therefore unconstructible.
-/

theorem same_q_different_topology_kind_is_not_same_slot :
    demoSlot .host ≠ demoSlot .custody := by
  decide

theorem topology_slot_equality_preserves_kind
    (left right : TopologySlot DemoSlotQ)
    (equal : left = right) :
    left.kind = right.kind := by
  exact congrArg TopologySlot.kind equal

/-! The post-state is the actual successor epoch/head/context, never the source. -/

theorem post_state_is_bound_to_successor :
    topologyPost.epoch = .successor ∧
      topologyPost.head = .successor ∧
      topologyPost.context = .successor := by
  exact
    ⟨post_snapshot_epoch_is_successor
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan,
      post_snapshot_head_is_successor
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan,
      post_snapshot_context_is_successor
        demoSystem oldSnapshot successorSnapshot hostDelta topologyPlan⟩

#print axioms topology_delta_exact
#print axioms topology_delta_has_changed_slot
#print axioms affected_requires_resolution
#print axioms affected_not_currently_usable
#print axioms historical_validity_preserved
#print axioms transport_bound_to_successor_topology
#print axioms old_active_universe_is_affected
#print axioms affected_rcc32_not_currently_usable
#print axioms affected_rcc33_not_currently_usable
#print axioms affected_rcc34_not_currently_usable
#print axioms affected_rcc35_not_currently_usable
#print axioms affected_rcc36_not_currently_usable
#print axioms stale_parent_snapshot_cannot_form_delta
#print axioms no_op_snapshot_cannot_form_delta
#print axioms out_of_scope_delta_member_is_rejected
#print axioms external_slot_is_really_out_of_scope
#print axioms external_slot_really_changes
#print axioms changed_external_slot_cannot_enter_lawful_delta
#print axioms history_rewrite_function_is_not_successor_history
#print axioms same_epoch_delta_is_rejected
#print axioms rogue_authority_is_rejected
#print axioms exact_successor_anchor_accepts_evidence_bundle
#print axioms stale_assumption_root_rejects_evidence_bundle
#print axioms stale_epoch_rejects_evidence_bundle
#print axioms stale_head_rejects_evidence_bundle
#print axioms stale_window_rejects_evidence_bundle
#print axioms stale_assumption_root_rejects_each_evidence_relation
#print axioms stale_epoch_rejects_each_evidence_relation
#print axioms stale_head_rejects_each_evidence_relation
#print axioms stale_window_rejects_each_evidence_relation
#print axioms marker_only_without_receipt_is_rejected
#print axioms old_certificate_reuse_at_successor_is_rejected
#print axioms wrong_facet_alias_is_rejected
#print axioms rcc35_transport_is_bound_to_successor
#print axioms old_active_rcc36_is_affected
#print axioms old_active_rcc36_is_not_usable
#print axioms same_q_different_topology_kind_is_not_same_slot

end Residua.RCC.TrustTopologyInvalidation.Tests

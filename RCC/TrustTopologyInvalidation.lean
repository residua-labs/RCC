import RCC.TemporalValidity

/-!
# RCC-37 Sealed Trust-Topology Invalidation

RCC-37 treats custody, host, operator, generator, key-lineage, and
model-lineage facts as observations in a sealed topology snapshot.  A topology
change is not a caller-written status bit: it is an exact, nonempty delta
between two sealed snapshots, bound to an expected parent head and authorized
by the pre-state.

This first authoritative kernel is deliberately conservative.  Every judgment
whose current certificate is bound to the old topology snapshot is affected by
any nonempty topology delta.  Selective field-level invalidation is an
optimization that additionally requires RCC-21 dependency-extraction
completeness; an incomplete dependency scanner is not accepted here.

Historical receipts are preserved by an explicit history-extension proof.
Current usability is semantic: it requires a replayable receipt and an
accepted, context-indexed facet certificate.  The post-state is mechanically
derived from the sealed old active universe and a proof-carrying resolution
plan; instances cannot supply a free `usable` marker.

The five certificate facets are the generic adapter interface for RCC-32
through RCC-36.  This file does not claim that the repository's concrete
RCC-32..36 artifact types have already been wired to that interface; a concrete
instance must supply those payload types and verifier relations without
collapsing them to booleans.

Prelude-only Lean 4.14; no Mathlib, no proof holes, and no custom axioms.
-/

namespace Residua.RCC.TrustTopologyInvalidation

open Residua.RCC.TemporalValidity

universe u

/-- The six topology surfaces frozen by the RCC specification. -/
inductive TopologyTargetKind where
  | custody
  | host
  | operator
  | generator
  | keyLineage
  | modelLineage
  deriving DecidableEq, Repr

/--
A stable topology coordinate.  The slot identity does not change when the
observed host, custodian, operator, generator, key, or model lineage changes.
-/
structure TopologySlot (SlotQ : Type u) where
  q : SlotQ
  kind : TopologyTargetKind
  deriving DecidableEq, Repr

/-- Proof-carrying certificate families consumed from RCC-32 through RCC-36. -/
inductive TopologyFacet where
  | failureCoverage
  | commonCauseIndependence
  | effectiveAuthorityQuorum
  | evidenceProfile
  | canonicalContribution
  deriving DecidableEq, Repr

/--
The full semantic coordinate of one sealed topology observation.  None of
these fields is decorative: observation admission, receipt replay, certificate
acceptance, and receipt/certificate binding are all indexed by this anchor.
-/
structure TopologyAnchor
    (Context Epoch Head Window AssumptionRoot : Type u) where
  context : Context
  epoch : Epoch
  head : Head
  window : Window
  assumptionRoot : AssumptionRoot
  deriving Repr

/--
Domain coordinates and verifier relations for one topology-invalidating
instance.  `Certificate facet` may be instantiated with the actual RCC proof
object for that facet.
-/
structure TrustTopologySystem where
  SlotQ : Type u
  ValueQ : Type u
  ObservationQ : Type u
  AttestationQ : Type u
  Context : Type u
  Epoch : Type u
  Head : Type u
  Window : Type u
  AssumptionRoot : Type u
  Judgment : Type u
  ClaimQ : Type u
  Receipt : Type u
  Authority : Type u
  Certificate : TopologyFacet → Type u
  slotDecidableEq : DecidableEq (TopologySlot SlotQ)
  judgmentDecidableEq : DecidableEq Judgment
  inScopeSlot : Context → TopologySlot SlotQ → Prop
  inScopeSlotDecidable :
    (context : Context) → (slot : TopologySlot SlotQ) →
      Decidable (inScopeSlot context slot)
  valueAt : Context → TopologySlot SlotQ → ValueQ
  observationAdmittedAt :
    TopologyAnchor Context Epoch Head Window AssumptionRoot →
      ObservationQ → AttestationQ →
      TopologySlot SlotQ → ValueQ → Prop
  certificateAcceptedAt :
    (facet : TopologyFacet) →
      TopologyAnchor Context Epoch Head Window AssumptionRoot →
        Judgment → Certificate facet → Prop
  replayableAt :
    TopologyAnchor Context Epoch Head Window AssumptionRoot →
      Judgment → Receipt → Prop
  receiptAt :
    TopologyAnchor Context Epoch Head Window AssumptionRoot →
      Judgment → Window → Option Receipt
  receiptSupports :
    TopologyAnchor Context Epoch Head Window AssumptionRoot →
      (judgment : Judgment) → Receipt →
        (facet : TopologyFacet) → Certificate facet → Prop
  claimOf : Judgment → ClaimQ
  authorizedChange :
    Authority →
      TopologyAnchor Context Epoch Head Window AssumptionRoot →
      TopologyAnchor Context Epoch Head Window AssumptionRoot →
        Prop
  successorEpoch : Epoch → Epoch → Prop
  successorEpochStrict :
    ∀ source successor,
      successorEpoch source successor → successor ≠ source

/-- Transport preserves the system's canonical claim identity definitionally. -/
def SameClaim
    (S : TrustTopologySystem)
    (judgment replacement : S.Judgment) : Prop :=
  S.claimOf judgment = S.claimOf replacement

/-- One admitted observation of one stable topology slot. -/
structure TopologyObservation
    (S : TrustTopologySystem)
    (anchor :
      TopologyAnchor
        S.Context S.Epoch S.Head S.Window S.AssumptionRoot) where
  slot : TopologySlot S.SlotQ
  value : S.ValueQ
  observationQ : S.ObservationQ
  attestationQ : S.AttestationQ
  admitted :
    S.observationAdmittedAt
      anchor observationQ attestationQ slot value
  valueExact : value = S.valueAt anchor.context slot

/--
One receipt and one accepted facet certificate are joined by an explicit
support relation at the same full topology anchor.
-/
structure ActiveWitness
    (S : TrustTopologySystem)
    (anchor :
      TopologyAnchor
        S.Context S.Epoch S.Head S.Window S.AssumptionRoot)
    (historicalReceipt : S.Judgment → S.Window → Option S.Receipt)
    (judgment : S.Judgment) where
  facet : TopologyFacet
  receipt : S.Receipt
  certificate : S.Certificate facet
  lookup :
    historicalReceipt judgment anchor.window = some receipt
  replayable :
    S.replayableAt anchor judgment receipt
  accepted :
    S.certificateAcceptedAt facet anchor judgment certificate
  supports :
    S.receiptSupports anchor judgment receipt facet certificate

/- A judgment is active through one exact RCC facet at one exact anchor. -/
def FacetBoundAt
    (S : TrustTopologySystem)
    (anchor :
      TopologyAnchor
        S.Context S.Epoch S.Head S.Window S.AssumptionRoot)
    (historicalReceipt : S.Judgment → S.Window → Option S.Receipt)
    (judgment : S.Judgment) (facet : TopologyFacet) : Prop :=
  ∃ witness : ActiveWitness S anchor historicalReceipt judgment,
    witness.facet = facet

/--
Semantic current authority before invalidation.  A bare state marker is
insufficient: one witness must join lookup, replay, accepted certificate, and
receipt support at the exact full anchor.
-/
def SemanticallyActiveAt
    (S : TrustTopologySystem)
    (anchor :
      TopologyAnchor
        S.Context S.Epoch S.Head S.Window S.AssumptionRoot)
    (historicalReceipt : S.Judgment → S.Window → Option S.Receipt)
    (judgment : S.Judgment) : Prop :=
  Nonempty (ActiveWitness S anchor historicalReceipt judgment)

/-- A facet-bound witness is in particular a semantic active witness. -/
theorem facet_bound_semantically_active
    {S : TrustTopologySystem}
    {anchor :
      TopologyAnchor
        S.Context S.Epoch S.Head S.Window S.AssumptionRoot}
    {historicalReceipt : S.Judgment → S.Window → Option S.Receipt}
    {judgment : S.Judgment}
    {facet : TopologyFacet}
    (bound :
      FacetBoundAt S anchor historicalReceipt judgment facet) :
    SemanticallyActiveAt S anchor historicalReceipt judgment := by
  obtain ⟨witness, _⟩ := bound
  exact ⟨witness⟩

/--
An exact sealed topology snapshot and the exact finite universe of judgments
currently authorized by certificates bound to it.
-/
structure SealedTopologySnapshot (S : TrustTopologySystem) where
  anchor :
    TopologyAnchor
      S.Context S.Epoch S.Head S.Window S.AssumptionRoot
  parentHead : S.Head
  observations : List (TopologyObservation S anchor)
  observationSlotsNodup : (observations.map fun observation => observation.slot).Nodup
  observationSound :
    ∀ observation, observation ∈ observations →
      S.inScopeSlot anchor.context observation.slot
  observationComplete :
    ∀ slot, S.inScopeSlot anchor.context slot →
      ∃ observation,
        observation ∈ observations ∧ observation.slot = slot
  allKindsCovered :
    ∀ kind,
      ∃ observation,
        observation ∈ observations ∧ observation.slot.kind = kind
  activeJudgments : List S.Judgment
  activeJudgmentsNodup : activeJudgments.Nodup
  activeSound :
    ∀ judgment, judgment ∈ activeJudgments →
      SemanticallyActiveAt S anchor (S.receiptAt anchor) judgment
  activeComplete :
    ∀ judgment,
      SemanticallyActiveAt S anchor (S.receiptAt anchor) judgment →
        judgment ∈ activeJudgments

/-- Convenience projections keep transition statements readable. -/
def SealedTopologySnapshot.context
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) : S.Context :=
  snapshot.anchor.context

def SealedTopologySnapshot.epoch
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) : S.Epoch :=
  snapshot.anchor.epoch

def SealedTopologySnapshot.head
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) : S.Head :=
  snapshot.anchor.head

def SealedTopologySnapshot.window
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) : S.Window :=
  snapshot.anchor.window

def SealedTopologySnapshot.assumptionRoot
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) : S.AssumptionRoot :=
  snapshot.anchor.assumptionRoot

/-- Receipt projection is derived from the full anchor, never caller supplied. -/
def SealedTopologySnapshot.historicalReceipt
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S) :
    S.Judgment → S.Window → Option S.Receipt :=
  S.receiptAt snapshot.anchor

/-- Historical validity at a sealed topology snapshot. -/
def ValidAt
    {S : TrustTopologySystem}
    (snapshot : SealedTopologySnapshot S)
    (judgment : S.Judgment) (window : S.Window)
    (receipt : S.Receipt) : Prop :=
  S.receiptAt snapshot.anchor judgment window = some receipt

/--
Exact, nonempty topology change.  `changedSlots` is both sound and complete
for value changes over the stable slot universe.  The new snapshot is fenced
to the exact old head and the old authority approves the transition.

The first authoritative kernel keeps the slot universe fixed across this
transition (`scopeExact`).  Add/remove is represented by an explicit value in
a stable slot domain, or by a separately admitted schema/source-universe
reepoch; it is not silently inferred by this delta.
-/
structure TopologyDelta
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S) where
  changedSlots : List (TopologySlot S.SlotQ)
  changedSlotsNodup : changedSlots.Nodup
  scopeExact :
    ∀ slot,
      S.inScopeSlot old.context slot ↔
        S.inScopeSlot new.context slot
  changedSound :
    ∀ slot, slot ∈ changedSlots →
      S.inScopeSlot old.context slot ∧
        S.valueAt old.context slot ≠ S.valueAt new.context slot
  changedComplete :
    ∀ slot,
      S.inScopeSlot old.context slot →
      S.valueAt old.context slot ≠ S.valueAt new.context slot →
        slot ∈ changedSlots
  nonempty : changedSlots ≠ []
  authority : S.Authority
  authorized :
    S.authorizedChange authority old.anchor new.anchor
  epochAdvance :
    S.successorEpoch old.epoch new.epoch
  expectedParent : new.parentHead = old.head
  headChanged : new.head ≠ old.head
  historyExtends :
    ∀ judgment window receipt,
      S.receiptAt old.anchor judgment window = some receipt →
        S.receiptAt new.anchor judgment window = some receipt

/-- The delta list is exactly the set of changed in-scope slots. -/
theorem topology_delta_exact
    {S : TrustTopologySystem}
    {old new : SealedTopologySnapshot S}
    (delta : TopologyDelta S old new)
    (slot : TopologySlot S.SlotQ) :
    slot ∈ delta.changedSlots ↔
      S.inScopeSlot old.context slot ∧
        S.valueAt old.context slot ≠ S.valueAt new.context slot := by
  constructor
  · exact delta.changedSound slot
  · exact fun changed =>
      delta.changedComplete slot changed.1 changed.2

/-- A lawful topology transition always changes at least one stable slot. -/
theorem topology_delta_has_changed_slot
    {S : TrustTopologySystem}
    {old new : SealedTopologySnapshot S}
    (delta : TopologyDelta S old new) :
    ∃ slot, slot ∈ delta.changedSlots := by
  cases slots : delta.changedSlots with
  | nil =>
      exact False.elim (delta.nonempty slots)
  | cons slot rest =>
      exact ⟨slot, by simp⟩

/-- The nonempty delta always exposes a genuinely changed in-scope slot. -/
theorem topology_delta_has_changed_in_scope_slot
    {S : TrustTopologySystem}
    {old new : SealedTopologySnapshot S}
    (delta : TopologyDelta S old new) :
    ∃ slot,
      slot ∈ delta.changedSlots ∧
        S.inScopeSlot old.context slot ∧
        S.valueAt old.context slot ≠ S.valueAt new.context slot := by
  obtain ⟨slot, member⟩ := topology_delta_has_changed_slot delta
  exact ⟨slot, member, delta.changedSound slot member⟩

/--
Conservative authoritative affected set: every active judgment is bound to the
old topology and is therefore affected by any nonempty exact topology delta.
-/
def Affected
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S)
    (judgment : S.Judgment) : Prop :=
  judgment ∈ old.activeJudgments

/-- The affected universe is mechanically derived, not supplied by an instance. -/
def affectedJudgments
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S) : List S.Judgment :=
  old.activeJudgments

theorem affected_judgments_exact
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S)
    (judgment : S.Judgment) :
    judgment ∈ affectedJudgments old ↔ Affected old judgment := by
  rfl

theorem affected_judgments_nodup
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S) :
    (affectedJudgments old).Nodup :=
  old.activeJudgmentsNodup

/-- Every semantically active old judgment is mechanically affected. -/
theorem semantically_active_is_affected
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S)
    (judgment : S.Judgment)
    (active :
      SemanticallyActiveAt S old.anchor
        old.historicalReceipt judgment) :
    Affected old judgment :=
  old.activeComplete judgment active

/--
The only post-change dispositions for an affected judgment.  Transport is
constructible only with a same-claim replacement that is semantically active
under the sealed new topology snapshot.

This is judgment-level transport.  It does not claim that the replacement
preserves every old facet; a facet-preserving transport adapter must carry and
verify that stronger proof separately.
-/
inductive TopologyResolution
    (S : TrustTopologySystem)
    (new : SealedTopologySnapshot S)
    (judgment : S.Judgment) where
  | revalidate
  | transport
      (replacement : S.Judgment)
      (sameClaim : SameClaim S judgment replacement)
      (replacementActive :
        SemanticallyActiveAt S new.anchor
          new.historicalReceipt replacement)
  | reopen

/-- Pointwise proof-carrying resolution for the derived affected universe. -/
structure TopologyResolutionPlan
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new) where
  resolve :
    (judgment : S.Judgment) →
      Affected old judgment →
        TopologyResolution S new judgment

def TopologyResolution.state
    {S : TrustTopologySystem}
    {new : SealedTopologySnapshot S}
    {judgment : S.Judgment} :
    TopologyResolution S new judgment →
      CurrentJudgmentState S.Judgment
  | .revalidate => .revalidate
  | .transport replacement _ _ => .transported replacement
  | .reopen => .reopened

/-- Successor snapshot produced by a topology invalidation transition. -/
structure TopologyPostSnapshot (S : TrustTopologySystem) where
  /--
  This is the successor anchor plus an invalidation/disposition ledger.  It is
  not a reconstructed successor authority registry: a transported judgment is
  usable only through the active witness carried by its transport resolution.
  -/
  anchor :
    TopologyAnchor
      S.Context S.Epoch S.Head S.Window S.AssumptionRoot
  parentHead : S.Head
  currentState : S.Judgment → CurrentJudgmentState S.Judgment

def TopologyPostSnapshot.context
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) : S.Context :=
  snapshot.anchor.context

def TopologyPostSnapshot.epoch
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) : S.Epoch :=
  snapshot.anchor.epoch

def TopologyPostSnapshot.head
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) : S.Head :=
  snapshot.anchor.head

def TopologyPostSnapshot.window
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) : S.Window :=
  snapshot.anchor.window

def TopologyPostSnapshot.assumptionRoot
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) : S.AssumptionRoot :=
  snapshot.anchor.assumptionRoot

def TopologyPostSnapshot.historicalReceipt
    {S : TrustTopologySystem}
    (snapshot : TopologyPostSnapshot S) :
    S.Judgment → S.Window → Option S.Receipt :=
  S.receiptAt snapshot.anchor

/--
Apply the exact topology change.  No caller supplies post-state markers.
Every old active judgment is resolved; every other old judgment is conservatively
reopened rather than silently treated as usable.
-/
def applyTopologyChange
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta) :
    TopologyPostSnapshot S where
  anchor := new.anchor
  parentHead := new.parentHead
  currentState := fun judgment =>
    letI : DecidableEq S.Judgment := S.judgmentDecidableEq
    if affected : judgment ∈ old.activeJudgments then
      (plan.resolve judgment affected).state
    else
      .reopened

/-- Semantic current usability in the post-state. -/
def CurrentlyUsable
    (S : TrustTopologySystem)
    (post : TopologyPostSnapshot S)
    (judgment : S.Judgment) : Prop :=
  post.currentState judgment = .usable ∧
    SemanticallyActiveAt S post.anchor
      post.historicalReceipt judgment

/-- Every affected judgment receives one of the three non-usable dispositions. -/
theorem affected_requires_resolution
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (affected : Affected old judgment) :
    RequiresRevalidationTransportOrReopen
      ((applyTopologyChange S old new delta plan).currentState judgment) := by
  change judgment ∈ old.activeJudgments at affected
  cases resolution : plan.resolve judgment affected <;>
    simp [applyTopologyChange, affected, resolution,
      TopologyResolution.state, RequiresRevalidationTransportOrReopen]

/-- No affected judgment retains current authority after the topology change. -/
theorem affected_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (affected : Affected old judgment) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment := by
  intro usable
  have resolution :=
    affected_requires_resolution S old new delta plan judgment affected
  rw [usable.1] at resolution
  exact resolution

/-- A non-active old judgment is never silently upgraded to usable. -/
theorem inactive_judgment_reopened
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (inactive : ¬ Affected old judgment) :
    (applyTopologyChange S old new delta plan).currentState judgment =
      .reopened := by
  change ¬ judgment ∈ old.activeJudgments at inactive
  simp [applyTopologyChange, inactive]

/-- Old historical receipts remain historical facts in the successor ledger. -/
theorem historical_validity_preserved
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (window : S.Window)
    (receipt : S.Receipt)
    (valid : ValidAt old judgment window receipt) :
    (applyTopologyChange S old new delta plan).historicalReceipt
        judgment window = some receipt := by
  exact delta.historyExtends judgment window receipt valid

theorem post_snapshot_epoch_is_successor
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta) :
    (applyTopologyChange S old new delta plan).epoch = new.epoch := by
  rfl

theorem post_snapshot_head_is_successor
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta) :
    (applyTopologyChange S old new delta plan).head = new.head := by
  rfl

theorem post_snapshot_context_is_successor
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta) :
    (applyTopologyChange S old new delta plan).context = new.context := by
  rfl

/-- The CAS fence is part of every lawful topology delta. -/
theorem topology_change_expected_parent
    {S : TrustTopologySystem}
    {old new : SealedTopologySnapshot S}
    (delta : TopologyDelta S old new) :
    new.parentHead = old.head :=
  delta.expectedParent

/-- A topology invalidation is an admitted successor epoch, not an in-place relabel. -/
theorem topology_change_epoch_changed
    {S : TrustTopologySystem}
    {old new : SealedTopologySnapshot S}
    (delta : TopologyDelta S old new) :
    new.epoch ≠ old.epoch :=
  S.successorEpochStrict old.epoch new.epoch delta.epochAdvance

/--
If an affected judgment is transported, the replacement is a same-claim
judgment with a replayable, accepted certificate under the new topology.
-/
theorem transport_bound_to_successor_topology
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (affected : Affected old judgment) :
    match
      (applyTopologyChange S old new delta plan).currentState judgment
    with
    | .transported replacement =>
        SameClaim S judgment replacement ∧
          SemanticallyActiveAt S new.anchor
            new.historicalReceipt replacement
    | _ => True := by
  change judgment ∈ old.activeJudgments at affected
  cases resolution : plan.resolve judgment affected with
  | revalidate =>
      simp [applyTopologyChange, affected, resolution,
        TopologyResolution.state]
  | transport replacement sameClaim replacementActive =>
      simpa [applyTopologyChange, affected, resolution,
        TopologyResolution.state] using
        And.intro sameClaim replacementActive
  | reopen =>
      simp [applyTopologyChange, affected, resolution,
        TopologyResolution.state]

/--
An old historical receipt alone never preserves current authority across a
topology change.
-/
theorem historically_valid_does_not_imply_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (window : S.Window)
    (receipt : S.Receipt)
    (valid : ValidAt old judgment window receipt)
    (active : Affected old judgment) :
    (applyTopologyChange S old new delta plan).historicalReceipt
        judgment window = some receipt ∧
      ¬ CurrentlyUsable S
        (applyTopologyChange S old new delta plan) judgment :=
  ⟨historical_validity_preserved
      S old new delta plan judgment window receipt valid,
    affected_not_currently_usable
      S old new delta plan judgment active⟩

/--
Coarse invalidation covers the complete old active universe without relying on
a field-level dependency extractor.
-/
theorem old_active_universe_is_affected
    {S : TrustTopologySystem}
    (old : SealedTopologySnapshot S)
    (judgment : S.Judgment)
    (active :
      SemanticallyActiveAt S old.anchor
        old.historicalReceipt judgment) :
    Affected old judgment :=
  semantically_active_is_affected old judgment active

private theorem facet_bound_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (facet : TopologyFacet)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment facet) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  affected_not_currently_usable
    S old new delta plan judgment
      (semantically_active_is_affected old judgment
        (facet_bound_semantically_active bound))

theorem affected_rcc32_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment
        .failureCoverage) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  facet_bound_not_currently_usable
    S old new delta plan judgment .failureCoverage bound

theorem affected_rcc33_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment
        .commonCauseIndependence) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  facet_bound_not_currently_usable
    S old new delta plan judgment .commonCauseIndependence bound

theorem affected_rcc34_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment
        .effectiveAuthorityQuorum) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  facet_bound_not_currently_usable
    S old new delta plan judgment .effectiveAuthorityQuorum bound

theorem affected_rcc35_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment
        .evidenceProfile) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  facet_bound_not_currently_usable
    S old new delta plan judgment .evidenceProfile bound

theorem affected_rcc36_not_currently_usable
    (S : TrustTopologySystem)
    (old new : SealedTopologySnapshot S)
    (delta : TopologyDelta S old new)
    (plan : TopologyResolutionPlan S old new delta)
    (judgment : S.Judgment)
    (bound :
      FacetBoundAt S old.anchor old.historicalReceipt judgment
        .canonicalContribution) :
    ¬ CurrentlyUsable S
      (applyTopologyChange S old new delta plan) judgment :=
  facet_bound_not_currently_usable
    S old new delta plan judgment .canonicalContribution bound

end Residua.RCC.TrustTopologyInvalidation

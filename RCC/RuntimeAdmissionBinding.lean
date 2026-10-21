import RCC.GlobalSettledAdmission

/-!
# Runtime binding for canonical history and effect observations

RCC-31 and RCC-43 deliberately expose abstract observation surfaces. This
module states the missing implementation refinement explicitly:

* canonical-history membership must agree with an actual store;
* effect observation bits and receipts must agree with an actual world/journal;
* the effect journal and canonical store must describe the same occurrence.

The two deletion witnesses demonstrate that an abstract record or settlement
alone cannot establish runtime truth.
-/

namespace Residua.RCC.RuntimeAdmissionBinding

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.EffectSettlement
open Residua.RCC.GlobalSettledAdmission

universe u

/-- Actual canonical-history runtime, independent of the abstract snapshot. -/
structure CanonicalHistoryRuntime
    (EventQ Head Store AppendReceipt : Type u) where
  actualHead : Store → Head
  actualContains : Store → EventQ → Prop
  append :
    Store → Head → EventQ → Store → AppendReceipt → Prop
  appendParent :
    ∀ {pre parent event post receipt},
      append pre parent event post receipt →
        actualHead pre = parent
  appendContains :
    ∀ {pre parent event post receipt},
      append pre parent event post receipt →
        actualContains post event

/--
Sound refinement of abstract durable membership to one actual store.

This is the minimum safety grade needed by admission: abstract durable
membership cannot be true while actual membership is false.
-/
structure CanonicalHistoryRuntimeBinding
    {EventQ Head Store AppendReceipt : Type u}
    (runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (snapshot : CanonicalHistorySnapshot EventQ Head)
    (store : Store) : Prop where
  headExact :
    runtime.actualHead store = snapshot.canonicalHead
  containsSound :
    ∀ event,
      snapshot.contains event = true →
        runtime.actualContains store event
  durableSound :
    ∀ event,
      snapshot.durableContains event →
        runtime.actualContains store event

/--
Exact projection grade, stronger than the safety binding: actual membership is
also completely reflected by both abstract membership surfaces.
-/
structure ExactCanonicalHistoryRuntimeBinding
    {EventQ Head Store AppendReceipt : Type u}
    (runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (snapshot : CanonicalHistorySnapshot EventQ Head)
    (store : Store)
    extends CanonicalHistoryRuntimeBinding runtime snapshot store : Prop where
  containsComplete :
    ∀ event,
      runtime.actualContains store event →
        snapshot.contains event = true
  durableComplete :
    ∀ event,
      runtime.actualContains store event →
        snapshot.durableContains event

/-- Abstract durable membership now implies actual store membership. -/
theorem CanonicalHistoryRuntimeBinding.actual_member
    {EventQ Head Store AppendReceipt : Type u}
    {runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {snapshot : CanonicalHistorySnapshot EventQ Head}
    {store : Store}
    (binding : CanonicalHistoryRuntimeBinding runtime snapshot store)
    {event : EventQ}
    (durable : snapshot.durableContains event) :
    runtime.actualContains store event :=
  binding.durableSound event durable

/-- One actual append, without yet claiming receipt or snapshot refinement. -/
structure BoundActualAppend
    {EventQ Head Store AppendReceipt : Type u}
    (runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (parent : Head)
    (event : EventQ) where
  preStore : Store
  postStore : Store
  receipt : AppendReceipt
  appended :
    runtime.append preStore parent event postStore receipt

/-- A successful actual append is present in its post-store. -/
theorem BoundActualAppend.actual_member
    {EventQ Head Store AppendReceipt : Type u}
    {runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {parent : Head}
    {event : EventQ}
    (bound : BoundActualAppend runtime parent event) :
    runtime.actualContains bound.postStore event :=
  runtime.appendContains bound.appended

/-- Semantic identity projections carried by one append receipt. -/
structure AppendReceiptView
    (EventQ Head StoreQ AppendReceipt : Type u) where
  event : AppendReceipt → EventQ
  parentHead : AppendReceipt → Head
  successorHead : AppendReceipt → Head
  postStoreQ : AppendReceipt → StoreQ
  authentic : AppendReceipt → Prop

/--
Strong transition binding for one canonical-history append.

The abstract history snapshot is a parent-coordinate view: its head binds the
pre-store, while its durable membership claims are checked against the
post-store. The append receipt independently binds the exact event, parent,
successor, and post-store identity.
-/
structure CanonicalHistoryTransitionBinding
    {EventQ Head Store AppendReceipt StoreQ : Type u}
    (runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt)
    (storeQ : Store → StoreQ)
    (snapshot : CanonicalHistorySnapshot EventQ Head)
    (parent : Head)
    (event : EventQ) : Type u where
  append : BoundActualAppend runtime parent event
  parentSnapshotExact :
    runtime.actualHead append.preStore = snapshot.canonicalHead
  claimedParentExact :
    snapshot.canonicalHead = parent
  abstractMembershipSound :
    ∀ candidate,
      snapshot.durableContains candidate →
        runtime.actualContains append.postStore candidate
  receiptAuthentic :
    receiptView.authentic append.receipt
  receiptEventExact :
    receiptView.event append.receipt = event
  receiptParentExact :
    receiptView.parentHead append.receipt = parent
  receiptSuccessorExact :
    receiptView.successorHead append.receipt =
      runtime.actualHead append.postStore
  receiptPostStoreExact :
    receiptView.postStoreQ append.receipt = storeQ append.postStore

/-- Full transition headline consumes every identity/refinement coordinate. -/
theorem CanonicalHistoryTransitionBinding.headline
    {EventQ Head Store AppendReceipt StoreQ : Type u}
    {runtime : CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {snapshot : CanonicalHistorySnapshot EventQ Head}
    {parent : Head}
    {event : EventQ}
    (binding :
      CanonicalHistoryTransitionBinding
        runtime receiptView storeQ snapshot parent event) :
    runtime.actualHead binding.append.preStore = parent ∧
      runtime.actualContains binding.append.postStore event ∧
      receiptView.authentic binding.append.receipt ∧
      receiptView.event binding.append.receipt = event ∧
      receiptView.parentHead binding.append.receipt = parent ∧
      receiptView.successorHead binding.append.receipt =
        runtime.actualHead binding.append.postStore ∧
      receiptView.postStoreQ binding.append.receipt =
        storeQ binding.append.postStore := by
  exact
    ⟨binding.parentSnapshotExact.trans binding.claimedParentExact,
      binding.append.actual_member,
      binding.receiptAuthentic,
      binding.receiptEventExact,
      binding.receiptParentExact,
      binding.receiptSuccessorExact,
      binding.receiptPostStoreExact⟩

/-- Actual world/journal semantics, independent of supplied booleans. -/
structure EffectObservationRuntime
    (Epoch Head EffectSlot Generation Occurrence FailureName : Type u) where
  World : Type u
  Journal : Type u
  worldApplied : World → Occurrence → Prop
  historyRecorded : Journal → Occurrence → Prop
  compensationApplied : World → Occurrence → Prop
  receiptAt :
    Journal → Occurrence →
      Option
        (EffectReceipt
          Epoch Head EffectSlot Generation Occurrence FailureName)

/--
Exact binding of one supplied effect observation to actual world state.

All three booleans are exact because the settlement algebra consumes both
positive and negative polarities across recorded, compensated, and terminal
failure phases.
-/
structure EffectObservationBinding
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type u}
    (runtime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (world : runtime.World)
    (journal : runtime.Journal)
    (occurrence : Occurrence)
    (observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName) : Prop where
  worldAppliedExact :
    observation.worldApplied = true ↔
      runtime.worldApplied world occurrence
  historyRecordedExact :
    observation.historyRecorded = true ↔
      runtime.historyRecorded journal occurrence
  compensationAppliedExact :
    observation.compensationApplied = true ↔
      runtime.compensationApplied world occurrence
  receiptExact :
    runtime.receiptAt journal occurrence = observation.receipt

/--
Cross-runtime law: the effect journal's recorded fact names the same actual
canonical-history occurrence, rather than a second unrelated store.
-/
structure EffectHistoryRuntimeCoherence
    {EventQ Head Store AppendReceipt Epoch EffectSlot Generation Occurrence
      FailureName : Type u}
    (historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName)
    (store : Store)
    (journal : effectRuntime.Journal)
    (occurrence : Occurrence)
    (event : EventQ) : Prop where
  recordedIff :
    effectRuntime.historyRecorded journal occurrence ↔
      historyRuntime.actualContains store event

/-- A formally settled receipt excludes an actual applied/unrecorded split. -/
theorem fenced_settlement_excludes_actual_applied_unrecorded
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type u}
    {snapshot :
      EffectSnapshot
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {effect : ExternalEffect Occurrence Head EffectSlot}
    {observation :
      EffectObservation
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {receipt :
      EffectReceipt
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {runtime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    {world : runtime.World}
    {journal : runtime.Journal}
    (settled :
      FencedSettledReceipt snapshot effect observation receipt)
    (binding :
      EffectObservationBinding
        runtime world journal effect.occurrence observation) :
    ¬ (runtime.worldApplied world effect.occurrence ∧
        ¬ runtime.historyRecorded journal effect.occurrence) := by
  rintro ⟨actuallyApplied, actuallyUnrecorded⟩
  have appliedTrue : observation.worldApplied = true :=
    binding.worldAppliedExact.2 actuallyApplied
  have recordedFalse : observation.historyRecorded = false := by
    cases recorded : observation.historyRecorded with
    | false => rfl
    | true =>
        exact False.elim
          (actuallyUnrecorded
            (binding.historyRecordedExact.1 recorded))
  exact
    (settlement_coherent_not_applied_unrecorded
      observation receipt settled.coherent)
      ⟨appliedTrue, recordedFalse⟩

/--
Actual-world refinement of the existing external-effect admission carrier.

The append, effect observation, and effect/history cross-law all name the
event and occurrence already fixed by the same globally settled proposal.
-/
structure ActuallyGloballySettledAdmission
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    (formal :
      GloballySettledAdmission linearizer version proposal)
    (historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt)
    (receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt)
    (storeQ : Store → StoreQ)
    (effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName) : Type u where
  transition :
    CanonicalHistoryTransitionBinding
      historyRuntime receiptView storeQ environment.historySnapshot
      proposal.expectedParent formal.history.event
  world : effectRuntime.World
  journal : effectRuntime.Journal
  effectBinding :
    EffectObservationBinding
      effectRuntime world journal formal.effect.occurrence
      formal.effectObservation
  effectHistoryCoherent :
    EffectHistoryRuntimeCoherence
      historyRuntime effectRuntime transition.append.postStore journal
      formal.effect.occurrence formal.history.event

/-- The admitted event is actually present in the bound post-store. -/
theorem ActuallyGloballySettledAdmission.actual_history_member
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal :
      GloballySettledAdmission linearizer version proposal}
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    (actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime) :
    historyRuntime.actualContains
      actual.transition.append.postStore formal.history.event :=
  actual.transition.append.actual_member

/-- The actual append binds parent, event, successor, store, and receipt. -/
theorem ActuallyGloballySettledAdmission.transition_headline
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal :
      GloballySettledAdmission linearizer version proposal}
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    (actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime) :
    historyRuntime.actualHead actual.transition.append.preStore =
        proposal.expectedParent ∧
      historyRuntime.actualContains
        actual.transition.append.postStore formal.history.event ∧
      receiptView.authentic actual.transition.append.receipt ∧
      receiptView.event actual.transition.append.receipt =
        formal.history.event ∧
      receiptView.parentHead actual.transition.append.receipt =
        proposal.expectedParent ∧
      receiptView.successorHead actual.transition.append.receipt =
        historyRuntime.actualHead actual.transition.append.postStore ∧
      receiptView.postStoreQ actual.transition.append.receipt =
        storeQ actual.transition.append.postStore :=
  actual.transition.headline

/-- The actual journal and post-store name the same occurrence/event pair. -/
theorem ActuallyGloballySettledAdmission.effect_history_same_occurrence
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal :
      GloballySettledAdmission linearizer version proposal}
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    (actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime) :
    effectRuntime.historyRecorded
        actual.journal formal.effect.occurrence ↔
      historyRuntime.actualContains
        actual.transition.append.postStore formal.history.event :=
  actual.effectHistoryCoherent.recordedIff

/-- The formal settlement also excludes an actual world/history split. -/
theorem ActuallyGloballySettledAdmission.no_actual_applied_unrecorded
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version Store AppendReceipt StoreQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    {formal :
      GloballySettledAdmission linearizer version proposal}
    {historyRuntime :
      CanonicalHistoryRuntime EventQ Head Store AppendReceipt}
    {receiptView : AppendReceiptView EventQ Head StoreQ AppendReceipt}
    {storeQ : Store → StoreQ}
    {effectRuntime :
      EffectObservationRuntime
        Epoch Head EffectSlot Generation Occurrence FailureName}
    (actual :
      ActuallyGloballySettledAdmission
        formal historyRuntime receiptView storeQ effectRuntime) :
    ¬ (effectRuntime.worldApplied actual.world formal.effect.occurrence ∧
        ¬ effectRuntime.historyRecorded
          actual.journal formal.effect.occurrence) :=
  fenced_settlement_excludes_actual_applied_unrecorded
    formal.settled actual.effectBinding

/-! ## Minimal deletion witnesses -/

def unitJudgmentEquivalence : JudgmentEquivalence Unit where
  Equivalent := Eq
  refl := fun _ => rfl
  symm := Eq.symm
  trans := Eq.trans
  decide := fun left right => inferInstanceAs (Decidable (left = right))

def liarHistoryView : HistoryEventView Unit Unit Unit Unit Unit where
  preHead := fun _ => ()
  slot := fun _ => ()
  judgment := fun _ => ()
  occurrence := fun _ => ()

def liarHistorySnapshot : CanonicalHistorySnapshot Unit Unit where
  canonicalHead := ()
  contains := fun _ => true
  durableContains := fun _ => True
  containsSound := by
    intro _ _
    trivial

def unitProposal : Proposal Unit Unit Unit where
  slot := ()
  expectedParent := ()
  judgment := ()

def liarCanonicalRecord :
    CanonicalHistoryRecord
      unitJudgmentEquivalence liarHistoryView liarHistorySnapshot
      unitProposal () where
  event := ()
  recorded := rfl
  durablyRecorded := True.intro
  canonicalHeadBound := rfl
  preHeadBound := rfl
  slotBound := rfl
  judgmentBound := rfl
  occurrenceBound := rfl

def emptyActualHistory :
    CanonicalHistoryRuntime Unit Unit Unit Unit where
  actualHead := fun _ => ()
  actualContains := fun _ _ => False
  append := fun _ _ _ _ _ => False
  appendParent := by
    intro _ _ _ _ _ impossible
    exact False.elim impossible
  appendContains := by
    intro _ _ _ _ _ impossible
    exact False.elim impossible

/-- Abstract durable membership cannot refine an actually empty store. -/
theorem liar_history_snapshot_has_no_actual_binding :
    ¬ Nonempty
      (CanonicalHistoryRuntimeBinding
        emptyActualHistory liarHistorySnapshot ()) := by
  rintro ⟨binding⟩
  exact
    binding.durableSound liarCanonicalRecord.event
      liarCanonicalRecord.durablyRecorded

inductive DemoFailure
  | failed
  deriving DecidableEq

def liarEffect : ExternalEffect Unit Unit Unit where
  occurrence := ()
  expectedParent := ()
  effectSlot := ()

def liarReceipt :
    EffectReceipt Unit Unit Unit Unit Unit DemoFailure where
  occurrence := ()
  fence := {
    epoch := ()
    head := ()
    effectSlot := ()
    generation := ()
  }
  phase := .recorded

def liarObservation :
    EffectObservation Unit Unit Unit Unit Unit DemoFailure where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some liarReceipt

def liarEffectSnapshot :
    EffectSnapshot Unit Unit Unit Unit Unit DemoFailure where
  epoch := ()
  head := ()
  currentGeneration := fun _ => ()
  policyTerminalFailure := fun _ => False
  externalEffects := [liarEffect]
  observe := fun _ => some liarObservation

def liarFencedSettlement :
    FencedSettledReceipt
      liarEffectSnapshot liarEffect liarObservation liarReceipt where
  observed := rfl
  receiptPresent := rfl
  epochBound := rfl
  expectedParentBound := rfl
  canonicalHeadBound := rfl
  slotBound := rfl
  generationBound := rfl
  occurrenceBound := rfl
  coherent := by
    simp [SettlementCoherent, liarReceipt, liarObservation]

def emptyActualEffect :
    EffectObservationRuntime Unit Unit Unit Unit Unit DemoFailure where
  World := Unit
  Journal := Unit
  worldApplied := fun _ _ => False
  historyRecorded := fun _ _ => False
  compensationApplied := fun _ _ => False
  receiptAt := fun _ _ => none

/-- A liar observation can settle abstractly but has no actual-world binding. -/
theorem liar_effect_observation_has_no_actual_binding :
    ¬ Nonempty
      (EffectObservationBinding
        emptyActualEffect () () liarEffect.occurrence liarObservation) := by
  rintro ⟨binding⟩
  exact binding.worldAppliedExact.1 rfl

end Residua.RCC.RuntimeAdmissionBinding

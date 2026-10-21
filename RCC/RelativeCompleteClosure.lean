import RCC.FormalCore
import RCC.GoalAdequacy
import RCC.FacetCoherence
import RCC.SupportClosure
import RCC.EvidenceReplayability
import RCC.FinalizedHeadWindow
import RCC.EffectSettlement
import RCC.PrimitiveOperationalTotality
import RCC.MetaFailureExhaustion
import RCC.ClosurePrerequisites
import RCC.ClosureExhaustion
import RCC.IntentSnapshotBinding
import RCC.PrimitiveInvocationCoverage
import RCC.ProofCarryingOutcome
import RCC.Reepoch
import RCC.WakeContract

/-!
# RCC RC-1 — Relative complete closure

This capstone does not accept caller-supplied `closed`, `globalClosed`, or
`allDone` propositions.  A closed state is exactly one for which the executable
packet deriver returns a product of the existing strong RCC certificates at
one FC-1 snapshot/carrier.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RelativeCompleteClosure

open Residua.RCC
open Residua.RCC.FacetSnapshot
open Residua.RCC.FacetCoherence
open Residua.RCC.SupportClosure
open Residua.RCC.EvidenceReplayability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.EffectSettlement
open Residua.RCC.MetaFailureExhaustion
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.ClosureExhaustion
open Residua.RCC.IntentSnapshotBinding
open Residua.RCC.PrimitiveInvocationCoverage
open Residua.RCC.ProofCarryingOutcome

universe u

/-! ## One state-indexed FC-1 carrier -/

structure ClosureContext (State : Type u) where
  Epoch : Type u
  HistoryHead : Type u
  [historyHeadDecidableEq : DecidableEq HistoryHead]
  AssumptionRoot : Type u
  AddressRegistry : Type u
  SourceAuthority : Type u
  Watermark : Type u
  Partition : Type u
  FailureModel : Type u
  ProposalWindow : Type u
  ImplementationBundle : Type u
  sealSpec :
    SnapshotSeal
      Epoch HistoryHead AssumptionRoot AddressRegistry
        (FinalizedSourceWindow SourceAuthority Watermark Partition) FailureModel
        ProposalWindow ImplementationBundle
  projection :
    CarrierProjection
      State Epoch HistoryHead AssumptionRoot AddressRegistry
        (FinalizedSourceWindow SourceAuthority Watermark Partition)
        FailureModel ProposalWindow ImplementationBundle
  snapshotAt : State → SealedSnapshot sealSpec
  carrierAt :
    (state : State) →
      SnapshotCarrier projection (snapshotAt state)
  carrierValueBound :
    ∀ state, (carrierAt state).value = state
  Payload : RCCFacet → Type u
  bundleAt :
    (state : State) →
      CoherentFacetBundle Payload (snapshotAt state) (carrierAt state)
  adapter : FacetSemanticAdapter State Payload
  facetCertificateAt :
    (state : State) →
      FacetCoherenceCertificate (bundleAt state) adapter
  formalStateAt :
    (basis current : State) →
      (adapter.index.world basis).State
  advanceEvidenceAt :
    (basis current next : State) →
      (adapter.index.world basis).Evidence
  advanceEventAt :
    (basis current next : State) →
      (adapter.index.world basis).AdmittedEvent
  supportSystem : SupportSystem State ImplementationBundle
  replaySystemAt :
    (state : State) →
      ReplaySystem (snapshotAt state) (carrierAt state)
  IntentAddress : Type u
  intentRegistry :
    IntentRegistryKernel AddressRegistry IntentAddress
  intentObservation :
    IntentObservationKernel
      State AddressRegistry IntentAddress intentRegistry
  intentGoalMapAt :
    (state : State) →
      GoalJudgmentMap
        (intentRegistry.profile
          (currentIntentSpec intentRegistry (snapshotAt state)))
        (replaySystemAt state).Judgment
  intentSupportMapAt :
    (state : State) →
      SupportJudgmentMap
        (replaySystemAt state).Judgment supportSystem.Judgment
  primitiveImplementation :
    PrimitiveImplementationProjection ImplementationBundle
  PrimitiveInvocation : Type u
  primitiveInvocationDecidableEq :
    DecidableEq PrimitiveInvocation
  primitiveInScopeAt :
    State → PrimitiveInvocation → Prop
  primitiveInvocationsAt :
    State → List PrimitiveInvocation
  primitiveLawfulAt :
    ∀ state,
      LawfulPrimitiveFamily
        (primitiveImplementation.policy
          (projection.implementationBundle (carrierAt state).value))
        (primitiveImplementation.family
          (projection.implementationBundle (carrierAt state).value))
  primitiveActualAt :
    (state : State) → PrimitiveInvocation →
      ActualPrimitiveInvocation
        (primitiveImplementation.family
          (projection.implementationBundle (carrierAt state).value))
  primitiveRuntimeBeforeAt :
    (state : State) → PrimitiveInvocation →
      (adapter.index.world state).RuntimeState
  primitiveRuntimeAfterAt :
    (state : State) → PrimitiveInvocation →
      (adapter.index.world state).RuntimeState
  PrimitiveMeasurementReceipt : Type u
  primitiveMeasuredReceiptAt :
    State → PrimitiveInvocation → Option PrimitiveMeasurementReceipt
  primitiveMeasurementBindsAt :
    State → PrimitiveInvocation → PrimitiveMeasurementReceipt → Prop
  ReepochGoal : Type u
  ReepochOccurrence : Type u
  ReepochSemanticValue : Type u
  ReepochGoalOrigin : Type u
  reepochSemanticValue :
    Epoch → EpochSemanticSlot → ReepochSemanticValue
  reepochParentEpoch : Epoch → Option Epoch
  reepochGoalOrigin : ReepochGoal → ReepochGoalOrigin
  reepochGoalSatisfied : Epoch → ReepochGoal → Prop
  reepochNonterminal : Epoch → ReepochGoal → Prop
  reepochTerminalAtMigration : Epoch → ReepochGoal → Prop
  reepochTriggerOccurrence : Epoch → Option ReepochOccurrence
  reepochMigrationForOccurrence :
    ReepochOccurrence → Option (Epoch × Epoch)
  reepochNewObservationAdmitted :
    Epoch → ReepochOccurrence → Prop
  reepochPolicyDecisionAdmitted :
    Epoch → ReepochOccurrence → Prop
  reepochKernelReplacementAdmitted :
    Epoch → ReepochOccurrence → Prop
  reepochStableObstructionAdmitted :
    Epoch → ReepochOccurrence → Prop
  reepochMeasure : Epoch → Nat
  EffectSlot : Type u
  Generation : Type u
  Occurrence : Type u
  FailureName : Type u
  effectSnapshotAt :
    State →
      EffectSnapshot
        Epoch HistoryHead EffectSlot Generation Occurrence FailureName
  EffectInScopeAt :
    State →
      ExternalEffect Occurrence HistoryHead EffectSlot →
      Prop
  failureSemantics : MetaFailureSemantics
  failureSnapshotOf : HistoryHead → failureSemantics.Snapshot
  failureModelOf : FailureModel → failureSemantics.FailureModel
  failureSnapshotFaithful :
    ∀ left right,
      failureSnapshotOf left = failureSnapshotOf right → left = right
  failureModelFaithful :
    ∀ left right,
      failureModelOf left = failureModelOf right → left = right
  closureSystem : ClosureStateSystem
  closureStateAt : State → closureSystem.State
  intentClosureGoalForAt :
    (state : State) →
      (intentRegistry.profile
        (currentIntentSpec intentRegistry (snapshotAt state))).Goal →
      closureSystem.Goal
  intentClosureGoalInjectiveAt :
    ∀ state {left right},
      intentClosureGoalForAt state left =
          intentClosureGoalForAt state right →
        left = right
  intentClosureGoalLiveExactAt :
    ∀ state closureGoal,
      closureSystem.liveGoalAt (closureStateAt state) closureGoal ↔
        ∃ goal,
          goal ∈
              (intentRegistry.profile
                (currentIntentSpec intentRegistry
                  (snapshotAt state))).mandatoryGoals ∧
            intentClosureGoalForAt state goal = closureGoal
  failureTerminalSystem :
    FailureTerminalSystem closureSystem.State failureSemantics
  failureContextExact :
    ∀ state,
      failureTerminalSystem.contextAt (closureStateAt state) =
        { snapshot :=
            failureSnapshotOf
              (snapshotAt state).coordinates.historyHead
          failureModel :=
            failureModelOf
              (snapshotAt state).coordinates.failureModel }
  failureWindowAt :
    (state : State) →
      AdmittedFailureWindow failureSemantics
        (failureTerminalSystem.contextAt (closureStateAt state))

def ClosureContext.failureContextAt
    (C : ClosureContext State)
    (state : State) :
    FailureContext C.failureSemantics.Snapshot
      C.failureSemantics.FailureModel where
  snapshot :=
    C.failureSnapshotOf (C.snapshotAt state).coordinates.historyHead
  failureModel :=
    C.failureModelOf (C.snapshotAt state).coordinates.failureModel

/--
The primitive system used by RC-1 is definitionally the context's projected
implementation family and FC-2 world at the current RCC state.  A packet
cannot substitute a detached benign system.
-/
def ClosureContext.primitiveSystem
    (C : ClosureContext State) :
    PrimitiveInvocationSystem where
  Snapshot := State
  Invocation := C.PrimitiveInvocation
  invocationDecidableEq := C.primitiveInvocationDecidableEq
  inScopeAt := C.primitiveInScopeAt
  invocationsAt := C.primitiveInvocationsAt
  policyAt := fun state =>
    C.primitiveImplementation.policy
      (C.projection.implementationBundle (C.carrierAt state).value)
  familyAt := fun state =>
    C.primitiveImplementation.family
      (C.projection.implementationBundle (C.carrierAt state).value)
  lawfulAt := C.primitiveLawfulAt
  actualAt := C.primitiveActualAt
  worldAt := fun state => C.adapter.index.world state
  runtimeBeforeAt := C.primitiveRuntimeBeforeAt
  runtimeAfterAt := C.primitiveRuntimeAfterAt
  MeasurementReceipt := C.PrimitiveMeasurementReceipt
  measuredReceiptAt := C.primitiveMeasuredReceiptAt
  MeasurementBindsAt := C.primitiveMeasurementBindsAt

/--
The migration system is fixed by the closure context and definitionally uses
the same epoch type as the FC-1 snapshot.  A branch packet cannot substitute a
detached epoch universe.
-/
def ClosureContext.reepochSystem
    (C : ClosureContext State) :
    ReepochSystem where
  Epoch := C.Epoch
  Goal := C.ReepochGoal
  Occurrence := C.ReepochOccurrence
  SemanticValue := C.ReepochSemanticValue
  GoalOrigin := C.ReepochGoalOrigin
  semanticValue := C.reepochSemanticValue
  parentEpoch := C.reepochParentEpoch
  goalOrigin := C.reepochGoalOrigin
  goalSatisfied := C.reepochGoalSatisfied
  nonterminal := C.reepochNonterminal
  terminalAtMigration := C.reepochTerminalAtMigration
  triggerOccurrence := C.reepochTriggerOccurrence
  migrationForOccurrence := C.reepochMigrationForOccurrence
  newObservationAdmitted := C.reepochNewObservationAdmitted
  policyDecisionAdmitted := C.reepochPolicyDecisionAdmitted
  kernelReplacementAdmitted := C.reepochKernelReplacementAdmitted
  stableObstructionAdmitted := C.reepochStableObstructionAdmitted
  epochMeasure := C.reepochMeasure

/-- Existential RCC-45 parameters, with the actual strong prerequisite. -/
structure FinalizedPrerequisiteAt
    (C : ClosureContext State)
    (state : State) where
  Slot : Type u
  Judgment : Type u
  EventQ : Type u
  Config : Type u
  AuthorityEvidence :
    Proposal Slot C.HistoryHead Judgment → Type u
  [headDecidableEq : DecidableEq C.HistoryHead]
  [generationDecidableEq : DecidableEq C.Generation]
  environment :
    AdmissionEnvironment
      Slot C.HistoryHead Judgment AuthorityEvidence C.Generation C.Epoch
        C.EffectSlot C.Occurrence C.FailureName EventQ
  history :
    FinalizedHistoryView EventQ Slot C.HistoryHead Config
  ConfigLawful : Config → Prop
  protocol :
    SourceWindowProtocol
      C.SourceAuthority C.Watermark C.Partition C.HistoryHead Config
  ConfigStable : Config → Prop
  closed :
    FinalizedClosureAt
      (environment := environment)
      (history := history)
      (ConfigLawful := ConfigLawful)
      (protocol := protocol)
      (ConfigStable := ConfigStable)
      (C.snapshotAt state)
  effectSnapshotExact :
    environment.effectSnapshot = C.effectSnapshotAt state
  finalizedEpoch : C.Epoch
  finalizedHead : C.HistoryHead
  finalizedWindow :
    FinalizedSourceWindow C.SourceAuthority C.Watermark C.Partition
  epochFromEvidence :
    environment.effectSnapshot.epoch = finalizedEpoch
  headFromEvidence :
    closed.evidence.snapshot.head = finalizedHead
  windowFromEvidence :
    finalizedSourceWindow closed.evidence = finalizedWindow
  epochExact :
    finalizedEpoch = (C.snapshotAt state).coordinates.epoch
  headExact :
    finalizedHead = (C.snapshotAt state).coordinates.historyHead
  windowExact :
    finalizedWindow = (C.snapshotAt state).coordinates.sourceWindow

/-! ## Exact-snapshot intent and primitive prerequisites -/

/--
The mandatory Goal, replay judgment, and support root are one exact
snapshot-indexed chain.  The intent specification is selected by the admitted
address registry; callers do not provide an `IntentSatisfied` proposition.
-/
structure IntentSnapshotPrerequisiteAt
    (C : ClosureContext State)
    (state : State) where
  closed :
    DerivedIntentClosureAt C.intentRegistry C.intentObservation
      (C.snapshotAt state) (C.carrierAt state)
  replayAssociation :
    ReplayGoalAssociation closed (C.replaySystemAt state)
      (C.intentGoalMapAt state)
  supportAssociation :
    SupportGoalAssociation closed (C.replaySystemAt state)
      (C.intentGoalMapAt state) C.supportSystem
      (C.intentSupportMapAt state)
  lifecycleTerminalExact :
    ∀ goal,
      goal ∈
          (C.intentRegistry.profile
            (currentIntentSpec C.intentRegistry
              (C.snapshotAt state))).mandatoryGoals →
        C.closureSystem.TerminalAt
            (C.closureStateAt state)
            (C.intentClosureGoalForAt state goal) ↔
          ((C.intentRegistry.profile
              (currentIntentSpec C.intentRegistry
                (C.snapshotAt state))).contract goal).verify
            (C.intentObservation.observe
              (currentIntentSpec C.intentRegistry
                (C.snapshotAt state))
              goal (C.carrierAt state).value)
            (closed.certificate goal) = true

/--
Every actual primitive invocation is covered by the context's definitionally
bound implementation family and FC-2 world at this exact RCC state.
-/
structure PrimitiveInvocationPrerequisiteAt
    (C : ClosureContext State)
    (state : State) where
  evidence : InvocationEvidenceWindowAt C.primitiveSystem state
  exhaustive :
    ExhaustiveInvocationCoverageAt C.primitiveSystem state evidence

/-! ## Strong global packet -/

structure GlobalEpochClosedPacket
    {State : Type u}
    (C : ClosureContext State)
    (state : State) where
  finalizedSourceHead :
    FinalizedPrerequisiteAt C state
  intentSnapshot :
    IntentSnapshotPrerequisiteAt C state
  effectSettlement :
    EffectSettlementAt
      (C.snapshotAt state) (C.effectSnapshotAt state)
        (C.EffectInScopeAt state)
  primitiveInvocations :
    PrimitiveInvocationPrerequisiteAt C state
  closureExhaustion :
    ClosureExhaustionAt C.closureSystem C.failureSemantics
      C.failureTerminalSystem (C.closureStateAt state)
  failureWindowExact :
    closureExhaustion.failureWindow.admitted = C.failureWindowAt state

def GlobalEpochClosed
    {State : Type u}
    (C : ClosureContext State)
    (state : State) : Prop :=
  Nonempty (GlobalEpochClosedPacket C state)

/-! ## Packet headlines -/

theorem packet_intent_satisfied
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    DerivedIntentSatisfied
      C.intentRegistry
      C.intentObservation
      (C.snapshotAt state) (C.carrierAt state) :=
  ⟨packet.intentSnapshot.closed⟩

/--
The three goal surfaces are semantically connected, not merely list-equal:
closed transitive support entails replay acceptance, and replay acceptance
entails the exact mandatory intent claim.
-/
theorem packet_support_replay_closes_mandatory_goal
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state)
    (goal :
      (C.intentRegistry.profile
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state))).Goal)
    (mandatory :
      goal ∈
        (C.intentRegistry.profile
          (currentIntentSpec C.intentRegistry
            (C.snapshotAt state))).mandatoryGoals) :
    ((C.intentRegistry.profile
      (currentIntentSpec C.intentRegistry
        (C.snapshotAt state))).contract goal).claim
      (C.intentObservation.observe
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state)) goal (C.carrierAt state).value) :=
  packet.intentSnapshot.closed.mandatoryClaim goal mandatory

/-- Replay executes the exact accepted mandatory Goal certificate. -/
theorem packet_mandatory_replay_accepted
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state)
    (goal :
      (C.intentRegistry.profile
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state))).Goal)
    (mandatory :
      goal ∈
        (C.intentRegistry.profile
          (currentIntentSpec C.intentRegistry
            (C.snapshotAt state))).mandatoryGoals) :
    (C.replaySystemAt state).verifyReplay
        ((C.intentGoalMapAt state).judgmentFor goal)
        ((C.replaySystemAt state).receiptFor
          ((C.intentGoalMapAt state).judgmentFor goal)) = true :=
  packet.intentSnapshot.replayAssociation.mandatoryReplayAccepted
    goal mandatory

/-- The exact mandatory Goal certificate is retained at its checked support root. -/
theorem packet_mandatory_support_root
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state)
    (goal :
      (C.intentRegistry.profile
        (currentIntentSpec C.intentRegistry
          (C.snapshotAt state))).Goal)
    (mandatory :
      goal ∈
        (C.intentRegistry.profile
          (currentIntentSpec C.intentRegistry
            (C.snapshotAt state))).mandatoryGoals) :
    C.supportSystem.RootClaim
        (C.carrierAt state).value
        (packet.intentSnapshot.supportAssociation.rootFor goal)
        (packet.intentSnapshot.supportAssociation.encodeRootCertificate {
          goal := goal
          certificate := packet.intentSnapshot.closed.certificate goal
        }) :=
  packet.intentSnapshot.supportAssociation.mandatoryRootClaim goal mandatory

theorem packet_effects_settled
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    EpochEffectClosed (C.effectSnapshotAt state) :=
  packet.effectSettlement.closed

/--
The source/finality admission environment and the settlement checker consume
the identical effect snapshot.  Epoch/head agreement alone is insufficient:
the generation policy, external-effect universe, and observation function are
all part of this structure equality.
-/
theorem packet_effect_snapshot_exact
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    packet.finalizedSourceHead.environment.effectSnapshot =
      C.effectSnapshotAt state :=
  packet.finalizedSourceHead.effectSnapshotExact

theorem packet_meta_quiescent
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    deriveActiveGoals C.closureSystem (C.closureStateAt state) = [] ∧
      deriveActiveFailures C.failureTerminalSystem
          (C.closureStateAt state)
          packet.closureExhaustion.failureWindow = [] ∧
      derivePendingMigrations C.closureSystem
          (C.closureStateAt state) = [] :=
  ⟨packet.closureExhaustion.activeGoalsEmpty,
    packet.closureExhaustion.activeFailuresEmpty,
    packet.closureExhaustion.pendingMigrationsEmpty⟩

theorem packet_meta_failures_terminal
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    ∀ failure,
      (C.failureSemantics.coverage.modelAt
        (C.failureContextAt state)).mandatory failure →
      ∃ facts classification certificate,
        packet.closureExhaustion.failureWindow.admitted.factsAt failure =
            some facts ∧
          deriveFailureClass facts = .classified classification ∧
          C.failureTerminalSystem.terminalCertificateAt
              (C.closureStateAt state) failure classification.tag =
            some certificate ∧
          C.failureTerminalSystem.receiptName certificate.receipt ≠ "" ∧
          C.failureTerminalSystem.receiptContext certificate.receipt =
              C.failureTerminalSystem.contextAt
                (C.closureStateAt state) ∧
          C.failureTerminalSystem.receiptFailure certificate.receipt =
              failure ∧
          C.failureTerminalSystem.receiptClass certificate.receipt =
              classification.tag ∧
          C.failureTerminalSystem.receiptKind certificate.receipt =
              certificate.terminalKind := by
  intro failure mandatory
  apply packet.closureExhaustion.mandatoryFailureTerminal
  rw [C.failureContextExact state]
  exact mandatory

theorem active_goal_excludes_closed
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    {goal : C.closureSystem.Goal}
    (member :
      goal ∈
        deriveActiveGoals C.closureSystem (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state := by
  rintro ⟨packet⟩
  rw [packet.closureExhaustion.activeGoalsEmpty] at member
  cases member

theorem pending_migration_excludes_closed
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    {migration : C.closureSystem.Migration}
    (member :
      migration ∈
        derivePendingMigrations C.closureSystem
          (C.closureStateAt state)) :
    ¬ GlobalEpochClosed C state := by
  rintro ⟨packet⟩
  rw [packet.closureExhaustion.pendingMigrationsEmpty] at member
  cases member

theorem packet_excludes_unsettled_effects
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    ∀ effect, C.EffectInScopeAt state effect →
      ∃ observation receipt,
        (C.effectSnapshotAt state).observe effect.occurrence =
            some observation ∧
          observation.receipt = some receipt ∧
          ¬ EffectAppliedUnrecorded observation ∧
          ¬ EffectRecordedNotApplied observation receipt ∧
          ¬ CompensationStillPending receipt := by
  intro effect inScope
  exact
    packet.effectSettlement.excludes_unsettled effect
      (packet.effectSettlement.coverage.complete effect inScope)

theorem context_fc2_runtime_address
    {State : Type u}
    {C : ClosureContext State}
    (state : State) :
    AddressReductionLaw (C.adapter.index.world state) ∧
      RuntimeRefinementLaw (C.adapter.index.world state) :=
  by
    rw [← C.carrierValueBound state]
    exact
      ⟨(C.facetCertificateAt state).addressReduction,
        (C.facetCertificateAt state).runtimeRefinement⟩

theorem packet_finalized_source_head_exact
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    packet.finalizedSourceHead.finalizedEpoch =
        (C.snapshotAt state).coordinates.epoch ∧
      packet.finalizedSourceHead.finalizedHead =
        (C.snapshotAt state).coordinates.historyHead ∧
      packet.finalizedSourceHead.finalizedWindow =
        (C.snapshotAt state).coordinates.sourceWindow :=
  ⟨packet.finalizedSourceHead.epochExact,
    packet.finalizedSourceHead.headExact,
    packet.finalizedSourceHead.windowExact⟩

theorem packet_effect_universe_exact_and_settled
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    ∀ effect,
      C.EffectInScopeAt state effect ↔
        effect ∈ (C.effectSnapshotAt state).externalEffects ∧
          ∃ observation receipt,
            FencedSettledReceipt
              (C.effectSnapshotAt state) effect observation receipt := by
  intro effect
  constructor
  · intro inScope
    have member :=
      packet.effectSettlement.coverage.complete effect inScope
    exact
      ⟨member,
        packet.effectSettlement.every_effect_settled effect member⟩
  · rintro ⟨declared, _⟩
    exact packet.effectSettlement.coverage.sound effect declared

theorem packet_actual_primitive_refines_family
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state)
    (invocation : C.PrimitiveInvocation)
    (inScope :
      C.primitiveInScopeAt state invocation) :
    ∃ refinement :
        ActualInvocationRefinementAt
          (C.primitiveSystem.familyAt state),
      refinement.invocation =
          C.primitiveSystem.actualAt state invocation ∧
        InvocationReturned refinement.invocation ∧
        (C.primitiveSystem.worldAt state).runtimeStep
            (C.primitiveSystem.runtimeBeforeAt state invocation)
            (C.primitiveSystem.runtimeAfterAt state invocation) ∧
        Nonempty
          (FormalOrMeasuredAt C.primitiveSystem state invocation) :=
  ExhaustiveInvocationCoverageAt.all_total_refined_runtime_bound
    packet.primitiveInvocations.exhaustive invocation inScope

theorem packet_failure_classified_and_terminal
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    ∀ failure,
      (C.failureSemantics.coverage.modelAt
        (C.failureContextAt state)).mandatory failure →
      ∃ facts classification certificate,
        packet.closureExhaustion.failureWindow.admitted.factsAt failure =
            some facts ∧
          deriveFailureClass facts = .classified classification ∧
          C.failureTerminalSystem.terminalCertificateAt
              (C.closureStateAt state) failure classification.tag =
            some certificate ∧
          C.failureTerminalSystem.receiptName certificate.receipt ≠ "" ∧
          C.failureTerminalSystem.receiptContext certificate.receipt =
              C.failureTerminalSystem.contextAt
                (C.closureStateAt state) ∧
          C.failureTerminalSystem.receiptFailure certificate.receipt =
              failure ∧
          C.failureTerminalSystem.receiptClass certificate.receipt =
              classification.tag ∧
          C.failureTerminalSystem.receiptKind certificate.receipt =
              certificate.terminalKind :=
  packet_meta_failures_terminal packet

/-- Closed headline projected from the concrete certificate product. -/
structure ClosedHeadline
    {State : Type u}
    (C : ClosureContext State)
    (state : State) where
  packet :
    GlobalEpochClosedPacket C state
  intentSatisfied :
    DerivedIntentSatisfied
      C.intentRegistry
      C.intentObservation
      (C.snapshotAt state) (C.carrierAt state)
  effectsSettled :
    EpochEffectClosed (C.effectSnapshotAt state)
  goalsQuiescent :
    deriveActiveGoals C.closureSystem (C.closureStateAt state) = []
  failuresQuiescent :
    deriveActiveFailures C.failureTerminalSystem
        (C.closureStateAt state)
        packet.closureExhaustion.failureWindow = []
  migrationsQuiescent :
    derivePendingMigrations C.closureSystem
        (C.closureStateAt state) = []
  addressReduction :
    AddressReductionLaw (C.adapter.index.world state)
  runtimeRefinement :
    RuntimeRefinementLaw (C.adapter.index.world state)

def GlobalEpochClosedPacket.headline
    {State : Type u}
    {C : ClosureContext State}
    {state : State}
    (packet : GlobalEpochClosedPacket C state) :
    ClosedHeadline C state where
  packet := packet
  intentSatisfied := packet_intent_satisfied packet
  effectsSettled := packet_effects_settled packet
  goalsQuiescent := packet.closureExhaustion.activeGoalsEmpty
  failuresQuiescent := packet.closureExhaustion.activeFailuresEmpty
  migrationsQuiescent := packet.closureExhaustion.pendingMigrationsEmpty
  addressReduction := (context_fc2_runtime_address state).1
  runtimeRefinement := (context_fc2_runtime_address state).2

/-! ## Proof-carrying normalization and CoreObject bridge -/

/-- One same-epoch transition, bound to FC-2 reduction and admission. -/
structure RC1AdvancePacket
    (C : ClosureContext State)
    (before after : State) : Type u where
  reduces :
    (C.adapter.index.world before).reduces
      (C.formalStateAt before before)
      (C.formalStateAt before after)
  admitted :
    (C.adapter.index.world before).admits
      (C.advanceEvidenceAt before before after)
      (C.advanceEventAt before before after)

/-- Await carries the exact wake contract and its certificate. -/
abbrev RC1WakePacket
    (W : WakeSystem)
    (state : W.State) :=
  PSigma fun contract : WakeContract W state =>
    AwaitCertificate W state contract

/-- Reepoch carries a real RCC-23 certificate from the current snapshot epoch. -/
structure RC1MigrationPacket
    (C : ClosureContext State)
    (state : State) where
  successor : C.Epoch
  certificate :
    ReepochCert C.reepochSystem
      (C.snapshotAt state).coordinates.epoch successor

/--
The exact refusal packet read from the context's one admitted failure window.
Unlike an exhaustive window, this packet may honestly contain ambiguous or
incomplete evidence.
-/
structure CurrentFailureRefusalAt
    (C : ClosureContext State)
    (state : State) where
  failure : C.failureSemantics.Failure
  facts :
    FailureFacts C.failureSemantics
      (C.failureTerminalSystem.contextAt
        (C.closureStateAt state)) failure
  residue : MetaFailureResidue
  found :
    (C.failureWindowAt state).factsAt failure = some facts
  refused : deriveFailureClass facts = .refuse residue

theorem CurrentFailureRefusalAt.inScope
    {C : ClosureContext State}
    {state : State}
    (refusal : CurrentFailureRefusalAt C state) :
    (C.failureSemantics.coverage.modelAt
      (C.failureTerminalSystem.contextAt
        (C.closureStateAt state))).inScope refusal.failure :=
  ((C.failureWindowAt state).packetSound
    refusal.failure refusal.facts refusal.found).1

theorem CurrentFailureRefusalAt.admitted
    {C : ClosureContext State}
    {state : State}
    (refusal : CurrentFailureRefusalAt C state) :
    C.failureSemantics.AdmittedAt
      (C.failureTerminalSystem.contextAt
        (C.closureStateAt state)) refusal.failure :=
  ((C.failureWindowAt state).packetSound
    refusal.failure refusal.facts refusal.found).2

/--
The fatal remainder is a typed failure already present in the mechanically
derived Goal/failure semantics.  There is no String, Unit, or caller Boolean
constructor.
-/
inductive RC1FatalCause
    (C : ClosureContext State)
    (state : State) where
  | goalEvidenceRefused
      (goal : C.closureSystem.Goal)
      (live :
        C.closureSystem.liveGoalAt (C.closureStateAt state) goal)
      (residue : DispositionResidue)
      (refused :
        deriveGoalDisposition
            (C.closureSystem.workflowFactsAt
              (C.closureStateAt state) goal) =
          .refuse residue)
  | failureEvidenceRefused
      (refusal : CurrentFailureRefusalAt C state)
  | primitiveResourceExhausted
      (invocation : C.PrimitiveInvocation)
      (inScope : C.primitiveInScopeAt state invocation)
      (residue :
        (C.primitiveSystem.familyAt state).Residue)
      (exhausted :
        (C.primitiveActualAt state invocation).result =
          .ResourceExhausted residue)

/--
A fatal failure refusal is not caller-supplied evidence.  It is the exact
in-scope packet found by the context's current admitted failure window.
-/
theorem RC1FatalCause.failureRefusalBoundToCurrentWindow
    {C : ClosureContext State}
    {state : State}
    (fatal : RC1FatalCause C state) :
    match fatal with
    | .failureEvidenceRefused refusal =>
        (C.failureSemantics.coverage.modelAt
            (C.failureTerminalSystem.contextAt
              (C.closureStateAt state))).inScope refusal.failure ∧
          C.failureSemantics.AdmittedAt
            (C.failureTerminalSystem.contextAt
              (C.closureStateAt state)) refusal.failure ∧
          (C.failureWindowAt state).factsAt refusal.failure =
            some refusal.facts ∧
          deriveFailureClass refusal.facts = .refuse refusal.residue
    | _ => True := by
  cases fatal with
  | goalEvidenceRefused => trivial
  | failureEvidenceRefused refusal =>
      exact
        ⟨refusal.inScope, refusal.admitted,
          refusal.found, refusal.refused⟩
  | primitiveResourceExhausted => trivial

/--
The same admitted failure window cannot both contain a refused in-scope packet
and support RC-1 closure exhaustion.
-/
theorem CurrentFailureRefusalAt.excludesClosed
    {C : ClosureContext State}
    {state : State}
    (refusal : CurrentFailureRefusalAt C state) :
    ¬ GlobalEpochClosed C state := by
  rintro ⟨packet⟩
  exact
    refused_packet_cannot_inhabit_exhaustive_window
      (C.failureWindowAt state)
      refusal.failure refusal.inScope refusal.facts refusal.found
      refusal.residue refusal.refused
      ⟨packet.closureExhaustion.failureWindow,
        packet.failureWindowExact⟩

/-- RC-1-local successor carrier; converted to PCO at the adapter boundary. -/
structure RC1CertifiedAdvance
    (C : ClosureContext State)
    (measure : State → Nat)
    (state : State) where
  next : State
  certificate : RC1AdvancePacket C state next
  decreases : measure next < measure state

/--
Only evidence readers vary by executable instance.  Their packet families are
fixed here to the strong RCC domains.
-/
structure RC1BranchKernel
    (W : WakeSystem)
    (C : ClosureContext W.State) where
  measure : W.State → Nat
  closedAt :
    (state : W.State) → Option (GlobalEpochClosedPacket C state)
  advanceAt :
    (state : W.State) →
      Option (RC1CertifiedAdvance C measure state)
  wakeAt :
    (state : W.State) → Option (RC1WakePacket W state)
  migrationAt :
    (state : W.State) → Option (RC1MigrationPacket C state)
  haltAt :
    (state : W.State) → RC1FatalCause C state

def RC1BranchKernel.toBranchSystem
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C) :
    BranchSystem where
  State := W.State
  measure := K.measure
  ClosedPacket := GlobalEpochClosedPacket C
  AdvancePacket := RC1AdvancePacket C
  WakePacket := RC1WakePacket W
  MigrationPacket := RC1MigrationPacket C
  HaltPacket := RC1FatalCause C
  closedAt := K.closedAt
  advanceAt := fun state =>
    match K.advanceAt state with
    | none => none
    | some advance =>
        some {
          next := advance.next
          certificate := advance.certificate
          decreases := advance.decreases
        }
  wakeAt := K.wakeAt
  migrationAt := K.migrationAt
  haltAt := K.haltAt

/-- Exact readers prevent a lower-priority branch from hiding a continuation. -/
structure RC1Execution
    {W : WakeSystem}
    {C : ClosureContext W.State}
    (K : RC1BranchKernel W C) : Prop where
  readers : BranchReadersComplete K.toBranchSystem

/-- Every RC-1 advance has the resource delta required by FC-3. -/
def RC1AdvancePacket.resourceDelta
    {C : ClosureContext State}
    {before after : State}
    (packet : RC1AdvancePacket C before after) :
    ResourceDeltaCertificate
      (C.adapter.index.world before)
      (C.formalStateAt before before)
      (C.formalStateAt before after) := by
  let law :
      ReductionResourceLaw (C.adapter.index.world before) := by
    have exactLaw :=
      (C.facetCertificateAt before).reductionResource
    exact
      Eq.mp
        (congrArg ReductionResourceLaw
          (congrArg C.adapter.index.world
            (C.carrierValueBound before)))
        exactLaw
  exact law.deltaFor _ _ packet.reduces

/-- Every admitted RC-1 advance carries grounded evidence. -/
theorem RC1AdvancePacket.evidenceGrounded
    {C : ClosureContext State}
    {before after : State}
    (packet : RC1AdvancePacket C before after) :
    (C.adapter.index.world before).grounded
      (C.advanceEvidenceAt before before after) := by
  let law :
      EvidenceAdmissionLaw (C.adapter.index.world before) := by
    have exactLaw :=
      (C.facetCertificateAt before).evidenceAdmission
    exact
      Eq.mp
        (congrArg EvidenceAdmissionLaw
          (congrArg C.adapter.index.world
            (C.carrierValueBound before)))
        exactLaw
  exact law.admittedGrounded _ _ packet.admitted

/-- A selected Await excludes every hidden certified advance. -/
theorem rc1_await_excludes_hidden_advance
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    (state : W.State)
    (wake : RC1WakePacket W state)
    (selected :
      deriveOpen K.toBranchSystem state = .await wake) :
    ¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state) :=
  await_excludes_hidden_advance
    K.toBranchSystem execution.readers state wake selected

/-- A selected Reepoch excludes both hidden advance and wake packets. -/
theorem rc1_reepoch_excludes_hidden_higher_priority
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    (state : W.State)
    (migration : RC1MigrationPacket C state)
    (selected :
      deriveOpen K.toBranchSystem state = .reepoch migration) :
    (¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state)) ∧
      ¬ Nonempty (K.toBranchSystem.WakePacket state) :=
  reepoch_excludes_hidden_higher_priority
    K.toBranchSystem execution.readers state migration selected

/-- Halt is the exact typed remainder of all higher-priority readers. -/
theorem rc1_halt_excludes_hidden_continuation
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    (state : W.State)
    (failure : RC1FatalCause C state)
    (selected :
      deriveOpen K.toBranchSystem state = .halt failure) :
    (¬ Nonempty
        (CertifiedAdvance K.toBranchSystem.State
          K.toBranchSystem.measure K.toBranchSystem.AdvancePacket state)) ∧
      (¬ Nonempty (K.toBranchSystem.WakePacket state)) ∧
      ¬ Nonempty (K.toBranchSystem.MigrationPacket state) :=
  halt_excludes_hidden_continuation
    K.toBranchSystem execution.readers state failure selected

/-- The induced fixed points are exactly strong RC-1 packets. -/
theorem core_fixed_iff_packet
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K)
    (state : W.State) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).D state state ↔
      GlobalEpochClosed C state :=
  (ProofCarryingOutcome.core_exact
    K.toBranchSystem execution.readers.closed) state

/-- RCC's CoreObject bridge is exact, not merely single-valued. -/
theorem derived_core_exact
    {W : WakeSystem}
    {C : ClosureContext W.State}
    {K : RC1BranchKernel W C}
    (execution : RC1Execution K) :
    (ProofCarryingOutcome.coreObject K.toBranchSystem).Exact :=
  ProofCarryingOutcome.core_exact
    K.toBranchSystem execution.readers.closed

end Residua.RCC.RelativeCompleteClosure

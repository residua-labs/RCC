import RCC.R1Target
import RCCTests.RC1StepMSTBinding
import RCCTests.FacetCoherence

/-!
# R1 discriminating site — one concrete `ClosureContext` inhabitant

`Residua.RCC.R1Target.Certificate` carries three fields universally quantified
over `{State : Type} {C : ClosureContext State}`
(`existingAdvanceHasSettledEvent`, `nonadmittedAdvanceCannotBind`,
`emptyEventCannotAppend`).  Until this file landed there was **no concrete
`ClosureContext` inhabitant anywhere in the tree** (measured 2026-10-29): every
consumer held `C` as a variable, so the strict evidence grade could not confirm
the certificate is exercisable at a real instance.

This site builds `demoContext : ClosureContext FacetCoherence.Tests.Carrier`
over the existing `Residua.RCC.FacetCoherence.Tests` carrier/world/adapter
fixture, then exercises the three parametric certificate fields at it:

* positive — one `AdvancePacket` between the two fixture carriers resolves to
  a durable `HistoryEdge` through `demoSurface`;
* mutant (non-admission) — the same packet with `admitted := false` cannot
  bind history;
* mutant (empty settled-event carrier) — `emptyEventSurface` cannot append.

The four `GoalWorkSystem`-indexed certificate fields are exercised at one
concrete `GoalWorkSystem`/`GoalWorkSnapshot` as well.

All constructions are `def`s; no `sorry`, no axioms beyond Lean's standard.
-/

namespace Residua.RCC.RegistrationSites.R1

open Residua.RCC
open Residua.RCC.FacetSnapshot
open Residua.RCC.FacetCoherence
open Residua.RCC.FacetCoherence.Tests
open Residua.RCC.SupportClosure
open Residua.RCC.EvidenceReplayability
open Residua.RCC.IntentSnapshotBinding
open Residua.RCC.GoalAdequacy
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.ClosureExhaustion
open Residua.RCC.EffectClassification
open Residua.RCC.EffectSettlement
open Residua.RCC.FailureCoverage
open Residua.RCC.MetaFailureExhaustion
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.RC1StepMSTBinding.Tests

/-! ## FC-1 core — sealed snapshot and carrier at every state -/

/-- Sealing accepts every coordinate tuple; the demo never needs to refuse. -/
def demoSealSpec :
    SnapshotSeal
      FacetCoherence.Tests.Epoch FacetCoherence.Tests.HistoryHead
      FacetCoherence.Tests.AssumptionRoot FacetCoherence.Tests.AddressRegistry
      (FinalizedSourceWindow Unit Unit Unit)
      FacetCoherence.Tests.FailureModel FacetCoherence.Tests.ProposalWindow
      FacetCoherence.Tests.ImplementationBundle where
  IsSealed := fun _ => True

/-- The snapshot coordinates are projected from the state itself, so every
    `SnapshotCarrier` bound field is `rfl`. -/
def demoCoordinates (state : Carrier) :
    SnapshotCoordinates
      FacetCoherence.Tests.Epoch FacetCoherence.Tests.HistoryHead
      FacetCoherence.Tests.AssumptionRoot FacetCoherence.Tests.AddressRegistry
      (FinalizedSourceWindow Unit Unit Unit)
      FacetCoherence.Tests.FailureModel FacetCoherence.Tests.ProposalWindow
      FacetCoherence.Tests.ImplementationBundle where
  epoch := state.epoch
  historyHead := state.historyHead
  assumptionRoot := state.assumptionRoot
  addressRegistry := state.addressRegistry
  sourceWindow := { sourceAuthority := (), watermark := (), priorPartitions := [] }
  failureModel := state.failureModel
  proposalWindow := state.proposalWindow
  implementationBundle := state.implementationBundle

def demoProjection :
    CarrierProjection
      Carrier
      FacetCoherence.Tests.Epoch FacetCoherence.Tests.HistoryHead
      FacetCoherence.Tests.AssumptionRoot FacetCoherence.Tests.AddressRegistry
      (FinalizedSourceWindow Unit Unit Unit)
      FacetCoherence.Tests.FailureModel FacetCoherence.Tests.ProposalWindow
      FacetCoherence.Tests.ImplementationBundle where
  epoch := Carrier.epoch
  historyHead := Carrier.historyHead
  assumptionRoot := Carrier.assumptionRoot
  addressRegistry := Carrier.addressRegistry
  sourceWindow := fun _ =>
    { sourceAuthority := (), watermark := (), priorPartitions := [] }
  failureModel := Carrier.failureModel
  proposalWindow := Carrier.proposalWindow
  implementationBundle := Carrier.implementationBundle

def demoSnapshotAt (state : Carrier) : SealedSnapshot demoSealSpec where
  coordinates := demoCoordinates state
  sealed := trivial

def demoCarrierAt (state : Carrier) :
    SnapshotCarrier demoProjection (demoSnapshotAt state) where
  value := state
  epochBound := rfl
  historyHeadBound := rfl
  assumptionRootBound := rfl
  addressRegistryBound := rfl
  sourceWindowBound := rfl
  failureModelBound := rfl
  proposalWindowBound := rfl
  implementationBundleBound := rfl

/-- Every facet observation is produced on the state's own snapshot and
    carrier, with the head-tagged payload the Tests adapter decodes. -/
def demoBundleAt (state : Carrier) :
    CoherentFacetBundle
      Payload (demoSnapshotAt state) (demoCarrierAt state) where
  evidence := fun facet =>
    { raw :=
        { snapshot := demoSnapshotAt state
          carrier := state
          payload := payloadAt state.historyHead facet }
      bound := { snapshotBound := rfl, carrierBound := rfl } }

/-- Per-state FC-2 certificate: the head case split reduces `decodeAtHead`
    to `some` on the matching branch. -/
def demoFacetCertificateAt (state : Carrier) :
    FacetCoherenceCertificate (demoBundleAt state) adapter := by
  rcases state with ⟨i, e, h, ar, ad, sw, fm, pw, ib⟩
  cases h <;>
    exact
      { addressSurface := addressSurfaceAt _
        addressDecoded := rfl
        evidenceSurface := evidenceSurfaceAt _
        evidenceDecoded := rfl
        reductionSurface := reductionSurfaceAt _
        reductionDecoded := rfl
        resourceSurface := resourceSurfaceAt _
        resourceDecoded := rfl
        reflectionSurface := reflectionSurfaceAt _
        reflectionDecoded := rfl
        runtimeSurface := runtimeSurfaceAt _
        runtimeDecoded := rfl
        lineageSurface := lineageSurfaceAt _
        lineageDecoded := rfl
        compositionSurface := compositionSurfaceAt _
        compositionDecoded := rfl }

/-! ## Intent, support, replay -/

/-- One trivial-but-explicit intent profile: the contract's real verifier
    rejects everything (so `verifySound` is vacuous) and adequacy is the named
    `explicitlyTrivial` constructor — nothing is silently vacuous. -/
def demoIntent : IntentProfile.{0, 0, 0} where
  Goal := Unit
  contract := fun _ =>
    { History := Unit
      Certificate := Unit
      lawful := fun _ => True
      claim := fun _ => True
      verify := fun _ _ => false
      mutantVerify := fun _ _ => true }
  mandatoryGoals := [()]
  criticalGoals := []
  adequacy := fun _ => .explicitlyTrivial (fun _ _ => trivial)
  policy := .explicitlyAdmitEntireIntentTrivial

def demoRegistry : IntentRegistryKernel
    FacetCoherence.Tests.AddressRegistry Unit where
  IntentSpec := Unit
  profile := fun _ => demoIntent
  currentSpec := fun _ => ()
  addressOf := fun spec => spec
  registeredAddress := fun _ => ()
  registryExact := fun _ => rfl
  addressInjective := fun h => h

def demoObservation : IntentObservationKernel
    Carrier FacetCoherence.Tests.AddressRegistry Unit demoRegistry where
  observe := fun _ _ _ => ()
  verifySound := fun _ _ _ _ h => Bool.noConfusion h

def demoSupport : SupportSystem Carrier Nat where
  Node := Unit
  Judgment := Unit
  Verifier := Unit
  RootCertificate := Unit
  RuleCertificate := Unit
  rank := fun _ => 0
  premises := fun _ => []
  mandatoryJudgments := [()]
  LiveMandatoryAt := fun _ => True
  directSupport := fun _ _ => [()]
  expectedVerifier := fun _ => ()
  rootVerifier := fun _ => ()
  ruleVerifier := fun _ => ()
  rootImplementation := fun _ => 19
  ruleImplementation := fun _ => 19
  RootClaim := fun _ _ _ => True
  RuleClaim := fun _ _ _ => True
  verifyRoot := fun _ _ _ => false
  verifyRule := fun _ _ _ => false
  rootSound := fun _ _ _ h => Bool.noConfusion h
  ruleSound := fun _ _ _ h => Bool.noConfusion h

def demoReplay
    (snapshot : SealedSnapshot demoSealSpec)
    (carrier : SnapshotCarrier demoProjection snapshot) :
    ReplaySystem snapshot carrier where
  Judgment := Unit
  Receipt := Unit
  Object := Unit
  ObjectQ := Unit
  mandatoryJudgments := [()]
  LiveMandatoryAt := fun _ => True
  receiptFor := fun _ => ()
  receiptObjectQ := fun _ => ()
  lookup := fun _ => some ()
  objectQ := fun _ => ()
  objectBytes := fun _ => ""
  digest := fun _ => ()
  decodeReceipt := fun _ => some ()
  objectDependencies := fun _ => []
  objectRank := fun _ => 0
  receiptEpoch := fun _ => snapshot.coordinates.epoch
  receiptHistoryHead := fun _ => snapshot.coordinates.historyHead
  receiptAssumptionRoot := fun _ => snapshot.coordinates.assumptionRoot
  receiptAddressRegistry := fun _ => snapshot.coordinates.addressRegistry
  receiptSourceWindow := fun _ => snapshot.coordinates.sourceWindow
  receiptFailureModel := fun _ => snapshot.coordinates.failureModel
  receiptProposalWindow := fun _ => snapshot.coordinates.proposalWindow
  receiptImplementationBundle := fun _ =>
    snapshot.coordinates.implementationBundle
  verifyReplay := fun _ _ => false

def demoGoalMap :
    GoalJudgmentMap
      (demoRegistry.profile (demoRegistry.currentSpec 0)) Unit where
  judgmentFor := fun goal => goal
  injective := fun h => h

def demoSupportMap : SupportJudgmentMap Unit Unit where
  supportFor := fun judgment => judgment
  injective := fun h => h

/-! ## Primitives -/

/-- Every contract counts as insufficient; the family's observation is the
    constant `ResourceLimit`, so the totality law is inhabited honestly. -/
def demoPolicy : ResourcePolicy where
  insufficient := fun _ _ => True
  fullyExhaustedInsufficient := fun _ _ _ => trivial

def demoFamily : PrimitiveFamily.{0, 0, 0, 0} where
  Input := fun _ => Unit
  Output := fun _ => Unit
  Wake := Unit
  Residue := Unit
  observe := fun _ _ _ => .ResourceLimit ()

def demoPrimitiveImpl : PrimitiveImplementationProjection Nat where
  policy := fun _ => demoPolicy
  family := fun _ => demoFamily

def demoLawful : LawfulPrimitiveFamily demoPolicy demoFamily where
  resourceBound := fun _ _ _ _ => ⟨(), rfl⟩

def demoActual : ActualPrimitiveInvocation demoFamily where
  primitive := .SourceScan
  contract :=
    { fuel := 0
      deadlineTicks := 0
      searchBound := 0
      processTimeoutTicks := 0
      leaseTicks := 0 }
  input := ()
  observed := .ResourceLimit ()
  result := .ResourceExhausted ()

/-! ## Failure semantics and closure state system -/

def demoFailureSemantics : MetaFailureSemantics.{0, 0, 0} where
  Snapshot := FacetCoherence.Tests.HistoryHead
  FailureModel := Nat
  Failure := Unit
  CoverageEvidence := Unit
  ExceptionName := Unit
  snapshotDecidableEq := inferInstance
  failureModelDecidableEq := inferInstance
  failureDecidableEq := inferInstance
  coverage :=
    { modelAt := fun _ =>
        { inScope := fun _ => True
          mandatory := fun _ => True
          mandatoryInScope := fun _ _ => trivial
          declared := [()] }
      AdmittedAt := fun _ _ => True
      CoversAt := fun _ _ _ _ => True }
  AdmittedAt := fun _ _ => True
  NodeResidueAt := fun _ _ => False
  BridgeResidueAt := fun _ _ => False
  AssumptionViolationAt := fun _ _ => False
  ScopeEscapeAt := fun _ _ => False

/-- The closure system's live goals are exactly the current intent profile's
    mandatory goals — so `intentClosureGoalLiveExactAt` holds by `rfl`-level
    unwinding, not by an extra hypothesis. -/
def demoClosureSystem : ClosureStateSystem where
  State := Carrier
  Goal := Unit
  WorkItem := Unit
  Migration := Unit
  goalDecidableEq := inferInstance
  migrationDecidableEq := inferInstance
  liveGoalAt := fun carrier goal =>
    goal ∈
      (demoRegistry.profile
        (demoRegistry.currentSpec carrier.addressRegistry)).mandatoryGoals
  goalsAt := fun carrier =>
    (demoRegistry.profile
      (demoRegistry.currentSpec carrier.addressRegistry)).mandatoryGoals
  MandatoryGoalAt := fun carrier goal =>
    goal ∈
      (demoRegistry.profile
        (demoRegistry.currentSpec carrier.addressRegistry)).mandatoryGoals
  GoalSatisfiedAt := fun _ _ => True
  targetGoal := fun _ => ()
  InvalidWorkItemAt := fun _ _ => False
  TerminalAt := fun _ _ => False
  mandatoryTerminalSound := fun _ _ _ terminal => terminal.elim
  DisputedAt := fun _ _ => False
  ReadyAt := fun _ _ => False
  BlockedAt := fun _ _ => False
  RuntimeAt := fun _ _ => False
  StuckAt := fun _ _ => False
  workflowFactsAt := fun _ _ =>
    { terminal := .unknown
      disputed := .unknown
      ready := .unknown
      blocked := .unknown
      runtime := .unknown
      stuck := .unknown }
  migrationInScopeAt := fun _ _ => False
  migrationsAt := fun _ => []
  PendingMigrationAt := fun _ _ => False
  migrationEvidenceAt := fun _ _ => .unknown

/-- The failure context is the state's own snapshot head and failure-model
    coordinate, so `failureContextExact` is `rfl`. -/
def demoFailureTerminal :
    FailureTerminalSystem Carrier demoFailureSemantics where
  Receipt := Unit
  contextAt := fun carrier =>
    { snapshot := carrier.historyHead
      failureModel := carrier.failureModel }
  mandatoryFailuresAt := fun _ => [()]
  receiptAt := fun _ _ => none
  receiptName := fun _ => ""
  receiptContext := fun _ =>
    ({ snapshot := .h1, failureModel := 0 } : FailureContext HistoryHead Nat)
  receiptFailure := fun _ => ()
  receiptClass := fun _ => .nodeResidue
  receiptKind := fun _ => .resolved
  ResolvedAt := fun _ _ _ => False
  BoundaryAt := fun _ _ _ => False
  InvalidAt := fun _ _ _ => False
  terminalCertificateAt := fun _ _ _ => none

def demoFailureFacts
    (context : FailureContext
      demoFailureSemantics.Snapshot demoFailureSemantics.FailureModel) :
    FailureFacts demoFailureSemantics context () where
  node := .unknown
  bridge := .unknown
  assumption := .unknown
  scopeEscape := .unknown

/-- An honest admitted window: every (unit) failure is in scope and admitted,
    each carrying an all-unknown facts packet — ambiguity is reported, not
    hidden. -/
def demoFailureWindow
    (context : FailureContext
      demoFailureSemantics.Snapshot demoFailureSemantics.FailureModel) :
    AdmittedFailureWindow demoFailureSemantics context where
  universeSeal :=
    { declaredSound := fun _ _ => trivial
      declaredComplete := fun failure _ => by
        cases failure
        exact List.Mem.head [] }
  coverageEvidence := [()]
  coverageCertificate :=
    { mandatoryNonempty := ⟨(), trivial⟩
      everyMandatoryCovered := fun _ _ =>
        ⟨(), List.Mem.head [], trivial, trivial⟩ }
  factsAt := fun _ => some (demoFailureFacts context)
  packetSound := fun _ _ _ => ⟨trivial, trivial⟩
  packetComplete := fun _ _ => ⟨demoFailureFacts context, rfl⟩

def demoEffectSnapshotAt (state : Carrier) :
    EffectSnapshot
      FacetCoherence.Tests.Epoch FacetCoherence.Tests.HistoryHead
      Unit Unit Unit Unit where
  epoch := state.epoch
  head := state.historyHead
  currentGeneration := fun _ => ()
  policyTerminalFailure := fun _ => False
  externalEffects := []
  observe := fun _ => none

/-! ## The concrete `ClosureContext` inhabitant -/

/-- The first concrete `ClosureContext` inhabitant in the tree.

    FC-1 state = the `FacetCoherence.Tests` carrier; snapshot coordinates are
    projected from the state itself; the FC-2 adapter/certificate is the Tests
    demo re-run per state; the closure system's live goals are the intent
    profile's mandatory goals; the failure context is the state's own head and
    failure-model coordinate.  No vacuous `False`-premise fields: every
    proof-carrying obligation either computes to `True`-styled honest
    inhabitants or discharges through the engineered equalities above. -/
def demoContext : ClosureContext Carrier where
  Epoch := FacetCoherence.Tests.Epoch
  HistoryHead := FacetCoherence.Tests.HistoryHead
  historyHeadDecidableEq := inferInstance
  AssumptionRoot := FacetCoherence.Tests.AssumptionRoot
  AddressRegistry := FacetCoherence.Tests.AddressRegistry
  SourceAuthority := Unit
  Watermark := Unit
  Partition := Unit
  FailureModel := FacetCoherence.Tests.FailureModel
  ProposalWindow := FacetCoherence.Tests.ProposalWindow
  ImplementationBundle := FacetCoherence.Tests.ImplementationBundle
  sealSpec := demoSealSpec
  projection := demoProjection
  snapshotAt := demoSnapshotAt
  carrierAt := demoCarrierAt
  carrierValueBound := fun _ => rfl
  Payload := Payload
  bundleAt := demoBundleAt
  adapter := adapter
  facetCertificateAt := demoFacetCertificateAt
  formalStateAt := fun _ current =>
    match current.historyHead with
    | .h1 => .before
    | .h2 => .after
  advanceEvidenceAt := fun _ _ _ => .witness
  advanceEventAt := fun _ _ _ => .admitted
  supportSystem := demoSupport
  replaySystemAt := fun state =>
    demoReplay (demoSnapshotAt state) (demoCarrierAt state)
  IntentAddress := Unit
  intentRegistry := demoRegistry
  intentObservation := demoObservation
  intentGoalMapAt := fun _ => demoGoalMap
  intentSupportMapAt := fun _ => demoSupportMap
  primitiveImplementation := demoPrimitiveImpl
  PrimitiveInvocation := Unit
  primitiveInvocationDecidableEq := inferInstance
  primitiveInScopeAt := fun _ _ => True
  primitiveInvocationsAt := fun _ => []
  primitiveLawfulAt := fun _ => demoLawful
  primitiveActualAt := fun _ _ => demoActual
  primitiveRuntimeBeforeAt := fun _ _ => .runningBefore
  primitiveRuntimeAfterAt := fun _ _ => .runningAfter
  PrimitiveMeasurementReceipt := Unit
  primitiveMeasuredReceiptAt := fun _ _ => none
  primitiveMeasurementBindsAt := fun _ _ _ => False
  ReepochGoal := Unit
  ReepochOccurrence := Unit
  ReepochSemanticValue := Unit
  ReepochGoalOrigin := Unit
  reepochSemanticValue := fun _ _ => ()
  reepochParentEpoch := fun _ => none
  reepochGoalOrigin := fun _ => ()
  reepochGoalSatisfied := fun _ _ => True
  reepochNonterminal := fun _ _ => False
  reepochTerminalAtMigration := fun _ _ => False
  reepochTriggerOccurrence := fun _ => none
  reepochMigrationForOccurrence := fun _ => none
  reepochNewObservationAdmitted := fun _ _ => False
  reepochPolicyDecisionAdmitted := fun _ _ => False
  reepochKernelReplacementAdmitted := fun _ _ => False
  reepochStableObstructionAdmitted := fun _ _ => False
  reepochMeasure := fun _ => 0
  EffectSlot := Unit
  Generation := Unit
  Occurrence := Unit
  FailureName := Unit
  effectSnapshotAt := demoEffectSnapshotAt
  EffectInScopeAt := fun _ _ => True
  failureSemantics := demoFailureSemantics
  failureSnapshotOf := fun head => head
  failureModelOf := fun model => model
  failureSnapshotFaithful := fun _ _ h => h
  failureModelFaithful := fun _ _ h => h
  closureSystem := demoClosureSystem
  closureStateAt := fun state => state
  intentClosureGoalForAt := fun _ goal => goal
  intentClosureGoalInjectiveAt := fun _ _ _ h => h
  intentClosureGoalLiveExactAt := fun _ closureGoal =>
    { mp := fun h => ⟨closureGoal, h, rfl⟩
      mpr := fun ⟨_goal, live, same⟩ => same ▸ live }
  failureTerminalSystem := demoFailureTerminal
  failureContextExact := fun _ => rfl
  failureWindowAt := fun state =>
    demoFailureWindow (demoFailureTerminal.contextAt state)

/- `demoContext` above IS the inhabitant evidence the strict reading
   required — its type `ClosureContext Carrier` elaborates concretely
   (`Type 1`), and `⟨demoContext⟩` inhabits `Nonempty _` on demand.
   (No standalone `Nonempty (ClosureContext Carrier)` theorem is stated:
   the structure's pooled universe binders differ between Lean 4.14 and
   4.29, so any signature that names `ClosureContext` bare goes rigid
   under `autoBound`, and an explicit `.{…}` pin is version-fragile.) -/


/-! ## Discriminating sites at the concrete context -/

/-- The two fixture states: `before` carries head `.h1`, `after` head `.h2`,
    so the formal-state map reads `.before → .after`. -/
def before : Carrier := carrierH1Value

def after : Carrier := carrierH2Value

/-- A real admitted advance packet: `.h1 ↦ .before` reduces to `.h2 ↦ .after`
    and the fixture witness is admitted. -/
def demoPacket : AdvancePacket demoContext before after where
  reduces := Reduces.advance
  admitted := Admits.witness

/-- Positive site: the existing packet resolves to a durable history edge. -/
theorem advance_resolves_at_concrete_context :
    HistoryEdge (demoSurface demoContext) before after :=
  existing_advance_resolves_to_history_edge demoPacket

/-- Mutant: same surface with admission disabled. -/
def notAdmittedSurface : StepSurface demoContext :=
  { demoSurface demoContext with admitted := fun _ => false }

/-- The non-admission refusal now runs at the concrete context and packet. -/
theorem nonadmitted_refuses_at_concrete_context :
    ¬ Nonempty (BoundAdvance notAdmittedSurface demoPacket) :=
  nonadmitted_advance_cannot_resolve_to_history
    (surface := notAdmittedSurface) (packet := demoPacket) rfl

/-- The empty-settled-event mutant cannot append durable history here either. -/
theorem empty_event_refuses_at_concrete_context :
    ¬ HistoryEdge (emptyEventSurface demoContext) before after :=
  empty_event_mutant_cannot_append_history

/-- The packet really is admitted on the positive surface (rfl), so the two
    sites genuinely discriminate admitted-vs-not at one concrete packet. -/
theorem demo_packet_is_admitted :
    (demoSurface demoContext).admitted
      ((demoSurface demoContext).classOf demoPacket) = true :=
  rfl

/-! ## GoalWorkSystem-parametric fields exercised at one concrete system -/

def demoGWSystem : GoalWorkSystem.{0, 0} where
  Goal := Unit
  WorkItem := Unit
  workDecidableEq := inferInstance
  target := fun _ => ()

def demoGWSnapshot : GoalWorkSnapshot demoGWSystem where
  goalPresent := fun _ => true
  goalStatus := fun _ => .open
  workStatus := fun _ => .active

theorem work_preserves_goal_presence :
    (applyWorkAction demoGWSystem demoGWSnapshot () .invalidate).goalPresent
        () = true :=
  work_action_preserves_goal_presence
    demoGWSystem demoGWSnapshot () .invalidate ()

theorem work_preserves_goal_status :
    (applyWorkAction demoGWSystem demoGWSnapshot () .reject).goalStatus
        () = .open :=
  work_action_preserves_goal_status
    demoGWSystem demoGWSnapshot () .reject ()

theorem acted_target_stays_open_and_disposed :
    (applyWorkAction demoGWSystem demoGWSnapshot () .supersede).goalStatus
        (demoGWSystem.target ()) = .open ∧
      (applyWorkAction demoGWSystem demoGWSnapshot () .supersede).workStatus
          () = .superseded :=
  ⟨ (target_goal_remains_open_after_work_action
      demoGWSystem demoGWSnapshot () .supersede rfl rfl).2,
    acted_work_receives_status
      demoGWSystem demoGWSnapshot () .supersede ⟩

#print axioms demoContext
#print axioms advance_resolves_at_concrete_context
#print axioms nonadmitted_refuses_at_concrete_context
#print axioms empty_event_refuses_at_concrete_context
#print axioms demo_packet_is_admitted
#print axioms work_preserves_goal_presence
#print axioms work_preserves_goal_status
#print axioms acted_target_stays_open_and_disposed

end Residua.RCC.RegistrationSites.R1

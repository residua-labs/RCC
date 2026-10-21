import RCC.FinalityLiveness

/-!
# RCC-46 Conditional Finality Liveness Countermodels

The positive witness reaches the real RCC-42 `fencedFinalize` surface within a
finite declared horizon.  Each missing liveness premise returns its own named
`Await`, even though the local writer snapshot already contains the proposal.
-/

namespace Residua.RCC.FinalityLiveness.Tests

open Residua.RCC
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalityLiveness

inductive Slot
  | deploy
  deriving DecidableEq

inductive Head
  | genesis
  deriving DecidableEq

inductive Judgment
  | commit
  deriving DecidableEq

inductive Generation
  | current
  deriving DecidableEq

inductive Version
  | before
  | after
  deriving DecidableEq

inductive Config
  | current
  deriving DecidableEq

inductive ConfigTransition
  | declared
  deriving DecidableEq

def transitionView :
    ConfigTransitionView Slot Head Config where
  Transition := ConfigTransition
  InUniverse := fun transition => transition = .declared
  pendingAt := fun _ _ _ _ => False

def transitionCoverage :
    CoverageCertificate transitionView.InUniverse [.declared] where
  sound := by
    intro transition _
    cases transition
    rfl
  complete := by
    intro transition _
    cases transition
    simp

def stableConfigEvidence :
    StableConfigEvidence
      transitionView .deploy .genesis .current where
  transitions := [.declared]
  coverage := transitionCoverage
  noPending := by
    intro _ _ pending
    exact pending

def proposal : Proposal Slot Head Judgment :=
  ⟨.deploy, .genesis, .commit⟩

/--
The test authorization token inhabits only the exact proposal fiber.  This
prevents a receipt for another proposal from being transported into this
finality run.
-/
inductive AuthorityEvidence : Proposal Slot Head Judgment → Type
  | quorum : AuthorityEvidence proposal

def authorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨proposal, .quorum⟩

def writerSpec : FencedWriterSpec Slot Head where
  slotParent := fun _ => .genesis

def judgmentEq : JudgmentEquivalence Judgment where
  Equivalent := Eq
  refl := by intro _; rfl
  symm := by intro _ _ equality; exact equality.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide := fun first second => inferInstanceAs (Decidable (first = second))

def request :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨authorization, .current⟩

def committedState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .genesis
  decisions := fun _ => some .commit

def linearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Version writerSpec judgmentEq where
  Precedes := fun _ _ => True
  precedesRefl := by intro _; trivial
  precedesTrans := by intro _ _ _ _ _; trivial
  comparable := by intro _ _; exact Or.inl True.intro
  activeGeneration := fun _ _ => .current
  canonicalDecision := fun _ _ _ => some .commit
  decisionPreserved := by
    intro _ _ _ _ judgment _ committed
    exact committed

def committedSnapshot (version : Version) :
    CanonicalWriterSnapshot linearizer version committedState where
  generationBound := rfl
  decisionBound := by intro slot; cases slot; rfl

def world : BoundedFinalityWorld writerSpec judgmentEq request where
  Version := Version
  linearizer := linearizer
  horizon := 5
  stateAt := fun _ => committedState
  versionAt := fun _ => .after
  canonicalSnapshotAt := fun _ => committedSnapshot .after
  Config := Config
  transitionView := transitionView
  configAt := fun _ => .current
  Lawful := fun candidate => candidate = proposal
  Eligible := fun _ candidate => candidate = proposal
  QuorumAvailable := fun _ => True
  FairDelivery := fun _ => True
  ReconfigurationBounded := fun _ => True
  DurableLockAvailable := fun _ => True

def progressAdapter : FinalityProgressAdapter world where
  ProgressReceipt := fun _ => PUnit
  makeReceipt := by
    intro step lawful eligible quorum delivery stable bounded lockAvailable
    exact PUnit.unit
  receiptRefinesCanonicalFinalize := by
    intro step receipt
    exact {
      slotBound := rfl
      parentBound := rfl
      generationBound := rfl
      decisionCommitted := rfl
    }

/-! ## All-True environmental predicates are not a progress proof -/

def uncommittedState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .genesis
  decisions := fun _ => none

def emptyLinearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Version writerSpec judgmentEq where
  Precedes := fun _ _ => True
  precedesRefl := by intro _; trivial
  precedesTrans := by intro _ _ _ _ _; trivial
  comparable := by intro _ _; exact Or.inl True.intro
  activeGeneration := fun _ _ => .current
  canonicalDecision := fun _ _ _ => none
  decisionPreserved := by
    intro _ _ _ _ judgment _ impossible
    simp at impossible

def uncommittedSnapshot (version : Version) :
    CanonicalWriterSnapshot emptyLinearizer version uncommittedState where
  generationBound := rfl
  decisionBound := by intro slot; cases slot; rfl

/--
CM-RCC46-COUPLING: every named environmental predicate is true, and the state
is a genuine global-linearizer snapshot, but no decision has been committed.
-/
def allTrueUncommittedWorld :
    BoundedFinalityWorld writerSpec judgmentEq request where
  Version := Version
  linearizer := emptyLinearizer
  horizon := 5
  stateAt := fun _ => uncommittedState
  versionAt := fun _ => .after
  canonicalSnapshotAt := fun _ => uncommittedSnapshot .after
  Config := Config
  transitionView := transitionView
  configAt := fun _ => .current
  Lawful := fun _ => True
  Eligible := fun _ _ => True
  QuorumAvailable := fun _ => True
  FairDelivery := fun _ => True
  ReconfigurationBounded := fun _ => True
  DurableLockAvailable := fun _ => True

/--
The five all-True environment predicates cannot fabricate the separate
progress/refinement adapter.  The contradiction is the missing canonical
decision, not a policy convention.
-/
theorem all_true_environment_cannot_fabricate_finality_progress :
    ¬ Nonempty (FinalityProgressAdapter allTrueUncommittedWorld) := by
  rintro ⟨progress⟩
  have stable :
      StableConfigAt allTrueUncommittedWorld 0 :=
    ⟨stableConfigEvidence⟩
  have receipt :=
    progress.makeReceipt 0
      True.intro True.intro True.intro True.intro stable True.intro
        True.intro
  have ready :=
    progress.receiptRefinesCanonicalFinalize 0 receipt
  have impossible :
      (none : Option Judgment) = some .commit :=
    ready.decisionCommitted
  cases impossible

def alwaysByZero : BoundedEventually (fun _ : Nat => True) 5 where
  bound := 0
  boundWithin := by decide
  holdsThrough := by
    intro step lower upper
    trivial

def quorumEvidence : QuorumAvailabilityCert world :=
  ⟨alwaysByZero⟩

def deliveryEvidence : FairDeliveryCert world :=
  ⟨alwaysByZero⟩

def stableConfigByZero :
    BoundedEventually (StableConfigAt world) 5 where
  bound := 0
  boundWithin := by decide
  holdsThrough := by
    intro step lower upper
    exact ⟨stableConfigEvidence⟩

def stableConfigCert : EventuallyStableConfigCert world :=
  ⟨stableConfigByZero⟩

def reconfigurationEvidence : BoundedReconfigurationCert world :=
  ⟨alwaysByZero⟩

def lockEvidence : DurableLockAvailabilityCert world :=
  ⟨alwaysByZero⟩

def completePremises : FinalityLivenessPremises world where
  quorum := quorumEvidence
  delivery := deliveryEvidence
  stableConfig := stableConfigCert
  boundedReconfiguration := reconfigurationEvidence
  durableLock := lockEvidence

def continuousEligibility :
    ContinuouslyEligible world where
  lawful := rfl
  eligible := by
    intro step withinHorizon
    rfl

def completePacket : FinalityLivenessEvidence world where
  quorum := some quorumEvidence
  delivery := some deliveryEvidence
  stableConfig := some stableConfigCert
  boundedReconfiguration := some reconfigurationEvidence
  durableLock := some lockEvidence

def missingQuorumPacket : FinalityLivenessEvidence world :=
  { completePacket with quorum := none }

def missingDeliveryPacket : FinalityLivenessEvidence world :=
  { completePacket with delivery := none }

def missingStableConfigPacket : FinalityLivenessEvidence world :=
  { completePacket with stableConfig := none }

def missingReconfigurationPacket : FinalityLivenessEvidence world :=
  { completePacket with boundedReconfiguration := none }

def missingLockPacket : FinalityLivenessEvidence world :=
  { completePacket with durableLock := none }

/-! ## Each absent premise is a distinct, honest wait -/

theorem missing_quorum_awaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket =
      .Await .finalityQuorumUnavailable := by
  rfl

theorem missing_fair_delivery_awaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingDeliveryPacket =
      .Await .finalityDeliveryPending := by
  rfl

theorem missing_stable_config_awaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingStableConfigPacket =
      .Await .finalityStableConfigPending := by
  rfl

theorem missing_bounded_reconfiguration_awaits :
    runConditionalFinality world progressAdapter continuousEligibility
        missingReconfigurationPacket =
      .Await .finalityReconfigurationPending := by
  rfl

theorem missing_durable_lock_awaits :
    runConditionalFinality
        world progressAdapter continuousEligibility missingLockPacket =
      .Await .finalityDurableLockUnavailable := by
  rfl

/--
Even a locally committed writer state cannot self-finalize when quorum
availability evidence is absent.
-/
theorem local_commit_does_not_bypass_missing_quorum :
    committedState.decisions .deploy = some .commit ∧
      (runConditionalFinality
        world progressAdapter continuousEligibility missingQuorumPacket).value? =
        none := by
  exact ⟨rfl, rfl⟩

/-! ## Positive bounded liveness reaches the actual RCC-42 computation -/

def boundedWitness :
    BoundedFinalityWitness world :=
  conditional_finality_liveness
    world progressAdapter continuousEligibility completePremises

theorem bounded_witness_is_within_declared_horizon :
    boundedWitness.step ≤ world.horizon :=
  boundedWitness.withinHorizon

theorem bounded_witness_is_actual_success :
    fencedFinalize writerSpec judgmentEq
        (world.stateAt boundedWitness.step) request =
      .Ok boundedWitness.success.localSuccess.output :=
  boundedWitness.success.localSuccess.accepted

theorem complete_packet_runs_to_actual_success :
    ∃ witness,
      runConditionalFinality
          world progressAdapter continuousEligibility completePacket =
        .Ok witness ∧
      fencedFinalize writerSpec judgmentEq
          (world.stateAt witness.step) request =
        .Ok witness.success.localSuccess.output := by
  refine
    ⟨boundedWitness, ?_, boundedWitness.success.localSuccess.accepted⟩
  rfl

/--
Safety consumes two global RCC-42 successes.  No liveness premise appears in
this theorem's type, and the theorem does not require one receiver state.
-/
theorem safety_is_unconditional :
    judgmentEq.Equivalent proposal.judgment proposal.judgment :=
  finality_safety_unconditional
    linearizer boundedWitness.success boundedWitness.success rfl rfl

def replicaState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .genesis
  decisions := fun _ => some .commit

def replicaSnapshot :
    CanonicalWriterSnapshot linearizer .before replicaState where
  generationBound := rfl
  decisionBound := by intro slot; cases slot; rfl

def replicaReady :
    CanonicalFinalizeReady writerSpec replicaState request where
  slotBound := rfl
  parentBound := rfl
  generationBound := rfl
  decisionCommitted := rfl

def replicaSuccess :
    GloballySuccessfulFinalize linearizer .before replicaState request where
  snapshot := replicaSnapshot
  localSuccess :=
    successfulFinalizeOfReady
      writerSpec judgmentEq replicaState request replicaReady

/--
The public safety theorem crosses receiver snapshots and canonical versions;
it is not the old same-state lemma.
-/
theorem cross_snapshot_cross_version_safety_is_unconditional :
    judgmentEq.Equivalent proposal.judgment proposal.judgment :=
  finality_safety_unconditional
    linearizer boundedWitness.success replicaSuccess rfl rfl

#print axioms missing_quorum_awaits
#print axioms missing_fair_delivery_awaits
#print axioms missing_stable_config_awaits
#print axioms missing_bounded_reconfiguration_awaits
#print axioms missing_durable_lock_awaits
#print axioms local_commit_does_not_bypass_missing_quorum
#print axioms all_true_environment_cannot_fabricate_finality_progress
#print axioms fencedFinalize_of_ready
#print axioms successfulFinalizeOfReady
#print axioms finalityReadyStep_within_horizon
#print axioms conditional_finality_liveness
#print axioms conditional_finality_liveness_theorem
#print axioms bounded_witness_is_actual_success
#print axioms complete_packet_runs_to_actual_success
#print axioms finality_safety_unconditional
#print axioms safety_is_unconditional
#print axioms cross_snapshot_cross_version_safety_is_unconditional

end Residua.RCC.FinalityLiveness.Tests

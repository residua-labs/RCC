import RCC.GoalAdequacy
import RCC.EvidenceReplayability
import RCC.SupportClosure

/-!
# RCC intent/snapshot and Goal/replay/support binding

An intent is selected mechanically from the FC-1 address-registry coordinate.
It cannot change at the same epoch without violating the epoch-stability law.
Closure is not a caller proposition: `DerivedIntentSatisfied` means that every
mandatory goal of the exact selected intent has an accepted certificate, from
which the goal claim follows by verifier soundness.

The second half binds each mandatory Goal injectively to a replay judgment,
the exact Goal/certificate envelope retained by that replay receipt, and an
injective support judgment with a semantically exact checked support root.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.IntentSnapshotBinding

open Residua.RCC
open Residua.RCC.FacetSnapshot
open Residua.RCC.EvidenceReplayability
open Residua.RCC.SupportClosure

universe u

/-! ## Intent selection at an FC-1 snapshot -/

/--
An address-registry projection selects exactly one intent specification.
`addressInjective` makes the registered address an identity for this declared
specification domain rather than a caller label.
-/
structure IntentRegistryKernel
    (AddressRegistry IntentAddress : Type u) where
  IntentSpec : Type u
  profile : IntentSpec → IntentProfile.{u, u, u}
  currentSpec : AddressRegistry → IntentSpec
  addressOf : IntentSpec → IntentAddress
  registeredAddress : AddressRegistry → IntentAddress
  registryExact :
    ∀ registry,
      addressOf (currentSpec registry) = registeredAddress registry
  addressInjective :
    ∀ {left right}, addressOf left = addressOf right → left = right

/-- Goal observation and verifier soundness for each registered intent spec. -/
structure IntentObservationKernel
    (Carrier AddressRegistry IntentAddress : Type u)
    (registry : IntentRegistryKernel AddressRegistry IntentAddress) where
  observe :
    (spec : registry.IntentSpec) →
      (goal : (registry.profile spec).Goal) →
      Carrier →
      ((registry.profile spec).contract goal).History
  verifySound :
    ∀ spec carrier goal certificate,
      ((registry.profile spec).contract goal).verify
          (observe spec goal carrier) certificate = true →
        ((registry.profile spec).contract goal).claim
          (observe spec goal carrier)

/--
A declared semantic intent is covered when all mandatory Goal claims suffice
to establish it. The intent predicate is fixed outside the contract, so an
evidence packet cannot choose a trivial target for itself.
-/
structure IntentCoverageContract
    {Carrier AddressRegistry IntentAddress : Type u}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress)
    (observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry)
    (IntentSatisfied : registry.IntentSpec → Carrier → Prop) : Prop where
  mandatoryClaimsSuffice :
    ∀ spec carrier,
      (∀ goal,
        goal ∈ (registry.profile spec).mandatoryGoals →
          ((registry.profile spec).contract goal).claim
            (observation.observe spec goal carrier)) →
        IntentSatisfied spec carrier

/-- The intent spec selected by one exact FC-1 snapshot. -/
def currentIntentSpec
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress)
    (snapshot : SealedSnapshot sealSpec) :
    registry.IntentSpec :=
  registry.currentSpec snapshot.coordinates.addressRegistry

/-- The intent address selected by one exact FC-1 snapshot. -/
def currentIntentAddress
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress)
    (snapshot : SealedSnapshot sealSpec) :
    IntentAddress :=
  registry.registeredAddress snapshot.coordinates.addressRegistry

/--
Within one epoch, the registered intent address is stable.  A policy-authorized
intent amendment must therefore use a successor epoch.
-/
structure IntentEpochBinding
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress) : Prop where
  sameEpochAddress :
    ∀ first second : SealedSnapshot sealSpec,
      first.coordinates.epoch = second.coordinates.epoch →
        currentIntentAddress registry first =
          currentIntentAddress registry second

/-- Equal-epoch snapshots select the same intent specification. -/
theorem same_epoch_intent_spec
    {Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    (binding : IntentEpochBinding (sealSpec := sealSpec) registry)
    (first second : SealedSnapshot sealSpec)
    (sameEpoch : first.coordinates.epoch = second.coordinates.epoch) :
    currentIntentSpec registry first = currentIntentSpec registry second := by
  apply registry.addressInjective
  calc
    registry.addressOf (currentIntentSpec registry first) =
        currentIntentAddress registry first :=
      registry.registryExact first.coordinates.addressRegistry
    _ = currentIntentAddress registry second :=
      binding.sameEpochAddress first second sameEpoch
    _ = registry.addressOf (currentIntentSpec registry second) :=
      (registry.registryExact second.coordinates.addressRegistry).symm

/-! ## Mechanically derived intent satisfaction -/

/--
Proof-carrying closure of every mandatory goal of the intent selected by this
exact FC-1 snapshot/carrier.
-/
structure DerivedIntentClosureAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress)
    (observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) where
  epochBinding :
    IntentEpochBinding (sealSpec := sealSpec) registry
  observedSnapshot : SealedSnapshot sealSpec
  snapshotBound : observedSnapshot = snapshot
  requireLoadBearing :
    (registry.profile (currentIntentSpec registry snapshot)).policy =
      .requireLoadBearing
  closureAdequate :
    ClosureAdequate
      (registry.profile (currentIntentSpec registry snapshot))
  certificate :
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal) →
      ((registry.profile (currentIntentSpec registry snapshot)).contract goal).Certificate
  accepted :
    ∀ goal,
      goal ∈
          (registry.profile
            (currentIntentSpec registry snapshot)).mandatoryGoals →
        ((registry.profile
          (currentIntentSpec registry snapshot)).contract goal).verify
            (observation.observe
              (currentIntentSpec registry snapshot) goal carrier.value)
            (certificate goal) = true

/--
This is the mechanically derived mandatory-certificate product. Semantic
intent satisfaction additionally requires an `IntentCoverageContract`.
-/
def DerivedIntentSatisfied
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    (registry : IntentRegistryKernel AddressRegistry IntentAddress)
    (observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) : Prop :=
  Nonempty (DerivedIntentClosureAt registry observation snapshot carrier)

/-- Every mandatory claim follows from the exact accepted certificate. -/
theorem DerivedIntentClosureAt.mandatoryClaim
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (closed : DerivedIntentClosureAt registry observation snapshot carrier)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (mandatory :
      goal ∈
        (registry.profile
          (currentIntentSpec registry snapshot)).mandatoryGoals) :
    ((registry.profile
      (currentIntentSpec registry snapshot)).contract goal).claim
        (observation.observe
          (currentIntentSpec registry snapshot) goal carrier.value) :=
  observation.verifySound
    (currentIntentSpec registry snapshot) carrier.value goal
      (closed.certificate goal) (closed.accepted goal mandatory)

/--
Accepted certificates for every mandatory Goal establish the externally fixed
semantic intent through its coverage sufficiency law.
-/
theorem DerivedIntentClosureAt.intentSatisfied
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {IntentSatisfied : registry.IntentSpec → Carrier → Prop}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (coverage :
      IntentCoverageContract registry observation IntentSatisfied)
    (closed : DerivedIntentClosureAt registry observation snapshot carrier) :
    IntentSatisfied (currentIntentSpec registry snapshot) carrier.value :=
  coverage.mandatoryClaimsSuffice
    (currentIntentSpec registry snapshot) carrier.value
    (fun goal mandatory => closed.mandatoryClaim goal mandatory)

/-- The selected mandatory-goal universe is nonempty and load-bearing. -/
theorem DerivedIntentClosureAt.mandatoryNonempty
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (closed : DerivedIntentClosureAt registry observation snapshot carrier) :
    (registry.profile
      (currentIntentSpec registry snapshot)).mandatoryGoals ≠ [] :=
  intent_adequate_requires_nonempty_mandatory
    (registry.profile (currentIntentSpec registry snapshot))
    closed.requireLoadBearing closed.closureAdequate.1

/-- A closure witness retains its exact snapshot and cannot be rebound. -/
theorem DerivedIntentClosureAt.cannotBindDifferentSnapshot
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot other : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (closed : DerivedIntentClosureAt registry observation snapshot carrier)
    (different : snapshot ≠ other) :
    closed.observedSnapshot ≠ other := by
  intro rebound
  exact different (closed.snapshotBound.symm.trans rebound)

/-! ## Goal → replay judgment → support root -/

/-- An accepted Goal and its exact certificate as one dependent payload. -/
structure GoalCertificateEnvelope
    (profile : IntentProfile.{u, u, u}) where
  goal : profile.Goal
  certificate : (profile.contract goal).Certificate

/-- A Goal-to-judgment map that cannot collapse distinct Goals. -/
structure GoalJudgmentMap
    (profile : IntentProfile.{u, u, u})
    (Judgment : Type u) where
  judgmentFor : profile.Goal → Judgment
  injective :
    ∀ {left right},
      judgmentFor left = judgmentFor right → left = right

/-- A replay-judgment-to-support-judgment map that cannot collapse claims. -/
structure SupportJudgmentMap
    (ReplayJudgment SupportJudgment : Type u) where
  supportFor : ReplayJudgment → SupportJudgment
  injective :
    ∀ {left right}, supportFor left = supportFor right → left = right

/--
Exact association between accepted Goal certificates and current replay
receipts.  The replay checker must return the same Boolean as the Goal checker;
an unrelated always-true replay checker cannot satisfy this law.
-/
structure ReplayGoalAssociation
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (closed : DerivedIntentClosureAt registry observation snapshot carrier)
    (replay : ReplaySystem snapshot carrier)
    (goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment) where
  encodeReceipt :
    GoalCertificateEnvelope
      (registry.profile (currentIntentSpec registry snapshot)) →
      replay.Receipt
  encodeInjective :
    ∀ {left right}, encodeReceipt left = encodeReceipt right → left = right
  liveExact :
    ∀ judgment,
      replay.LiveMandatoryAt judgment ↔
        ∃ goal,
          goal ∈
              (registry.profile
                (currentIntentSpec registry snapshot)).mandatoryGoals ∧
            goalMap.judgmentFor goal = judgment
  mandatoryListExact :
    replay.mandatoryJudgments =
      (registry.profile
        (currentIntentSpec registry snapshot)).mandatoryGoals.map
          goalMap.judgmentFor
  receiptExact :
    ∀ goal,
      goal ∈
          (registry.profile
            (currentIntentSpec registry snapshot)).mandatoryGoals →
      replay.receiptFor (goalMap.judgmentFor goal) =
        encodeReceipt {
          goal := goal
          certificate := closed.certificate goal
        }
  verifierExactAll :
    ∀ envelope :
        GoalCertificateEnvelope
          (registry.profile (currentIntentSpec registry snapshot)),
      replay.verifyReplay
          (goalMap.judgmentFor envelope.goal)
          (encodeReceipt envelope) =
        ((registry.profile
          (currentIntentSpec registry snapshot)).contract envelope.goal).verify
            (observation.observe
              (currentIntentSpec registry snapshot) envelope.goal carrier.value)
            envelope.certificate
  replayability : EvidenceReplayabilityAt replay

/-- Replaying a mandatory Goal yields its exact current accepted verdict. -/
theorem ReplayGoalAssociation.mandatoryReplayAccepted
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    (association : ReplayGoalAssociation closed replay goalMap)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (mandatory :
      goal ∈
        (registry.profile
          (currentIntentSpec registry snapshot)).mandatoryGoals) :
    replay.verifyReplay
        (goalMap.judgmentFor goal)
        (replay.receiptFor (goalMap.judgmentFor goal)) = true := by
  rw [association.receiptExact goal mandatory]
  rw [association.verifierExactAll {
    goal := goal
    certificate := closed.certificate goal
  }]
  exact closed.accepted goal mandatory

/--
Replay rejection follows from Goal-verifier rejection.  This theorem is used by
the always-true replay-verifier mutant.  It deliberately ranges over arbitrary
certificates rather than the already accepted closure certificate.
-/
theorem ReplayGoalAssociation.replayRejectsWhenGoalRejects
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    (association : ReplayGoalAssociation closed replay goalMap)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (certificate :
      ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).Certificate)
    (rejected :
      ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).verify
          (observation.observe
            (currentIntentSpec registry snapshot) goal carrier.value)
          certificate = false) :
    replay.verifyReplay
        (goalMap.judgmentFor goal)
        (association.encodeReceipt {
          goal := goal
          certificate := certificate
        }) = false := by
  rw [association.verifierExactAll {
    goal := goal
    certificate := certificate
  }]
  exact rejected

/-- An always-accepting replay implementation cannot mask a rejected certificate. -/
theorem ReplayGoalAssociation.alwaysTrueCannotMaskRejectedGoal
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    (association : ReplayGoalAssociation closed replay goalMap)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (certificate :
      ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).Certificate)
    (rejected :
      ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).verify
          (observation.observe
            (currentIntentSpec registry snapshot) goal carrier.value)
          certificate = false)
    (alwaysAccepts :
      replay.verifyReplay
          (goalMap.judgmentFor goal)
          (association.encodeReceipt {
            goal := goal
            certificate := certificate
          }) = true) :
    False := by
  have rejects :=
    association.replayRejectsWhenGoalRejects goal certificate rejected
  rw [alwaysAccepts] at rejects
  cases rejects

/--
Exact support-root association for the same mandatory Goal/certificate
envelopes retained by replay.
-/
structure SupportGoalAssociation
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (closed : DerivedIntentClosureAt registry observation snapshot carrier)
    (replay : ReplaySystem snapshot carrier)
    (goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment)
    (support : SupportSystem Carrier ImplementationBundle)
    (supportMap :
      SupportJudgmentMap replay.Judgment support.Judgment) where
  rootFor :
    (registry.profile (currentIntentSpec registry snapshot)).Goal →
      support.Node
  rootForInjective :
    ∀ {left right}, rootFor left = rootFor right → left = right
  encodeRootCertificate :
    GoalCertificateEnvelope
      (registry.profile (currentIntentSpec registry snapshot)) →
      support.RootCertificate
  liveExact :
    ∀ supportJudgment,
      support.LiveMandatoryAt supportJudgment ↔
        ∃ goal,
          goal ∈
              (registry.profile
                (currentIntentSpec registry snapshot)).mandatoryGoals ∧
            supportMap.supportFor (goalMap.judgmentFor goal) =
              supportJudgment
  mandatoryListExact :
    support.mandatoryJudgments =
      (registry.profile
        (currentIntentSpec registry snapshot)).mandatoryGoals.map
          (fun goal => supportMap.supportFor (goalMap.judgmentFor goal))
  directSupportExact :
    ∀ goal,
      goal ∈
          (registry.profile
            (currentIntentSpec registry snapshot)).mandatoryGoals →
      support.directSupport carrier.value
          (supportMap.supportFor (goalMap.judgmentFor goal)) =
        [rootFor goal]
  rootWitness :
    ∀ goal,
      goal ∈
          (registry.profile
            (currentIntentSpec registry snapshot)).mandatoryGoals →
      RootWitnessAt support snapshot carrier (rootFor goal)
  rootCertificateExact :
    ∀ goal,
      (mandatory :
        goal ∈
          (registry.profile
            (currentIntentSpec registry snapshot)).mandatoryGoals) →
      (rootWitness goal mandatory).certificate =
        encodeRootCertificate {
          goal := goal
          certificate := closed.certificate goal
        }
  rootClaimExact :
    ∀ observed goal certificate,
      support.RootClaim observed (rootFor goal)
          (encodeRootCertificate {
            goal := goal
            certificate := certificate
          }) ↔
        ((registry.profile
          (currentIntentSpec registry snapshot)).contract goal).claim
          (observation.observe
            (currentIntentSpec registry snapshot) goal observed)
  supportClosure :
    SupportClosureCertificate support snapshot carrier

/-- A mandatory Goal's checked support root carries that Goal's exact claim. -/
theorem SupportGoalAssociation.mandatoryRootClaim
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    {support : SupportSystem Carrier ImplementationBundle}
    {supportMap :
      SupportJudgmentMap replay.Judgment support.Judgment}
    (association :
      SupportGoalAssociation closed replay goalMap support supportMap)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (mandatory :
      goal ∈
        (registry.profile
          (currentIntentSpec registry snapshot)).mandatoryGoals) :
    support.RootClaim carrier.value (association.rootFor goal)
        (association.encodeRootCertificate {
          goal := goal
          certificate := closed.certificate goal
        }) := by
  have exactCertificate :=
    association.rootCertificateExact goal mandatory
  have rootClaim :
      support.RootClaim carrier.value (association.rootFor goal)
        (association.rootWitness goal mandatory).certificate := by
    have claimAtObserved :=
      (association.rootWitness goal mandatory).claim
    rw [(association.rootWitness goal mandatory).carrierBound] at claimAtObserved
    exact claimAtObserved
  rw [exactCertificate] at rootClaim
  exact rootClaim

/--
An unrelated always-true support claim cannot replace the exact Goal claim.
-/
theorem SupportGoalAssociation.unrelatedRootCannotMaskFalseGoal
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    {support : SupportSystem Carrier ImplementationBundle}
    {supportMap :
      SupportJudgmentMap replay.Judgment support.Judgment}
    (association :
      SupportGoalAssociation closed replay goalMap support supportMap)
    (observed : Carrier)
    (goal :
      (registry.profile (currentIntentSpec registry snapshot)).Goal)
    (certificate :
      ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).Certificate)
    (rootClaim :
      support.RootClaim observed (association.rootFor goal)
        (association.encodeRootCertificate {
          goal := goal
          certificate := certificate
        }))
    (goalRefuted :
      ¬ ((registry.profile
        (currentIntentSpec registry snapshot)).contract goal).claim
          (observation.observe
            (currentIntentSpec registry snapshot) goal observed)) :
    False :=
  goalRefuted
    ((association.rootClaimExact observed goal certificate).mp rootClaim)

/-- Distinct Goals cannot share a replay judgment in a lawful binding. -/
theorem GoalJudgmentMap.noCollapse
    {profile : IntentProfile.{u, u, u}}
    {Judgment : Type u}
    (mapping : GoalJudgmentMap profile Judgment)
    {left right : profile.Goal}
    (different : left ≠ right) :
    mapping.judgmentFor left ≠ mapping.judgmentFor right := by
  intro same
  exact different (mapping.injective same)

/-- Distinct replay judgments cannot share a support judgment. -/
theorem SupportJudgmentMap.noCollapse
    {ReplayJudgment SupportJudgment : Type u}
    (mapping : SupportJudgmentMap ReplayJudgment SupportJudgment)
    {left right : ReplayJudgment}
    (different : left ≠ right) :
    mapping.supportFor left ≠ mapping.supportFor right := by
  intro same
  exact different (mapping.injective same)

/-- Distinct Goals cannot share one support root in a lawful association. -/
theorem SupportGoalAssociation.noRootCollapse
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle IntentAddress : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {registry : IntentRegistryKernel AddressRegistry IntentAddress}
    {observation :
      IntentObservationKernel Carrier AddressRegistry IntentAddress registry}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {closed : DerivedIntentClosureAt registry observation snapshot carrier}
    {replay : ReplaySystem snapshot carrier}
    {goalMap :
      GoalJudgmentMap
        (registry.profile (currentIntentSpec registry snapshot))
        replay.Judgment}
    {support : SupportSystem Carrier ImplementationBundle}
    {supportMap :
      SupportJudgmentMap replay.Judgment support.Judgment}
    (association :
      SupportGoalAssociation closed replay goalMap support supportMap)
    {left right :
      (registry.profile (currentIntentSpec registry snapshot)).Goal}
    (different : left ≠ right) :
    association.rootFor left ≠ association.rootFor right := by
  intro same
  exact different (association.rootForInjective same)

end Residua.RCC.IntentSnapshotBinding

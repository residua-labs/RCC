import RCC.FinalizedHeadWindow

/-!
# RCC-46 Conditional Finality Liveness

Safety remains unconditional: two actual RCC-42 global finalizations are
equivalent independently of availability or timing.
Liveness is conditional on five explicit proof-carrying premises:

* quorum availability;
* fair delivery / partial synchrony;
* an eventually stable writer or leader;
* bounded authority reconfiguration; and
* durable signer-lock availability.

This kernel proves only finite, Nat-bounded liveness inside a declared horizon.
It does not claim an unbounded temporal model, physical delivery, quorum
availability, host CAS progress, storage durability, or scheduler fairness.
Concrete adapters must supply those facts.  Missing evidence returns a named
`Await`; the kernel never lowers a threshold and never treats a locally
committed partition as self-finalizing.

The positive result carries an actual RCC-42 `GloballySuccessfulFinalize`,
including the computation equality `fencedFinalize ... = .Ok output`.  Stable
configuration is not a caller predicate: it is RCC-45
`StableConfigEvidence` over a complete authority-transition universe.

Prelude-only Lean 4.14; no Mathlib, admitted proof gaps, declared assumptions,
or kernel-evaluation shortcuts.
-/

namespace Residua.RCC.FinalityLiveness

open Residua.RCC
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow

universe u

/--
The exact canonical writer facts sufficient for the real RCC-42 finalizer to
return `Ok`.
-/
structure CanonicalFinalizeReady
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    (spec : FencedWriterSpec Slot Head)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) : Prop where
  slotBound :
    spec.slotParent request.authorization.proposal.slot =
      request.authorization.proposal.expectedParent
  parentBound :
    request.authorization.proposal.expectedParent = state.canonicalHead
  generationBound : request.expectedGeneration = state.generation
  decisionCommitted :
    state.decisions request.authorization.proposal.slot =
      some request.authorization.proposal.judgment

/-- Build the exact RCC-42 output determined by canonical readiness. -/
def canonicalFinalizeOutput
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation)
    (ready : CanonicalFinalizeReady spec state request) :
    FencedFinalizeOutput spec equivalence state request where
  finality := {
    authorization := request.authorization
    linearizationEvidence := {
      generation := state.generation
      slot := request.authorization.proposal.slot
      parentHead := request.authorization.proposal.expectedParent
      slotBound := rfl
      parentHeadBound := ready.parentBound
    }
    parentBound := ready.parentBound
  }
  authorizationBound := rfl
  generationBound := ready.generationBound
  finalized :=
    ⟨ready.slotBound, ready.parentBound,
      request.authorization.proposal.judgment, ready.decisionCommitted,
      equivalence.refl request.authorization.proposal.judgment⟩

/-- Canonical readiness computes through the actual RCC-42 finalizer. -/
theorem fencedFinalize_of_ready
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation)
    (ready : CanonicalFinalizeReady spec state request) :
    fencedFinalize spec equivalence state request =
      .Ok (canonicalFinalizeOutput spec equivalence state request ready) := by
  unfold fencedFinalize
  rw [dif_pos ready.slotBound, dif_pos ready.parentBound,
    dif_pos ready.generationBound]
  split
  · rename_i decisionEmpty
    have impossible :
        (none : Option Judgment) =
          some request.authorization.proposal.judgment :=
      decisionEmpty.symm.trans ready.decisionCommitted
    contradiction
  · rename_i stored decisionStored
    have storedEq :
        stored = request.authorization.proposal.judgment := by
      apply Option.some.inj
      exact decisionStored.symm.trans ready.decisionCommitted
    subst stored
    split
    · rfl
    · rename_i notEquivalent decisionResult
      exact False.elim
        (notEquivalent
          (equivalence.refl request.authorization.proposal.judgment))

/-- Package canonical readiness as an actual successful RCC-42 computation. -/
def successfulFinalizeOfReady
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation)
    (ready : CanonicalFinalizeReady spec state request) :
    SuccessfulFinalize spec equivalence state request where
  output := canonicalFinalizeOutput spec equivalence state request ready
  accepted := fencedFinalize_of_ready spec equivalence state request ready

/--
A proposition that becomes and remains true inside one finite declared
horizon.  This is the precise strength used here instead of an unbounded
temporal modality.
-/
structure BoundedEventually (predicate : Nat → Prop) (horizon : Nat) where
  bound : Nat
  boundWithin : bound ≤ horizon
  holdsThrough :
    ∀ step, bound ≤ step → step ≤ horizon → predicate step

/--
One finite finality environment.  Each receiver state is proved to be a
projection of one version of the global RCC-42 admission linearizer.  The five
environmental predicates deliberately do not imply progress by themselves;
that separate bridge is `FinalityProgressAdapter`.
-/
structure BoundedFinalityWorld
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) where
  Version : Type u
  linearizer :
    AdmissionLinearizer
      Slot Head Judgment Generation Version spec equivalence
  horizon : Nat
  stateAt : Nat → FencedWriterState Slot Head Judgment Generation
  versionAt : Nat → Version
  canonicalSnapshotAt :
    ∀ step,
      CanonicalWriterSnapshot
        linearizer (versionAt step) (stateAt step)
  Config : Type u
  transitionView : ConfigTransitionView Slot Head Config
  configAt : Nat → Config
  Lawful : Proposal Slot Head Judgment → Prop
  Eligible : Nat → Proposal Slot Head Judgment → Prop
  QuorumAvailable : Nat → Prop
  FairDelivery : Nat → Prop
  ReconfigurationBounded : Nat → Prop
  DurableLockAvailable : Nat → Prop

/--
RCC-45's proof-carrying stability judgment at one step.  The finalized slot and
canonical head come from the exact request/state coordinate; the configuration
and complete transition universe come from the world projection.
-/
def StableConfigAt
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request)
    (step : Nat) : Prop :=
  Nonempty
    (StableConfigEvidence
      world.transitionView
      request.authorization.proposal.slot
      (world.stateAt step).canonicalHead
      (world.configAt step))

/--
The explicit implementation/refinement boundary for finite progress.

`makeReceipt` models the instance-specific protocol progress step.  A receipt
cannot authorize finality directly: `receiptRefinesCanonicalFinalize` must
reduce it to the exact canonical facts checked by RCC-42.  Keeping this adapter
separate makes it impossible to infer finality merely by defining all five
environmental predicates as `True`.
-/
structure FinalityProgressAdapter
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  ProgressReceipt : Nat → Type u
  makeReceipt :
    ∀ step,
      world.Lawful request.authorization.proposal →
      world.Eligible step request.authorization.proposal →
      world.QuorumAvailable step →
      world.FairDelivery step →
      StableConfigAt world step →
      world.ReconfigurationBounded step →
      world.DurableLockAvailable step →
      ProgressReceipt step
  receiptRefinesCanonicalFinalize :
    ∀ step,
      ProgressReceipt step →
      CanonicalFinalizeReady spec (world.stateAt step) request

/-- Proof-carrying quorum-availability premise. -/
structure QuorumAvailabilityCert
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  evidence :
    BoundedEventually world.QuorumAvailable world.horizon

/-- Proof-carrying fair-delivery / partial-synchrony premise. -/
structure FairDeliveryCert
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  evidence :
    BoundedEventually world.FairDelivery world.horizon

/-- Proof-carrying eventually-stable authority-configuration premise. -/
structure EventuallyStableConfigCert
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  evidence :
    BoundedEventually (StableConfigAt world) world.horizon

/-- Proof-carrying bounded-reconfiguration premise. -/
structure BoundedReconfigurationCert
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  evidence :
    BoundedEventually world.ReconfigurationBounded world.horizon

/-- Proof-carrying durable signer-lock availability premise. -/
structure DurableLockAvailabilityCert
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  evidence :
    BoundedEventually world.DurableLockAvailable world.horizon

/-- All five conditional-liveness premises, with no optional field. -/
structure FinalityLivenessPremises
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  quorum : QuorumAvailabilityCert world
  delivery : FairDeliveryCert world
  stableConfig : EventuallyStableConfigCert world
  boundedReconfiguration : BoundedReconfigurationCert world
  durableLock : DurableLockAvailabilityCert world

/-- Lawfulness and eligibility at every point of the finite trace. -/
structure ContinuouslyEligible
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) : Prop where
  lawful : world.Lawful request.authorization.proposal
  eligible :
    ∀ step, step ≤ world.horizon →
      world.Eligible step request.authorization.proposal

/-- Optional evidence extracted from the external runtime boundary. -/
structure FinalityLivenessEvidence
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  quorum : Option (QuorumAvailabilityCert world)
  delivery : Option (FairDeliveryCert world)
  stableConfig : Option (EventuallyStableConfigCert world)
  boundedReconfiguration : Option (BoundedReconfigurationCert world)
  durableLock : Option (DurableLockAvailabilityCert world)

/-- Every missing premise has its own stable wake reason. -/
inductive FinalityWake
  | finalityQuorumUnavailable
  | finalityDeliveryPending
  | finalityStableConfigPending
  | finalityReconfigurationPending
  | finalityDurableLockUnavailable
  deriving DecidableEq, Repr

/-- Pure RCC-46 has no refusal constructor; it either proves or waits. -/
inductive NoFinalityResidue

/-- Mechanically derive the mandatory premise product, or a named wait. -/
def deriveFinalityLivenessPremises
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    {world : BoundedFinalityWorld spec equivalence request}
    (evidence : FinalityLivenessEvidence world) :
    OpResult
      (FinalityLivenessPremises world) FinalityWake NoFinalityResidue :=
  match evidence.quorum with
  | none => .Await .finalityQuorumUnavailable
  | some quorum =>
      match evidence.delivery with
      | none => .Await .finalityDeliveryPending
      | some delivery =>
          match evidence.stableConfig with
          | none => .Await .finalityStableConfigPending
          | some stableConfig =>
              match evidence.boundedReconfiguration with
              | none => .Await .finalityReconfigurationPending
              | some boundedReconfiguration =>
                  match evidence.durableLock with
                  | none => .Await .finalityDurableLockUnavailable
                  | some durableLock =>
                      .Ok {
                        quorum := quorum
                        delivery := delivery
                        stableConfig := stableConfig
                        boundedReconfiguration := boundedReconfiguration
                        durableLock := durableLock
                      }

/-- Canonical witness point: the endpoint of the declared finite trace. -/
def finalityReadyStep
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    {world : BoundedFinalityWorld spec equivalence request}
    (_premises : FinalityLivenessPremises world) : Nat :=
  world.horizon

/-- The joint ready step stays inside the declared finite trace. -/
theorem finalityReadyStep_within_horizon
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    {world : BoundedFinalityWorld spec equivalence request}
    (premises : FinalityLivenessPremises world) :
    finalityReadyStep premises ≤ world.horizon := by
  exact Nat.le_refl _

/-- Finite eventual-finality witness carrying the actual RCC-42 success. -/
structure BoundedFinalityWitness
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request) where
  step : Nat
  withinHorizon : step ≤ world.horizon
  success :
    GloballySuccessfulFinalize
      world.linearizer (world.versionAt step) (world.stateAt step) request

/--
RCC-46 finite conditional liveness.  The theorem is constructive over supplied
bounded evidence; it does not synthesize or assume an infinite temporal run.
-/
def conditional_finality_liveness
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request)
    (progress : FinalityProgressAdapter world)
    (continuous : ContinuouslyEligible world)
    (premises : FinalityLivenessPremises world) :
    BoundedFinalityWitness world := by
  let step := finalityReadyStep premises
  have withinHorizon : step ≤ world.horizon := by
    exact finalityReadyStep_within_horizon premises
  have quorumReady :=
    premises.quorum.evidence.holdsThrough
      step premises.quorum.evidence.boundWithin withinHorizon
  have deliveryReady :=
    premises.delivery.evidence.holdsThrough
      step premises.delivery.evidence.boundWithin withinHorizon
  have stableConfig :=
    premises.stableConfig.evidence.holdsThrough
      step premises.stableConfig.evidence.boundWithin withinHorizon
  have reconfigurationReady :=
    premises.boundedReconfiguration.evidence.holdsThrough
      step premises.boundedReconfiguration.evidence.boundWithin withinHorizon
  have lockReady :=
    premises.durableLock.evidence.holdsThrough
      step premises.durableLock.evidence.boundWithin withinHorizon
  have progressReceipt :=
    progress.makeReceipt
      step continuous.lawful (continuous.eligible step withinHorizon)
        quorumReady deliveryReady stableConfig reconfigurationReady lockReady
  have ready :=
    progress.receiptRefinesCanonicalFinalize step progressReceipt
  have localSuccess :=
    successfulFinalizeOfReady
      spec equivalence (world.stateAt step) request ready
  exact {
    step := step
    withinHorizon := withinHorizon
    success := {
      snapshot := world.canonicalSnapshotAt step
      localSuccess := localSuccess
    }
  }

/--
Propositional form of finite conditional liveness.  The witness is bounded by
the declared horizon and is an actual successful RCC-42 finalization, not an
opaque `Closed` assertion.
-/
theorem conditional_finality_liveness_theorem
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request)
    (progress : FinalityProgressAdapter world)
    (continuous : ContinuouslyEligible world)
    (premises : FinalityLivenessPremises world) :
    ∃ witness : BoundedFinalityWitness world,
      witness.step ≤ world.horizon ∧
      fencedFinalize spec equivalence (world.stateAt witness.step) request =
        .Ok witness.success.localSuccess.output := by
  let witness :=
    conditional_finality_liveness world progress continuous premises
  exact
    ⟨witness, witness.withinHorizon,
      witness.success.localSuccess.accepted⟩

/--
Executable finite boundary: complete evidence yields actual finality; every
missing premise remains a named wait.
-/
def runConditionalFinality
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (world : BoundedFinalityWorld spec equivalence request)
    (progress : FinalityProgressAdapter world)
    (continuous : ContinuouslyEligible world)
    (evidence : FinalityLivenessEvidence world) :
    OpResult (BoundedFinalityWitness world) FinalityWake NoFinalityResidue :=
  match deriveFinalityLivenessPremises evidence with
  | .Ok premises =>
      .Ok
        (conditional_finality_liveness
          world progress continuous premises)
  | .Await wake => .Await wake
  | .Refuse residue => nomatch residue
  | .ResourceExhausted residue => nomatch residue

/--
The local RCC-42 lemma retained for one exact receiver snapshot.  It is not the
public cross-snapshot finality theorem.
-/
theorem local_finality_safety_unconditional
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {state : FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (first : SuccessfulFinalize spec equivalence state firstRequest)
    (second : SuccessfulFinalize spec equivalence state secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot) :
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment :=
  successful_finalizes_same_slot_equivalent
    spec equivalence state first second sameSlot

/--
RCC-46 safety is unconditional and global: no liveness premise occurs in this
theorem, and the two successful finalizations may come from different receiver
states and different canonical versions.  Both must refine the same global
RCC-42 admission linearizer and target the same parent/slot coordinates.
-/
theorem finality_safety_unconditional
    {Slot Head Judgment Generation : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {spec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {Version : Type u}
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version spec equivalence)
    {firstVersion secondVersion : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (first :
      GloballySuccessfulFinalize
        linearizer firstVersion firstState firstRequest)
    (second :
      GloballySuccessfulFinalize
        linearizer secondVersion secondState secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot)
    (sameParent :
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent) :
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment :=
  global_finalizes_same_slot_parent_equivalent
    linearizer first second sameSlot sameParent

end Residua.RCC.FinalityLiveness

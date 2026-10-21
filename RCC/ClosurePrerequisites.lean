import RCC.FacetSnapshot
import RCC.FinalizedHeadWindow

/-!
# RCC relative-closure prerequisites

This module binds three existing RCC kernels to one FC-1 snapshot and carrier:

* RCC-45 finalized-head/source-window evidence;
* RCC-31 effect settlement; and
* RCC-18 primitive operational totality.

The bridges contain no caller-supplied `closed` Boolean and no vacuous `True`
field.  Source and effect evidence must name the exact FC-1 epoch/head/window,
while primitive policy and implementation are projected from the exact current
implementation-bundle coordinate.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.ClosurePrerequisites

open Residua.RCC
open Residua.RCC.FacetSnapshot
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.EffectSettlement

universe u

/--
The source-window coordinate carried by FC-1.  It contains the same three
semantic fields used by `FinalizedClosureEvidence`; the finalized head remains
the separate FC-1 history-head coordinate.
-/
structure FinalizedSourceWindow
    (SourceAuthority Watermark Partition : Type u) where
  sourceAuthority : SourceAuthority
  watermark : Watermark
  priorPartitions : List Partition

/-- Project RCC-45 evidence to its exact FC-1 source-window coordinate. -/
def finalizedSourceWindow
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (evidence :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)) :
    FinalizedSourceWindow SourceAuthority Watermark Partition where
  sourceAuthority := evidence.snapshot.sourceAuthority
  watermark := evidence.snapshot.watermark
  priorPartitions := evidence.snapshot.priorPartitions

/--
RCC-45 evidence bound to the exact FC-1 epoch, canonical head, and source
window.  The epoch is the epoch already carried by the admission environment's
settlement snapshot; it is not a parallel caller label.
-/
structure FinalizedClosureAt
    {Epoch Head AssumptionRoot AddressRegistry FailureModel ProposalWindow
      ImplementationBundle Slot Judgment Generation EffectSlot Occurrence
      FailureName EventQ Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry
          (FinalizedSourceWindow SourceAuthority Watermark Partition)
          FailureModel ProposalWindow ImplementationBundle}
    (snapshot : SealedSnapshot sealSpec)
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop} where
  evidence :
    FinalizedClosureEvidence
      (environment := environment)
      (history := history)
      (ConfigLawful := ConfigLawful)
      (protocol := protocol)
      (ConfigStable := ConfigStable)
  epochExact :
    environment.effectSnapshot.epoch = snapshot.coordinates.epoch
  headExact :
    evidence.snapshot.head = snapshot.coordinates.historyHead
  sourceWindowExact :
    finalizedSourceWindow evidence = snapshot.coordinates.sourceWindow

/--
The finalized prerequisite and FC-1 carrier agree on epoch, canonical head,
and source window.  All three equalities are derived from indexed certificates.
-/
theorem finalized_closure_fc1_exact
    {Carrier Epoch Head AssumptionRoot AddressRegistry FailureModel ProposalWindow
      ImplementationBundle Slot Judgment Generation EffectSlot Occurrence
      FailureName EventQ Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry
          (FinalizedSourceWindow SourceAuthority Watermark Partition)
          FailureModel ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry
          (FinalizedSourceWindow SourceAuthority Watermark Partition)
          FailureModel ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    (carrier : SnapshotCarrier projection snapshot)
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (closed :
      FinalizedClosureAt
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)
        snapshot) :
    projection.epoch carrier.value = environment.effectSnapshot.epoch ∧
      projection.historyHead carrier.value = closed.evidence.snapshot.head ∧
      projection.sourceWindow carrier.value =
        finalizedSourceWindow closed.evidence := by
  constructor
  · exact carrier.epochBound.trans closed.epochExact.symm
  · constructor
    · exact carrier.historyHeadBound.trans closed.headExact.symm
    · exact carrier.sourceWindowBound.trans closed.sourceWindowExact.symm

/--
One RCC-45 evidence object cannot be transported to a different FC-1 history
head.  A new head requires newly bound evidence.
-/
theorem finalized_closure_cannot_cross_head
    {Epoch Head AssumptionRoot AddressRegistry FailureModel ProposalWindow
      ImplementationBundle Slot Judgment Generation EffectSlot Occurrence
      FailureName EventQ Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry
          (FinalizedSourceWindow SourceAuthority Watermark Partition)
          FailureModel ProposalWindow ImplementationBundle}
    {first second : SealedSnapshot sealSpec}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (atFirst :
      FinalizedClosureAt
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)
        first)
    (differentHead :
      first.coordinates.historyHead ≠ second.coordinates.historyHead) :
    ¬ ∃ atSecond :
        FinalizedClosureAt
          (environment := environment)
          (history := history)
          (ConfigLawful := ConfigLawful)
          (protocol := protocol)
          (ConfigStable := ConfigStable)
          second,
        atSecond.evidence = atFirst.evidence := by
  rintro ⟨atSecond, sameEvidence⟩
  apply differentHead
  have secondHead :
      atFirst.evidence.snapshot.head =
        second.coordinates.historyHead := by
    rw [← sameEvidence]
    exact atSecond.headExact
  exact atFirst.headExact.symm.trans secondHead

/--
Without a finalized-head certificate, the existing RCC-45 executable gate
returns its named wait residue.  Missing evidence cannot become eligibility.
-/
theorem missing_finalized_head_awaits
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    [DecidableEq Slot] [DecidableEq Config] [DecidableEq Head]
    [DecidableEq Generation] [DecidableEq SourceAuthority]
    [DecidableEq Watermark] [DecidableEq Partition]
    (snapshot :
      ClosureSnapshot Slot Config Head SourceAuthority Watermark Partition)
    (finalizedWindow? :
      Option (FinalizedWindowEnvelope protocol ConfigStable))
    (stableConfig? :
      Option
        (StableConfigEvidence
          snapshot.transitionView snapshot.slot snapshot.head snapshot.config)) :
    assessFinalizedClosure
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable)
        snapshot none finalizedWindow? stableConfig? =
      .await .sourceWindowNotFinalized :=
  rfl

/--
An RCC-31 effect snapshot bound to the exact FC-1 epoch/head and accompanied by
the existing proof that every declared external effect is settled.
-/
structure EffectSettlementAt
    {Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle EffectSlot Generation Occurrence
      FailureName : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    (snapshot : SealedSnapshot sealSpec)
    (effects :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (InScopeEffect :
      ExternalEffect Occurrence Head EffectSlot → Prop) :
    Prop where
  epochExact : effects.epoch = snapshot.coordinates.epoch
  headExact : effects.head = snapshot.coordinates.historyHead
  coverage :
    CoverageCertificate InScopeEffect effects.externalEffects
  closed : EpochEffectClosed effects

/-- The effect prerequisite and FC-1 carrier name the same epoch and head. -/
theorem effect_settlement_fc1_exact
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle EffectSlot Generation Occurrence
      FailureName : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    (carrier : SnapshotCarrier projection snapshot)
    {effects :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {InScopeEffect :
      ExternalEffect Occurrence Head EffectSlot → Prop}
    (settled : EffectSettlementAt snapshot effects InScopeEffect) :
    projection.epoch carrier.value = effects.epoch ∧
      projection.historyHead carrier.value = effects.head := by
  constructor
  · exact carrier.epochBound.trans settled.epochExact.symm
  · exact carrier.historyHeadBound.trans settled.headExact.symm

/-- Every declared external effect has its exact fenced settled receipt. -/
theorem EffectSettlementAt.every_effect_settled
    {Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle EffectSlot Generation Occurrence
      FailureName : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {effects :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {InScopeEffect :
      ExternalEffect Occurrence Head EffectSlot → Prop}
    (settled : EffectSettlementAt snapshot effects InScopeEffect) :
    ∀ effect, effect ∈ effects.externalEffects →
      ∃ observation receipt,
        FencedSettledReceipt effects effect observation receipt :=
  epoch_effect_closed_every_external_effect_settled effects settled.closed

/-- Every in-scope effect is enumerated and has a fenced settled receipt. -/
theorem EffectSettlementAt.every_in_scope_effect_settled
    {Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle EffectSlot Generation Occurrence
      FailureName : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {effects :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {InScopeEffect :
      ExternalEffect Occurrence Head EffectSlot → Prop}
    (settled : EffectSettlementAt snapshot effects InScopeEffect) :
    ∀ effect, InScopeEffect effect →
      ∃ observation receipt,
        FencedSettledReceipt effects effect observation receipt := by
  intro effect inScope
  exact
    settled.closed effect
      (settled.coverage.complete effect inScope)

/--
Every declared effect excludes both effect/history split directions and a
pending compensation.
-/
theorem EffectSettlementAt.excludes_unsettled
    {Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle EffectSlot Generation Occurrence
      FailureName : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {effects :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {InScopeEffect :
      ExternalEffect Occurrence Head EffectSlot → Prop}
    (settled : EffectSettlementAt snapshot effects InScopeEffect) :
    ∀ effect, effect ∈ effects.externalEffects →
      ∃ observation receipt,
        effects.observe effect.occurrence = some observation ∧
        observation.receipt = some receipt ∧
        ¬ EffectAppliedUnrecorded observation ∧
        ¬ EffectRecordedNotApplied observation receipt ∧
        ¬ CompensationStillPending receipt :=
  epoch_effect_closed_excludes_unsettled_phases effects settled.closed

/--
The epoch-specific projection from FC-1's implementation-bundle coordinate to
the exact RCC-18 resource policy and primitive family.
-/
structure PrimitiveImplementationProjection
    (ImplementationBundle : Type u) where
  policy : ImplementationBundle → ResourcePolicy
  family : ImplementationBundle → PrimitiveFamily.{u, u, u, u}

/--
One concrete host-adapter invocation after the host boundary has returned.  A
hung call cannot inhabit this structure: adapters must first convert timeout,
resource limit, or caught exception into `OperationalObservation`.
-/
structure ActualPrimitiveInvocation
    (family : PrimitiveFamily.{u, u, u, u}) where
  primitive : PrimitiveKind
  contract : ResourceContract
  input : family.Input primitive
  observed :
    OperationalObservation
      (family.Output primitive) family.Wake family.Residue
  result :
    OpResult (family.Output primitive) family.Wake family.Residue

/--
Proof that the actual returned invocation is exactly the current RCC-18
implementation: its boundary observation equals `family.observe`, and its
reported result is the classification of that observed boundary value.
-/
structure ActualInvocationRefinementAt
    (family : PrimitiveFamily.{u, u, u, u}) where
  invocation : ActualPrimitiveInvocation family
  observationExact :
    invocation.observed =
      family.observe
        invocation.primitive invocation.contract invocation.input
  resultExact :
    invocation.result = classify invocation.observed

/--
RCC-18 lawfulness for the primitive family projected from the exact current
FC-1 carrier.  A caller cannot pair the current carrier with another family.
-/
structure PrimitiveTotalityAt
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {carrierProjection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    (carrier : SnapshotCarrier carrierProjection snapshot)
    (implementation :
      PrimitiveImplementationProjection ImplementationBundle) where
  lawful :
    LawfulPrimitiveFamily
      (implementation.policy
        (carrierProjection.implementationBundle carrier.value))
      (implementation.family
        (carrierProjection.implementationBundle carrier.value))
  actual :
    ActualInvocationRefinementAt
      (implementation.family
        (carrierProjection.implementationBundle carrier.value))

/-- The primitive bridge is bound to the current FC-1 implementation bundle. -/
theorem primitive_implementation_fc1_exact
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {carrierProjection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    (carrier : SnapshotCarrier carrierProjection snapshot) :
    carrierProjection.implementationBundle carrier.value =
      snapshot.coordinates.implementationBundle :=
  carrier.implementationBundleBound

/--
The exact current primitive implementation returns one of the four RCC-18
branches, and a policy-insufficient resource contract is explicitly reported
as resource exhaustion.
-/
theorem PrimitiveTotalityAt.four_way
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {carrierProjection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier carrierProjection snapshot}
    {implementation :
      PrimitiveImplementationProjection ImplementationBundle}
    (total : PrimitiveTotalityAt carrier implementation)
    (primitive : PrimitiveKind)
    (contract : ResourceContract)
    (input :
      (implementation.family
        (carrierProjection.implementationBundle carrier.value)).Input primitive) :
    let policy :=
      implementation.policy
        (carrierProjection.implementationBundle carrier.value)
    let family :=
      implementation.family
        (carrierProjection.implementationBundle carrier.value)
    ((∃ value, execute family primitive contract input = .Ok value) ∨
        (∃ wake, execute family primitive contract input = .Await wake) ∨
        (∃ residue, execute family primitive contract input = .Refuse residue) ∨
        (∃ residue,
          execute family primitive contract input = .ResourceExhausted residue)) ∧
      (policy.insufficient primitive contract →
        ∃ residue,
          execute family primitive contract input =
            .ResourceExhausted residue) := by
  exact
    rcc18_parametric_boundary
      (implementation.policy
        (carrierProjection.implementationBundle carrier.value))
      (implementation.family
        (carrierProjection.implementationBundle carrier.value))
      total.lawful primitive contract input

/--
The actual current invocation finite-returns through the exact four-way
boundary and equals `execute` for its projected primitive, resource contract,
and input.
-/
theorem PrimitiveTotalityAt.actual_result_exact
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {carrierProjection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier carrierProjection snapshot}
    {implementation :
      PrimitiveImplementationProjection ImplementationBundle}
    (total : PrimitiveTotalityAt carrier implementation) :
    let family :=
      implementation.family
        (carrierProjection.implementationBundle carrier.value)
    total.actual.invocation.result =
      execute family
        total.actual.invocation.primitive
        total.actual.invocation.contract
        total.actual.invocation.input := by
  exact total.actual.resultExact.trans
    (congrArg classify total.actual.observationExact)

/-- The actual invocation has one of the four and only four RCC-18 results. -/
theorem PrimitiveTotalityAt.actual_four_way
    {Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
      ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {carrierProjection :
      CarrierProjection
        Carrier Epoch Head AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier carrierProjection snapshot}
    {implementation :
      PrimitiveImplementationProjection ImplementationBundle}
    (total : PrimitiveTotalityAt carrier implementation) :
    (∃ value, total.actual.invocation.result = .Ok value) ∨
      (∃ wake, total.actual.invocation.result = .Await wake) ∨
      (∃ residue, total.actual.invocation.result = .Refuse residue) ∨
      (∃ residue,
        total.actual.invocation.result = .ResourceExhausted residue) :=
  OpResult.exhaustive total.actual.invocation.result

end Residua.RCC.ClosurePrerequisites

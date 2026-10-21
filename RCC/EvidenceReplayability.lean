import RCC.FacetSnapshot

/-!
# RCC evidence replayability

Current authority requires more than historical validity.  Every mandatory
judgment is bound to an actual archive object whose bytes re-hash, decode to
the expected receipt, bind the common FC-1 snapshot coordinates, retain a
well-founded transitive dependency closure, and pass the replay verifier.

The mandatory universe is finite, nonempty, and sealed in both directions.
Consequently an empty or partial list cannot manufacture vacuous closure.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.EvidenceReplayability

open Residua.RCC.FacetSnapshot

universe u

structure ReplaySystem
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) where
  Judgment : Type u
  Receipt : Type u
  Object : Type u
  ObjectQ : Type u

  mandatoryJudgments : List Judgment
  LiveMandatoryAt : Judgment → Prop

  receiptFor : Judgment → Receipt
  receiptObjectQ : Receipt → ObjectQ
  lookup : ObjectQ → Option Object
  objectQ : Object → ObjectQ
  objectBytes : Object → String
  digest : String → ObjectQ
  decodeReceipt : Object → Option Receipt
  objectDependencies : Object → List ObjectQ
  objectRank : ObjectQ → Nat

  receiptEpoch : Receipt → Epoch
  receiptHistoryHead : Receipt → HistoryHead
  receiptAssumptionRoot : Receipt → AssumptionRoot
  receiptAddressRegistry : Receipt → AddressRegistry
  receiptSourceWindow : Receipt → SourceWindow
  receiptFailureModel : Receipt → FailureModel
  receiptProposalWindow : Receipt → ProposalWindow
  receiptImplementationBundle : Receipt → ImplementationBundle

  verifyReplay : Judgment → Receipt → Bool

/-- A nonempty exact enumeration of the mandatory judgment universe. -/
structure MandatoryJudgmentUniverseSeal
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (K : ReplaySystem snapshot carrier) : Prop where
  nonempty : K.mandatoryJudgments ≠ []
  declaredSound :
    ∀ judgment, judgment ∈ K.mandatoryJudgments →
      K.LiveMandatoryAt judgment
  declaredComplete :
    ∀ judgment, K.LiveMandatoryAt judgment →
      judgment ∈ K.mandatoryJudgments

/--
Proof-carrying transitive archive closure.

Every referenced object must be present under its exact address, its bytes
must re-hash to that address, and every dependency has strictly smaller rank.
The recursive premise therefore cannot be satisfied by a missing dependency
or by a circular support graph.
-/
inductive ArchiveObjectClosure
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (K : ReplaySystem snapshot carrier) : K.ObjectQ → Type u
  | checked
      (address : K.ObjectQ)
      (object : K.Object)
      (found : K.lookup address = some object)
      (addressBound : K.objectQ object = address)
      (rehash : K.digest (K.objectBytes object) = address)
      (dependenciesLower :
        ∀ dependency,
          dependency ∈ K.objectDependencies object →
            K.objectRank dependency < K.objectRank address)
      (dependenciesClosed :
        ∀ dependency,
          dependency ∈ K.objectDependencies object →
            ArchiveObjectClosure K dependency) :
      ArchiveObjectClosure K address

/-- A closed archive address always resolves to actual retained bytes. -/
theorem archive_object_available
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {K : ReplaySystem snapshot carrier}
    {address : K.ObjectQ}
    (closed : ArchiveObjectClosure K address) :
    ∃ object, K.lookup address = some object := by
  cases closed with
  | checked _ object found _ _ _ _ =>
      exact ⟨object, found⟩

/-- Current replayability of one mandatory judgment at the exact FC-1 index. -/
structure ReplayableJudgmentAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (K : ReplaySystem snapshot carrier)
    (judgment : K.Judgment) where
  mandatory : K.LiveMandatoryAt judgment
  object : K.Object
  found :
    K.lookup (K.receiptObjectQ (K.receiptFor judgment)) = some object
  addressBound :
    K.objectQ object = K.receiptObjectQ (K.receiptFor judgment)
  rehash :
    K.digest (K.objectBytes object) =
      K.receiptObjectQ (K.receiptFor judgment)
  decoded :
    K.decodeReceipt object = some (K.receiptFor judgment)
  epochBound :
    K.receiptEpoch (K.receiptFor judgment) = snapshot.coordinates.epoch
  historyHeadBound :
    K.receiptHistoryHead (K.receiptFor judgment) =
      snapshot.coordinates.historyHead
  assumptionRootBound :
    K.receiptAssumptionRoot (K.receiptFor judgment) =
      snapshot.coordinates.assumptionRoot
  addressRegistryBound :
    K.receiptAddressRegistry (K.receiptFor judgment) =
      snapshot.coordinates.addressRegistry
  sourceWindowBound :
    K.receiptSourceWindow (K.receiptFor judgment) =
      snapshot.coordinates.sourceWindow
  failureModelBound :
    K.receiptFailureModel (K.receiptFor judgment) =
      snapshot.coordinates.failureModel
  proposalWindowBound :
    K.receiptProposalWindow (K.receiptFor judgment) =
      snapshot.coordinates.proposalWindow
  implementationBound :
    K.receiptImplementationBundle (K.receiptFor judgment) =
      snapshot.coordinates.implementationBundle
  archiveClosed :
    ArchiveObjectClosure K (K.receiptObjectQ (K.receiptFor judgment))
  replayAccepted :
    K.verifyReplay judgment (K.receiptFor judgment) = true

/-- All and only live mandatory judgments remain replayable now. -/
structure EvidenceReplayabilityAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (K : ReplaySystem snapshot carrier) where
  universeSeal : MandatoryJudgmentUniverseSeal K
  replayable :
    ∀ judgment, K.LiveMandatoryAt judgment →
      ReplayableJudgmentAt K judgment

def mandatoryJudgmentReplayable
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {K : ReplaySystem snapshot carrier}
    (closure : EvidenceReplayabilityAt K)
    (judgment : K.Judgment)
    (mandatory : K.LiveMandatoryAt judgment) :
    ReplayableJudgmentAt K judgment :=
  closure.replayable judgment mandatory

theorem replayable_has_archive_object
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {K : ReplaySystem snapshot carrier}
    {judgment : K.Judgment}
    (replayable : ReplayableJudgmentAt K judgment) :
    ∃ object,
      K.lookup (K.receiptObjectQ (K.receiptFor judgment)) = some object := by
  exact ⟨replayable.object, replayable.found⟩

theorem replayable_binds_current_snapshot
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {K : ReplaySystem snapshot carrier}
    {judgment : K.Judgment}
    (replayable : ReplayableJudgmentAt K judgment) :
    K.receiptEpoch (K.receiptFor judgment) = snapshot.coordinates.epoch ∧
      K.receiptHistoryHead (K.receiptFor judgment) =
        snapshot.coordinates.historyHead ∧
      K.receiptAssumptionRoot (K.receiptFor judgment) =
        snapshot.coordinates.assumptionRoot ∧
      K.receiptAddressRegistry (K.receiptFor judgment) =
        snapshot.coordinates.addressRegistry ∧
      K.receiptSourceWindow (K.receiptFor judgment) =
        snapshot.coordinates.sourceWindow ∧
      K.receiptFailureModel (K.receiptFor judgment) =
        snapshot.coordinates.failureModel ∧
      K.receiptProposalWindow (K.receiptFor judgment) =
        snapshot.coordinates.proposalWindow ∧
      K.receiptImplementationBundle (K.receiptFor judgment) =
        snapshot.coordinates.implementationBundle :=
  ⟨replayable.epochBound, replayable.historyHeadBound,
    replayable.assumptionRootBound, replayable.addressRegistryBound,
    replayable.sourceWindowBound, replayable.failureModelBound,
    replayable.proposalWindowBound, replayable.implementationBound⟩

theorem empty_mandatory_universe_refused
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    (K : ReplaySystem snapshot carrier)
    (empty : K.mandatoryJudgments = []) :
    ¬ MandatoryJudgmentUniverseSeal K :=
  fun universeSeal => universeSeal.nonempty empty

end Residua.RCC.EvidenceReplayability

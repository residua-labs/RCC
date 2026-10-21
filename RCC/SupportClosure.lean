import RCC.FacetSnapshot

/-!
# RCC support closure

Support is derived from checked certificates, never from a caller supplied
`verified := True` proposition.  Required nodes are likewise derived from a
sealed, nonempty live-mandatory universe and its exact transitive support
projection; an instance cannot choose an unrelated empty `RequiredAt`.

Every certificate and closure token is indexed by one `SealedSnapshot` and
its exact `SnapshotCarrier`.  Rule premises strictly descend in rank.
Recursive SCCs must therefore first be replaced by one externally checked
joint-discharge rule.

Prelude-only Lean 4.14; no Mathlib or proof placeholders.
-/

namespace Residua.RCC.SupportClosure

open Residua.RCC.FacetSnapshot

universe u

/-- Checked support semantics at one concrete FC-1 carrier. -/
structure SupportSystem
    (Carrier ImplementationBundle : Type u) where
  Node : Type u
  Judgment : Type u
  Verifier : Type u
  RootCertificate : Type u
  RuleCertificate : Type u

  rank : Node → Nat
  premises : Node → List Node

  mandatoryJudgments : List Judgment
  LiveMandatoryAt : Judgment → Prop
  directSupport : Carrier → Judgment → List Node

  expectedVerifier : Carrier → Verifier
  rootVerifier : RootCertificate → Verifier
  ruleVerifier : RuleCertificate → Verifier
  rootImplementation : RootCertificate → ImplementationBundle
  ruleImplementation : RuleCertificate → ImplementationBundle

  RootClaim : Carrier → Node → RootCertificate → Prop
  RuleClaim : Carrier → Node → RuleCertificate → Prop
  verifyRoot : Carrier → Node → RootCertificate → Bool
  verifyRule : Carrier → Node → RuleCertificate → Bool
  rootSound :
    ∀ carrier node certificate,
      verifyRoot carrier node certificate = true →
        RootClaim carrier node certificate
  ruleSound :
    ∀ carrier node certificate,
      verifyRule carrier node certificate = true →
        RuleClaim carrier node certificate

/--
Mechanical transitive support projection from a live mandatory judgment.
There is no instance field that can independently declare a node required.
-/
inductive RequiredNodeOrigin
    {Carrier ImplementationBundle : Type u}
    (system : SupportSystem Carrier ImplementationBundle)
    (carrier : Carrier) : system.Node → Prop
  | direct
      (judgment : system.Judgment)
      (node : system.Node)
      (live : system.LiveMandatoryAt judgment)
      (selected : node ∈ system.directSupport carrier judgment) :
      RequiredNodeOrigin system carrier node
  | dependency
      (parent node : system.Node)
      (parentRequired : RequiredNodeOrigin system carrier parent)
      (selected : node ∈ system.premises parent) :
      RequiredNodeOrigin system carrier node

/-- `RequiredAt` is an abbreviation for the transitive source projection. -/
abbrev RequiredAt
    {Carrier ImplementationBundle : Type u}
    (system : SupportSystem Carrier ImplementationBundle)
    (carrier : Carrier)
    (node : system.Node) : Prop :=
  RequiredNodeOrigin system carrier node

/--
Exact live-mandatory universe and its nonempty direct support adapter.
`liveExists` rules out vacuous closure; `sourceNonempty` prevents a live
mandatory judgment from projecting no support obligations.
-/
structure MandatorySupportProjectionAt
    {Carrier ImplementationBundle : Type u}
    (system : SupportSystem Carrier ImplementationBundle)
    (carrier : Carrier) where
  liveExists : ∃ judgment, system.LiveMandatoryAt judgment
  declaredSound :
    ∀ judgment,
      judgment ∈ system.mandatoryJudgments →
        system.LiveMandatoryAt judgment
  declaredComplete :
    ∀ judgment,
      system.LiveMandatoryAt judgment →
        judgment ∈ system.mandatoryJudgments
  sourceNonempty :
    ∀ judgment,
      system.LiveMandatoryAt judgment →
        system.directSupport carrier judgment ≠ []

/-- A sealed live-mandatory universe is necessarily nonempty. -/
theorem MandatorySupportProjectionAt.mandatoryNonempty
    {Carrier ImplementationBundle : Type u}
    {system : SupportSystem Carrier ImplementationBundle}
    {carrier : Carrier}
    (projection : MandatorySupportProjectionAt system carrier) :
    system.mandatoryJudgments ≠ [] := by
  intro empty
  obtain ⟨judgment, live⟩ := projection.liveExists
  have member := projection.declaredComplete judgment live
  rw [empty] at member
  cases member

/-- A sealed mandatory support projection has at least one required node. -/
theorem MandatorySupportProjectionAt.requiredExists
    {Carrier ImplementationBundle : Type u}
    {system : SupportSystem Carrier ImplementationBundle}
    {carrier : Carrier}
    (projection : MandatorySupportProjectionAt system carrier) :
    ∃ node, RequiredAt system carrier node := by
  obtain ⟨judgment, live⟩ := projection.liveExists
  have nonempty := projection.sourceNonempty judgment live
  cases selected : system.directSupport carrier judgment with
  | nil =>
      exact (nonempty selected).elim
  | cons node rest =>
      exact
        ⟨node,
          .direct judgment node live
            (by rw [selected]; exact List.Mem.head rest)⟩

/--
Checked root certificate bound to the exact snapshot, carrier, verifier, and
FC-1 implementation coordinate.
-/
structure RootWitnessAt
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
    (system : SupportSystem Carrier ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    (node : system.Node) where
  observedSnapshot : SealedSnapshot sealSpec
  observedCarrier : Carrier
  certificate : system.RootCertificate
  snapshotBound : observedSnapshot = snapshot
  carrierBound : observedCarrier = carrier.value
  verifierBound :
    system.rootVerifier certificate =
      system.expectedVerifier observedCarrier
  implementationBound :
    system.rootImplementation certificate =
      snapshot.coordinates.implementationBundle
  accepted :
    system.verifyRoot observedCarrier node certificate = true
  claim : system.RootClaim observedCarrier node certificate
  claimDerived :
    claim = system.rootSound observedCarrier node certificate accepted

/--
Checked derivation rule at the same exact coordinates.  Premises are schema
data and strictly descend.
-/
structure RuleWitnessAt
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
    (system : SupportSystem Carrier ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    (node : system.Node) where
  observedSnapshot : SealedSnapshot sealSpec
  observedCarrier : Carrier
  certificate : system.RuleCertificate
  snapshotBound : observedSnapshot = snapshot
  carrierBound : observedCarrier = carrier.value
  verifierBound :
    system.ruleVerifier certificate =
      system.expectedVerifier observedCarrier
  implementationBound :
    system.ruleImplementation certificate =
      snapshot.coordinates.implementationBundle
  accepted :
    system.verifyRule observedCarrier node certificate = true
  claim : system.RuleClaim observedCarrier node certificate
  claimDerived :
    claim = system.ruleSound observedCarrier node certificate accepted
  premisesNonempty : system.premises node ≠ []
  premisesLower :
    ∀ premise,
      premise ∈ system.premises node →
        system.rank premise < system.rank node

/-- Recursively grounded support at one exact FC-1 index. -/
inductive SupportClosureAt
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
    (system : SupportSystem Carrier ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) :
    system.Node → Prop
  | root
      (node : system.Node)
      (witness : RootWitnessAt system snapshot carrier node) :
      SupportClosureAt system snapshot carrier node
  | derived
      (node : system.Node)
      (witness : RuleWitnessAt system snapshot carrier node)
      (premisesClosed :
        ∀ premise,
          premise ∈ system.premises node →
            SupportClosureAt system snapshot carrier premise) :
      SupportClosureAt system snapshot carrier node

/-- Exact finite enumeration of the mechanically derived required universe. -/
structure RequiredNodeSeal
    {Carrier ImplementationBundle : Type u}
    (system : SupportSystem Carrier ImplementationBundle)
    (carrier : Carrier) where
  nodes : List system.Node
  sound :
    ∀ node,
      node ∈ nodes →
        RequiredAt system carrier node
  complete :
    ∀ node,
      RequiredAt system carrier node →
        node ∈ nodes

/-- Proof-carrying closure of the exact mandatory support projection. -/
structure SupportClosureCertificate
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
    (system : SupportSystem Carrier ImplementationBundle)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot) where
  mandatoryProjection :
    MandatorySupportProjectionAt system carrier.value
  requiredSeal : RequiredNodeSeal system carrier.value
  closesRequired :
    ∀ node,
      RequiredAt system carrier.value node →
        SupportClosureAt system snapshot carrier node

section IndexedConsequences

variable
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

/-- Closure is nonvacuous because its mandatory projection yields a node. -/
theorem SupportClosureCertificate.hasClosedRequiredNode
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    (certificate : SupportClosureCertificate system snapshot carrier) :
    ∃ node,
      RequiredAt system carrier.value node ∧
        SupportClosureAt system snapshot carrier node := by
  obtain ⟨node, required⟩ :=
    certificate.mandatoryProjection.requiredExists
  exact ⟨node, required, certificate.closesRequired node required⟩

/-- A root token cannot be rebound to a distinct sealed snapshot. -/
theorem RootWitnessAt.cannotBindDifferentSnapshot
    {snapshot other : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    {node : system.Node}
    (witness : RootWitnessAt system snapshot carrier node)
    (different : snapshot ≠ other) :
    witness.observedSnapshot ≠ other := by
  intro rebound
  exact different (witness.snapshotBound.symm.trans rebound)

/-- A rule token cannot be rebound to a distinct sealed snapshot. -/
theorem RuleWitnessAt.cannotBindDifferentSnapshot
    {snapshot other : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    {node : system.Node}
    (witness : RuleWitnessAt system snapshot carrier node)
    (different : snapshot ≠ other) :
    witness.observedSnapshot ≠ other := by
  intro rebound
  exact different (witness.snapshotBound.symm.trans rebound)

/-- Strict descent rejects a rule that lists itself as a premise. -/
theorem RuleWitnessAt.noSelfPremise
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    {node : system.Node}
    (witness : RuleWitnessAt system snapshot carrier node) :
    node ∉ system.premises node := by
  intro self
  exact Nat.lt_irrefl _ (witness.premisesLower node self)

/-- Two checked rules cannot support one another. -/
theorem noVerifiedTwoCycle
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    {first second : system.Node}
    (firstRule : RuleWitnessAt system snapshot carrier first)
    (secondRule : RuleWitnessAt system snapshot carrier second)
    (secondSupportsFirst : second ∈ system.premises first)
    (firstSupportsSecond : first ∈ system.premises second) :
    False := by
  have secondLower :=
    firstRule.premisesLower second secondSupportsFirst
  have firstLower :=
    secondRule.premisesLower first firstSupportsSecond
  exact (Nat.not_lt_of_ge (Nat.le_of_lt secondLower)) firstLower

/-- A rootless leaf cannot be closed by an empty derivation rule. -/
theorem rootlessLeafCannotClose
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {system : SupportSystem Carrier ImplementationBundle}
    {node : system.Node}
    (noAcceptedRoot :
      ∀ certificate,
        system.verifyRoot carrier.value node certificate = false)
    (leaf : system.premises node = []) :
    ¬ SupportClosureAt system snapshot carrier node := by
  intro closed
  cases closed with
  | root _ witness =>
      have rejected := noAcceptedRoot witness.certificate
      have acceptedAtCarrier :
          system.verifyRoot carrier.value node witness.certificate = true := by
        rw [← witness.carrierBound]
        exact witness.accepted
      rw [rejected] at acceptedAtCarrier
      cases acceptedAtCarrier
  | derived _ witness _ =>
      exact witness.premisesNonempty leaf

end IndexedConsequences

end Residua.RCC.SupportClosure

import RCC.SupportClosure

namespace Residua.RCC.SupportClosure.Tests

open Residua.RCC.FacetSnapshot

inductive Head | first | second deriving DecidableEq
inductive Node | root | derived | leaf deriving DecidableEq
inductive Judgment | mandatory | omitted deriving DecidableEq
inductive Verifier | trusted deriving DecidableEq
inductive RootCertificate | good | forged deriving DecidableEq
inductive RuleCertificate | good | forged deriving DecidableEq

structure Carrier where
  head : Head

abbrev ImplementationBundle := Nat

def sealSpec :
    SnapshotSeal Unit Head Unit Unit Unit Unit Unit ImplementationBundle where
  IsSealed := fun coordinates =>
    coordinates.sourceWindow = () ∧
      coordinates.implementationBundle = 19

def coordinates (head : Head) :
    SnapshotCoordinates Unit Head Unit Unit Unit Unit Unit ImplementationBundle :=
  { epoch := ()
    historyHead := head
    assumptionRoot := ()
    addressRegistry := ()
    sourceWindow := ()
    failureModel := ()
    proposalWindow := ()
    implementationBundle := 19 }

def snapshotFirst : SealedSnapshot sealSpec :=
  { coordinates := coordinates .first
    sealed := ⟨rfl, rfl⟩ }

def snapshotSecond : SealedSnapshot sealSpec :=
  { coordinates := coordinates .second
    sealed := ⟨rfl, rfl⟩ }

def projection :
    CarrierProjection
      Carrier Unit Head Unit Unit Unit Unit Unit ImplementationBundle :=
  { epoch := fun _ => ()
    historyHead := Carrier.head
    assumptionRoot := fun _ => ()
    addressRegistry := fun _ => ()
    sourceWindow := fun _ => ()
    failureModel := fun _ => ()
    proposalWindow := fun _ => ()
    implementationBundle := fun _ => 19 }

def carrierFirst : SnapshotCarrier projection snapshotFirst :=
  { value := { head := .first }
    epochBound := rfl
    historyHeadBound := rfl
    assumptionRootBound := rfl
    addressRegistryBound := rfl
    sourceWindowBound := rfl
    failureModelBound := rfl
    proposalWindowBound := rfl
    implementationBundleBound := rfl }

abbrev system : SupportSystem Carrier ImplementationBundle :=
  { Node := Node
    Judgment := Judgment
    Verifier := Verifier
    RootCertificate := RootCertificate
    RuleCertificate := RuleCertificate
    rank := fun
      | .root => 0
      | .derived => 1
      | .leaf => 0
    premises := fun
      | .root => []
      | .derived => [.root]
      | .leaf => []
    mandatoryJudgments := [.mandatory]
    LiveMandatoryAt := fun judgment => judgment = .mandatory
    directSupport := fun carrier judgment =>
      if carrier.head == .first && judgment == .mandatory then
        [.derived]
      else
        []
    expectedVerifier := fun _ => .trusted
    rootVerifier := fun _ => .trusted
    ruleVerifier := fun _ => .trusted
    rootImplementation := fun
      | .good => 19
      | .forged => 20
    ruleImplementation := fun
      | .good => 19
      | .forged => 20
    RootClaim := fun carrier node certificate =>
      carrier.head = .first ∧ node = .root ∧ certificate = .good
    RuleClaim := fun carrier node certificate =>
      carrier.head = .first ∧ node = .derived ∧ certificate = .good
    verifyRoot := fun carrier node certificate =>
      carrier.head == .first && node == .root && certificate == .good
    verifyRule := fun carrier node certificate =>
      carrier.head == .first && node == .derived && certificate == .good
    rootSound := by
      intro carrier node certificate accepted
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩
    ruleSound := by
      intro carrier node certificate accepted
      simp only [Bool.and_eq_true, beq_iff_eq] at accepted
      exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩ }

theorem derivedPremises :
    system.premises Node.derived = [Node.root] := rfl

theorem rootPremises :
    system.premises Node.root = [] := rfl

theorem rootRank : system.rank Node.root = 0 := rfl
theorem derivedRank : system.rank Node.derived = 1 := rfl

def rootWitness :
    RootWitnessAt system snapshotFirst carrierFirst Node.root :=
  { observedSnapshot := snapshotFirst
    observedCarrier := carrierFirst.value
    certificate := .good
    snapshotBound := rfl
    carrierBound := rfl
    verifierBound := rfl
    implementationBound := rfl
    accepted := rfl
    claim := ⟨rfl, rfl, rfl⟩
    claimDerived := rfl }

def rootClosed :
    SupportClosureAt system snapshotFirst carrierFirst Node.root :=
  SupportClosureAt.root
    (system := system) (snapshot := snapshotFirst) (carrier := carrierFirst)
    Node.root rootWitness

def derivedWitness :
    RuleWitnessAt system snapshotFirst carrierFirst Node.derived :=
  { observedSnapshot := snapshotFirst
    observedCarrier := carrierFirst.value
    certificate := .good
    snapshotBound := rfl
    carrierBound := rfl
    verifierBound := rfl
    implementationBound := rfl
    accepted := rfl
    claim := ⟨rfl, rfl, rfl⟩
    claimDerived := rfl
    premisesNonempty := by
      intro empty
      rw [derivedPremises] at empty
      cases empty
    premisesLower := by
      intro premise member
      rw [derivedPremises] at member
      cases member with
      | head =>
          rw [rootRank, derivedRank]
          decide
      | tail _ impossible =>
          cases impossible }

def derivedClosed :
    SupportClosureAt system snapshotFirst carrierFirst Node.derived :=
  SupportClosureAt.derived
    (system := system) (snapshot := snapshotFirst) (carrier := carrierFirst)
    Node.derived derivedWitness (by
      intro premise member
      rw [derivedPremises] at member
      cases member with
      | head => exact rootClosed
      | tail _ impossible => cases impossible)

def mandatoryProjection :
    MandatorySupportProjectionAt system carrierFirst.value :=
  { liveExists := ⟨.mandatory, rfl⟩
    declaredSound := by
      intro judgment member
      change judgment ∈ [Judgment.mandatory] at member
      cases member with
      | head => rfl
      | tail _ impossible => cases impossible
    declaredComplete := by
      intro judgment live
      subst judgment
      exact List.Mem.head []
    sourceNonempty := by
      intro judgment live
      subst judgment
      simp [system, carrierFirst] }

def requiredSeal : RequiredNodeSeal system carrierFirst.value :=
  { nodes := [.derived, .root]
    sound := by
      intro node member
      cases member with
      | head =>
          exact
            RequiredNodeOrigin.direct
              (system := system) (carrier := carrierFirst.value)
              Judgment.mandatory Node.derived rfl
              (by simp [system, carrierFirst])
      | tail _ member =>
          cases member with
          | head =>
              exact
                RequiredNodeOrigin.dependency
                  (system := system) (carrier := carrierFirst.value)
                  Node.derived Node.root
                  (RequiredNodeOrigin.direct
                    (system := system) (carrier := carrierFirst.value)
                    Judgment.mandatory Node.derived rfl
                    (by simp [system, carrierFirst]))
                  (by rw [derivedPremises]; exact List.Mem.head [])
          | tail _ impossible => cases impossible
    complete := by
      intro node required
      induction required with
      | direct judgment node live selected =>
          subst judgment
          change node ∈ [Node.derived, Node.root]
          have selectedDerived : node ∈ [Node.derived] := by
            simpa [system, carrierFirst] using selected
          cases selectedDerived with
          | head => exact List.Mem.head _
          | tail _ impossible => cases impossible
      | dependency parent node parentRequired selected parentMember =>
          change node ∈ [Node.derived, Node.root]
          cases parentMember with
          | head =>
              rw [derivedPremises] at selected
              have nodeRoot : node = Node.root :=
                List.eq_of_mem_singleton selected
              subst node
              exact List.Mem.tail _ (List.Mem.head [])
          | tail _ parentTail =>
              cases parentTail with
              | head =>
                  rw [rootPremises] at selected
                  cases selected
              | tail _ impossible =>
                  cases impossible }

def closureCertificate :
    SupportClosureCertificate system snapshotFirst carrierFirst :=
  { mandatoryProjection := mandatoryProjection
    requiredSeal := requiredSeal
    closesRequired := by
      intro node required
      have member := requiredSeal.complete node required
      cases member with
      | head => exact derivedClosed
      | tail _ member =>
          cases member with
          | head => exact rootClosed
          | tail _ impossible => cases impossible }

theorem positive_support_is_nonvacuous :
    ∃ node,
      RequiredAt system carrierFirst.value node ∧
        SupportClosureAt system snapshotFirst carrierFirst node :=
  closureCertificate.hasClosedRequiredNode

/-! ## Checker and universe countermodels -/

theorem forged_root_flag_cannot_bypass_checker
    (witness : RootWitnessAt system snapshotFirst carrierFirst Node.root) :
    witness.certificate ≠ RootCertificate.forged := by
  intro forged
  have accepted := witness.accepted
  rw [witness.carrierBound, forged] at accepted
  cases accepted

def alwaysTrueRoot
    (_carrier : Carrier) (_node : Node) (_certificate : RootCertificate) : Bool :=
  true

def impossibleRootClaim
    (_carrier : Carrier) (_node : Node) (_certificate : RootCertificate) : Prop :=
  False

theorem always_true_checker_has_no_soundness :
    ¬ ∀ carrier node certificate,
      alwaysTrueRoot carrier node certificate = true →
        impossibleRootClaim carrier node certificate := by
  intro claimedSound
  exact claimedSound carrierFirst.value .root .forged rfl

def emptyMandatorySystem : SupportSystem Carrier ImplementationBundle :=
  { system with mandatoryJudgments := [] }

theorem empty_mandatory_universe_cannot_seal :
    ¬ Nonempty
      (MandatorySupportProjectionAt
        emptyMandatorySystem carrierFirst.value) := by
  intro ⟨sealed⟩
  exact sealed.mandatoryNonempty rfl

def partialMandatorySystem : SupportSystem Carrier ImplementationBundle :=
  { system with
    mandatoryJudgments := [.mandatory]
    LiveMandatoryAt := fun _ => True }

theorem partial_mandatory_universe_cannot_seal :
    ¬ Nonempty
      (MandatorySupportProjectionAt
        partialMandatorySystem carrierFirst.value) := by
  intro ⟨sealed⟩
  have omitted := sealed.declaredComplete Judgment.omitted trivial
  change Judgment.omitted ∈ [Judgment.mandatory] at omitted
  exact nomatch omitted

def emptySupportSystem : SupportSystem Carrier ImplementationBundle :=
  { system with directSupport := fun _ _ => [] }

theorem live_mandatory_cannot_project_empty_support :
    ¬ Nonempty
      (MandatorySupportProjectionAt
        emptySupportSystem carrierFirst.value) := by
  intro ⟨sealed⟩
  have nonempty := sealed.sourceNonempty Judgment.mandatory rfl
  exact nonempty rfl

/-! ## Cycle and snapshot countermodels -/

theorem rootless_leaf_cannot_close :
    ¬ SupportClosureAt system snapshotFirst carrierFirst Node.leaf :=
  rootlessLeafCannotClose
    (by
      intro certificate
      cases certificate <;> rfl)
    rfl

def selfLoopSystem : SupportSystem Carrier ImplementationBundle :=
  { system with
    premises := fun node =>
      if node == .derived then [.derived] else [] }

theorem self_loop_cannot_have_checked_rule :
    ¬ Nonempty
      (RuleWitnessAt
        selfLoopSystem snapshotFirst carrierFirst Node.derived) := by
  intro ⟨witness⟩
  apply witness.noSelfPremise
  change Node.derived ∈
    (if Node.derived == Node.derived then [Node.derived] else [])
  simp

def twoCycleSystem : SupportSystem Carrier ImplementationBundle :=
  { system with
    rank := fun
      | .derived => 1
      | .leaf => 1
      | .root => 0
    premises := fun
      | .derived => [.leaf]
      | .leaf => [.derived]
      | .root => []
    RuleClaim := fun carrier node certificate =>
      carrier.head = .first ∧
        (node = .derived ∨ node = .leaf) ∧ certificate = .good
    verifyRule := fun carrier node certificate =>
      carrier.head == .first &&
        (node == .derived || node == .leaf) &&
          certificate == .good
    ruleSound := by
      intro carrier node certificate accepted
      simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at accepted
      exact ⟨accepted.1.1, accepted.1.2, accepted.2⟩ }

theorem concrete_two_cycle_cannot_have_both_rules :
    ¬ (Nonempty
          (RuleWitnessAt
            twoCycleSystem snapshotFirst carrierFirst Node.derived) ∧
        Nonempty
          (RuleWitnessAt
            twoCycleSystem snapshotFirst carrierFirst Node.leaf)) := by
  rintro ⟨⟨firstRule⟩, ⟨secondRule⟩⟩
  exact
    noVerifiedTwoCycle firstRule secondRule
      (by change Node.leaf ∈ [Node.leaf]; exact List.Mem.head [])
      (by change Node.derived ∈ [Node.derived]; exact List.Mem.head [])

theorem snapshotFirst_ne_snapshotSecond :
    snapshotFirst ≠ snapshotSecond := by
  intro same
  have heads :
      snapshotFirst.coordinates.historyHead =
        snapshotSecond.coordinates.historyHead :=
    congrArg (fun value => value.coordinates.historyHead) same
  cases heads

theorem cross_snapshot_closure_token_rejected :
    ¬ ∃ witness : RootWitnessAt system snapshotFirst carrierFirst Node.root,
      witness.observedSnapshot = snapshotSecond ∧
        SupportClosureAt system snapshotFirst carrierFirst Node.root := by
  rintro ⟨witness, rebound, _closed⟩
  exact
    witness.cannotBindDifferentSnapshot
      snapshotFirst_ne_snapshotSecond rebound

end Residua.RCC.SupportClosure.Tests

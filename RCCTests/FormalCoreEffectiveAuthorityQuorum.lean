import RCC.EffectiveAuthorityQuorum

/-!
# RCC-34 Effective Authority Quorum Witnesses

These finite witnesses separate public-key and logical-identity counts from the
effective control-domain min-cut.  The topology is closed-world only when an
explicit coverage proof accounts for every eligible signer.
-/

namespace Residua.RCC.EffectiveAuthorityQuorum.Tests

open Residua.RCC.EffectiveAuthorityQuorum

theorem mem_singleton_exact {α : Type} {item only : α} :
    item ∈ [only] ↔ item = only := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]

theorem mem_pair_exact {α : Type} {item first second : α} :
    item ∈ [first, second] ↔ item = first ∨ item = second := by
  simp only [List.mem_cons, List.not_mem_nil, or_false]

inductive PairSigner
  | left
  | right
  deriving DecidableEq

inductive PairKey
  | leftKey
  | rightKey
  deriving DecidableEq

inductive PairActor
  | author
  | disposer
  deriving DecidableEq

inductive PairProcess
  | leftProcess
  | rightProcess
  deriving DecidableEq

inductive PairDomain
  | leftDomain
  | rightDomain
  | oneCustodian
  deriving DecidableEq

inductive PairContext
  | independent
  | oneCustodian
  deriving DecidableEq

def pairSystem : AuthoritySystem where
  Context := PairContext
  Signer := PairSigner
  KeyQ := PairKey
  ActorQ := PairActor
  ProcessQ := PairProcess
  ControlDomain := PairDomain
  ActQ := Unit
  eligible := fun _ => True
  keyOf
    | .left => .leftKey
    | .right => .rightKey
  actorOf
    | .left => .author
    | .right => .disposer
  processOf
    | .left => .leftProcess
    | .right => .rightProcess
  thresholdAt := fun _ => 2
  threatBudgetAt := fun _ => 1
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt
    | .independent, _, signers => signers = [.left, .right]
    | .oneCustodian, _, signers => signers = [.left, .right]
  controlDepends
    | .independent, .left, domain => domain = .leftDomain
    | .independent, .right, domain => domain = .rightDomain
    | .oneCustodian, _, domain => domain = .oneCustodian

def pairPolicy : AuthorityPolicy pairSystem where
  threshold := 2
  threatBudget := 1

def relaxedPairPolicy : AuthorityPolicy pairSystem where
  threshold := 2
  threatBudget := 0

def independentTopology : FiniteControlTopology pairSystem where
  context := .independent
  listedSigners := [.left, .right]
  listedDomains := [.leftDomain, .rightDomain, .oneCustodian]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains
    | .left => [.leftDomain]
    | .right => [.rightDomain]
  dependencyDomainsNoDup := by
    intro signer
    cases signer <;> simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer with
    | left =>
        change domain ∈ [.leftDomain] ↔ domain = .leftDomain
        exact mem_singleton_exact
    | right =>
        change domain ∈ [.rightDomain] ↔ domain = .rightDomain
        exact mem_singleton_exact
  dependencyDomainsListed := by
    intro signer domain member
    cases signer <;> simp at member ⊢ <;> simp [member]
  keyCustodyDomain
    | .leftKey => .leftDomain
    | .rightKey => .rightDomain
  processHostDomain
    | .leftProcess => .leftDomain
    | .rightProcess => .rightDomain
  actorAuthorityRootDomain
    | .author => .leftDomain
    | .disposer => .rightDomain
  mandatoryControlPaths := by
    intro signer _
    cases signer with
    | left =>
        exact
          ⟨mem_singleton_exact.2 rfl,
            mem_singleton_exact.2 rfl,
            mem_singleton_exact.2 rfl⟩
    | right =>
        exact
          ⟨mem_singleton_exact.2 rfl,
            mem_singleton_exact.2 rfl,
            mem_singleton_exact.2 rfl⟩
  domainCost := fun _ => 1
  domainCostExact := by
    intro _
    rfl
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

def oneCustodianTopology : FiniteControlTopology pairSystem where
  context := .oneCustodian
  listedSigners := [.left, .right]
  listedDomains := [.leftDomain, .rightDomain, .oneCustodian]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains := fun _ => [.oneCustodian]
  dependencyDomainsNoDup := by
    intro signer
    cases signer <;> simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer <;>
      change domain ∈ [.oneCustodian] ↔ domain = .oneCustodian <;>
      exact mem_singleton_exact
  dependencyDomainsListed := by
    intro _ domain member
    simp at member ⊢
    exact Or.inr (Or.inr member)
  keyCustodyDomain := fun _ => .oneCustodian
  processHostDomain := fun _ => .oneCustodian
  actorAuthorityRootDomain := fun _ => .oneCustodian
  mandatoryControlPaths := by
    intro signer _
    cases signer <;>
      exact
        ⟨mem_singleton_exact.2 rfl,
          mem_singleton_exact.2 rfl,
          mem_singleton_exact.2 rfl⟩
  domainCost := fun _ => 1
  domainCostExact := by
    intro _
    rfl
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

theorem relaxed_policy_cannot_bind_pre_state :
    ¬ PolicyBoundAt pairSystem independentTopology relaxedPairPolicy := by
  simp [PolicyBoundAt, relaxedPairPolicy, pairSystem, independentTopology]

theorem relaxed_policy_cannot_form_certificate :
    EffectiveAuthorityCertificate
      pairSystem relaxedPairPolicy independentTopology → False := by
  intro certificate
  exact relaxed_policy_cannot_bind_pre_state certificate.preStatePolicy

theorem relaxed_policy_cannot_prove_effective_authority :
    ¬ EffectiveControlCutExceedsBudget
      pairSystem relaxedPairPolicy independentTopology := by
  intro effective
  exact relaxed_policy_cannot_bind_pre_state effective.1

def inflatedPairDomainCost : PairDomain → Nat :=
  fun _ => 100

theorem inflated_domain_cost_cannot_match_pre_state :
    ¬ ∀ domain,
      inflatedPairDomainCost domain =
        pairSystem.controlDomainCostAt
          independentTopology.context domain := by
  intro exactCost
  have impossible := exactCost .leftDomain
  simp [inflatedPairDomainCost, pairSystem, independentTopology] at impossible

theorem pair_quorum_is_key_and_actor_distinct :
    SignerCountMeetsThreshold pairPolicy [.left, .right] ∧
      DistinctKeys pairSystem [.left, .right] ∧
      DistinctActors pairSystem [.left, .right] ∧
      EligibleKeyQuorum pairSystem pairPolicy [.left, .right] := by
  simp [SignerCountMeetsThreshold, DistinctKeys, DistinctActors,
    EligibleKeyQuorum, pairPolicy, pairSystem]

theorem one_custodian_is_an_actual_control_cut :
    IsActualControlCut pairSystem pairPolicy oneCustodianTopology
      [.oneCustodian] := by
  refine ⟨by simp, ?_⟩
  exact ⟨[.left, .right], pair_quorum_is_key_and_actor_distinct.2.2.2, by
    intro signer _
    exact
      ⟨.oneCustodian, mem_singleton_exact.2 rfl,
        by cases signer <;> rfl⟩⟩

/--
Countermodel 1: two distinct public keys still have an affordable one-domain
forgery cut when both keys share one custodian.
-/
theorem two_public_keys_one_custodian_countermodel :
    DistinctKeys pairSystem [.left, .right] ∧
      ¬ EffectiveControlCutExceedsBudget
        pairSystem pairPolicy oneCustodianTopology := by
  refine ⟨pair_quorum_is_key_and_actor_distinct.2.1, ?_⟩
  exact affordable_actual_cut_refutes_effective_authority
    pairSystem pairPolicy oneCustodianTopology [.oneCustodian]
    one_custodian_is_an_actual_control_cut
    (by simp [ControlCutCost, oneCustodianTopology, pairPolicy])

inductive AutoSigner
  | author
  | reviewer
  | disposer
  deriving DecidableEq

inductive AutoKey
  | authorKey
  | reviewerKey
  | disposerKey
  deriving DecidableEq

inductive AutoActor
  | authorActor
  | reviewerActor
  | disposerActor
  deriving DecidableEq

inductive AutoProcess
  | soleAutoSigner
  deriving DecidableEq

inductive AutoDomain
  | soleProcessDomain
  deriving DecidableEq

def autoSystem : AuthoritySystem where
  Context := Unit
  Signer := AutoSigner
  KeyQ := AutoKey
  ActorQ := AutoActor
  ProcessQ := AutoProcess
  ControlDomain := AutoDomain
  ActQ := Unit
  eligible := fun _ => True
  keyOf
    | .author => .authorKey
    | .reviewer => .reviewerKey
    | .disposer => .disposerKey
  actorOf
    | .author => .authorActor
    | .reviewer => .reviewerActor
    | .disposer => .disposerActor
  processOf := fun _ => .soleAutoSigner
  thresholdAt := fun _ => 3
  threatBudgetAt := fun _ => 1
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt := fun _ _ _ => False
  controlDepends := fun _ _ domain => domain = .soleProcessDomain

def autoPolicy : AuthorityPolicy autoSystem where
  threshold := 3
  threatBudget := 1

def oneProcessTopology : FiniteControlTopology autoSystem where
  context := ()
  listedSigners := [.author, .reviewer, .disposer]
  listedDomains := [.soleProcessDomain]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains := fun _ => [.soleProcessDomain]
  dependencyDomainsNoDup := by
    intro signer
    cases signer <;> simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer <;>
      change domain ∈ [.soleProcessDomain] ↔
        domain = .soleProcessDomain <;>
      exact mem_singleton_exact
  dependencyDomainsListed := by
    intro _ domain member
    exact member
  keyCustodyDomain := fun _ => .soleProcessDomain
  processHostDomain := fun _ => .soleProcessDomain
  actorAuthorityRootDomain := fun _ => .soleProcessDomain
  mandatoryControlPaths := by
    intro _ _
    simp
  domainCost := fun _ => 1
  domainCostExact := by
    intro _
    rfl
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

theorem auto_signer_quorum_is_key_and_actor_distinct :
    DistinctActors autoSystem [.author, .reviewer, .disposer] ∧
      DistinctKeys autoSystem [.author, .reviewer, .disposer] ∧
      ¬ DistinctProcesses autoSystem [.author, .reviewer, .disposer] ∧
      EligibleKeyQuorum autoSystem autoPolicy
        [.author, .reviewer, .disposer] := by
  simp [DistinctActors, DistinctKeys, DistinctProcesses, EligibleKeyQuorum,
    SignerCountMeetsThreshold, autoPolicy, autoSystem]

theorem one_process_is_an_actual_control_cut :
    IsActualControlCut autoSystem autoPolicy oneProcessTopology
      [.soleProcessDomain] := by
  refine ⟨by simp, ?_⟩
  exact
    ⟨[.author, .reviewer, .disposer],
      auto_signer_quorum_is_key_and_actor_distinct.2.2.2,
      by
        intro signer _
        exact
          ⟨.soleProcessDomain, by simp,
            by simp [autoSystem]⟩⟩

/--
Countermodel 3: distinct actor addresses and distinct keys do not create
control separation when one process can auto-sign every role.
-/
theorem distinct_actors_one_process_countermodel :
    DistinctActors autoSystem [.author, .reviewer, .disposer] ∧
      DistinctKeys autoSystem [.author, .reviewer, .disposer] ∧
      ¬ DistinctProcesses autoSystem [.author, .reviewer, .disposer] ∧
      ¬ EffectiveControlCutExceedsBudget
        autoSystem autoPolicy oneProcessTopology := by
  refine
    ⟨auto_signer_quorum_is_key_and_actor_distinct.1,
      auto_signer_quorum_is_key_and_actor_distinct.2.1,
      auto_signer_quorum_is_key_and_actor_distinct.2.2.1, ?_⟩
  exact affordable_actual_cut_refutes_effective_authority
    autoSystem autoPolicy oneProcessTopology [.soleProcessDomain]
    one_process_is_an_actual_control_cut
    (by simp [ControlCutCost, oneProcessTopology, autoPolicy])

inductive HostSigner
  | first
  | second
  | third
  deriving DecidableEq

inductive HostKey
  | firstKey
  | secondKey
  | thirdKey
  deriving DecidableEq

inductive HostActor
  | firstActor
  | secondActor
  | thirdActor
  deriving DecidableEq

inductive HostProcess
  | firstProcess
  | secondProcess
  | thirdProcess
  deriving DecidableEq

inductive HostDomain
  | firstCustody
  | secondCustody
  | thirdCustody
  | sharedHost
  deriving DecidableEq

def hostSystem : AuthoritySystem where
  Context := Unit
  Signer := HostSigner
  KeyQ := HostKey
  ActorQ := HostActor
  ProcessQ := HostProcess
  ControlDomain := HostDomain
  ActQ := Unit
  eligible := fun _ => True
  keyOf
    | .first => .firstKey
    | .second => .secondKey
    | .third => .thirdKey
  actorOf
    | .first => .firstActor
    | .second => .secondActor
    | .third => .thirdActor
  processOf
    | .first => .firstProcess
    | .second => .secondProcess
    | .third => .thirdProcess
  thresholdAt := fun _ => 3
  threatBudgetAt := fun _ => 1
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt := fun _ _ _ => False
  controlDepends
    | _, .first, domain =>
        domain = .firstCustody ∨ domain = .sharedHost
    | _, .second, domain =>
        domain = .secondCustody ∨ domain = .sharedHost
    | _, .third, domain =>
        domain = .thirdCustody ∨ domain = .sharedHost

def hostPolicy : AuthorityPolicy hostSystem where
  threshold := 3
  threatBudget := 1

def sharedHostTopology : FiniteControlTopology hostSystem where
  context := ()
  listedSigners := [.first, .second, .third]
  listedDomains :=
    [.firstCustody, .secondCustody, .thirdCustody, .sharedHost]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains
    | .first => [.firstCustody, .sharedHost]
    | .second => [.secondCustody, .sharedHost]
    | .third => [.thirdCustody, .sharedHost]
  dependencyDomainsNoDup := by
    intro signer
    cases signer <;> simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer with
    | first =>
        change
          domain ∈ [.firstCustody, .sharedHost] ↔
            domain = .firstCustody ∨ domain = .sharedHost
        exact mem_pair_exact
    | second =>
        change
          domain ∈ [.secondCustody, .sharedHost] ↔
            domain = .secondCustody ∨ domain = .sharedHost
        exact mem_pair_exact
    | third =>
        change
          domain ∈ [.thirdCustody, .sharedHost] ↔
            domain = .thirdCustody ∨ domain = .sharedHost
        exact mem_pair_exact
  dependencyDomainsListed := by
    intro signer domain member
    cases signer <;>
      simp at member ⊢ <;>
      rcases member with rfl | rfl <;> simp
  keyCustodyDomain
    | .firstKey => .firstCustody
    | .secondKey => .secondCustody
    | .thirdKey => .thirdCustody
  processHostDomain := fun _ => .sharedHost
  actorAuthorityRootDomain
    | .firstActor => .firstCustody
    | .secondActor => .secondCustody
    | .thirdActor => .thirdCustody
  mandatoryControlPaths := by
    intro signer _
    cases signer with
    | first =>
        exact
          ⟨mem_pair_exact.2 (Or.inl rfl),
            mem_pair_exact.2 (Or.inr rfl),
            mem_pair_exact.2 (Or.inl rfl)⟩
    | second =>
        exact
          ⟨mem_pair_exact.2 (Or.inl rfl),
            mem_pair_exact.2 (Or.inr rfl),
            mem_pair_exact.2 (Or.inl rfl)⟩
    | third =>
        exact
          ⟨mem_pair_exact.2 (Or.inl rfl),
            mem_pair_exact.2 (Or.inr rfl),
            mem_pair_exact.2 (Or.inl rfl)⟩
  domainCost := fun _ => 1
  domainCostExact := by
    intro _
    rfl
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

theorem host_quorum_has_three_distinct_keys_and_processes :
    DistinctKeys hostSystem [.first, .second, .third] ∧
      DistinctProcesses hostSystem [.first, .second, .third] ∧
      EligibleKeyQuorum hostSystem hostPolicy [.first, .second, .third] := by
  simp [DistinctKeys, DistinctProcesses, EligibleKeyQuorum,
    SignerCountMeetsThreshold, hostPolicy, hostSystem]

theorem shared_host_is_an_actual_control_cut :
    IsActualControlCut hostSystem hostPolicy sharedHostTopology
      [.sharedHost] := by
  refine ⟨by simp, ?_⟩
  exact
    ⟨[.first, .second, .third],
      host_quorum_has_three_distinct_keys_and_processes.2.2,
      by
        intro signer _
        refine
          ⟨.sharedHost, mem_singleton_exact.2 rfl, ?_⟩
        cases signer <;> exact Or.inr rfl⟩

theorem shared_host_cut_cost_equals_budget :
    ControlCutCost sharedHostTopology [.sharedHost] =
      hostPolicy.threatBudget := by
  rfl

/--
Three distinct keys and three distinct processes remain one effective authority
when every process is hosted by one affordable control domain.
-/
theorem three_keys_one_host_countermodel :
    DistinctKeys hostSystem [.first, .second, .third] ∧
      DistinctProcesses hostSystem [.first, .second, .third] ∧
      ¬ EffectiveControlCutExceedsBudget
        hostSystem hostPolicy sharedHostTopology := by
  refine
    ⟨host_quorum_has_three_distinct_keys_and_processes.1,
      host_quorum_has_three_distinct_keys_and_processes.2.1, ?_⟩
  exact affordable_actual_cut_refutes_effective_authority
    hostSystem hostPolicy sharedHostTopology [.sharedHost]
    shared_host_is_an_actual_control_cut
    (Nat.le_of_eq shared_host_cut_cost_equals_budget)

def omittedSharedHostDependencies : HostSigner → List HostDomain
  | .first => [.firstCustody]
  | .second => [.secondCustody]
  | .third => [.thirdCustody]

/--
A caller cannot omit the shared host and still construct the exact dependency
seal required by `FiniteControlTopology`.
-/
theorem omitted_shared_host_dependency_cannot_be_exact :
    ¬ ∀ signer domain,
      domain ∈ omittedSharedHostDependencies signer ↔
        hostSystem.controlDepends () signer domain := by
  intro exactDependencies
  have sharedHostMustBeListed :=
    (exactDependencies .first .sharedHost).2
      (by simp [hostSystem])
  simp [omittedSharedHostDependencies] at sharedHostMustBeListed

inductive Handle
  | authorHandle
  | reviewerHandle
  | disposerHandle
  deriving DecidableEq

inductive HandleKey
  | soleSigningKey
  deriving DecidableEq

inductive HandleActor
  | authorActor
  | reviewerActor
  | disposerActor
  deriving DecidableEq

inductive HandleProcess
  | soleProcess
  deriving DecidableEq

inductive HandleDomain
  | soleControlDomain
  deriving DecidableEq

def handleSystem : AuthoritySystem where
  Context := Unit
  Signer := Handle
  KeyQ := HandleKey
  ActorQ := HandleActor
  ProcessQ := HandleProcess
  ControlDomain := HandleDomain
  ActQ := Unit
  eligible := fun _ => True
  keyOf := fun _ => .soleSigningKey
  actorOf
    | .authorHandle => .authorActor
    | .reviewerHandle => .reviewerActor
    | .disposerHandle => .disposerActor
  processOf := fun _ => .soleProcess
  thresholdAt := fun _ => 3
  threatBudgetAt := fun _ => 1
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt := fun _ _ _ => False
  controlDepends := fun _ _ _ => False

def handlePolicy : AuthorityPolicy handleSystem where
  threshold := 3
  threatBudget := 1

/--
Countermodel 2: three distinct handles and actor addresses meet a naive count,
but one signing key cannot form an eligible distinct-key three-vote quorum.
-/
theorem three_handles_one_signing_key_countermodel :
    SignerCountMeetsThreshold handlePolicy
        [.authorHandle, .reviewerHandle, .disposerHandle] ∧
      DistinctActors handleSystem
        [.authorHandle, .reviewerHandle, .disposerHandle] ∧
      ¬ DistinctKeys handleSystem
        [.authorHandle, .reviewerHandle, .disposerHandle] ∧
      ¬ EligibleKeyQuorum handleSystem handlePolicy
        [.authorHandle, .reviewerHandle, .disposerHandle] := by
  simp [SignerCountMeetsThreshold, DistinctActors, DistinctKeys,
    EligibleKeyQuorum, handlePolicy, handleSystem]

theorem independent_topology_is_closed :
    ClosedWorldCoverage pairSystem independentTopology := by
  constructor
  · intro signer _
    cases signer <;> simp [independentTopology]
  · intro domain
    cases domain <;> simp [independentTopology]

theorem independent_pair_is_a_listed_control_cut :
    IsListedControlCut pairSystem pairPolicy independentTopology
      [.leftDomain, .rightDomain] := by
  refine ⟨by simp, ?_⟩
  exact ⟨[.left, .right], pair_quorum_is_key_and_actor_distinct.2.2.2,
    by
      intro signer _
      cases signer with
      | left => exact mem_pair_exact.2 (Or.inl rfl)
      | right => exact mem_pair_exact.2 (Or.inr rfl),
    by
      intro signer _
      cases signer with
      | left =>
          exact
            ⟨.leftDomain, mem_pair_exact.2 (Or.inl rfl), rfl⟩
      | right =>
          exact
            ⟨.rightDomain, mem_pair_exact.2 (Or.inr rfl), rfl⟩⟩

theorem independent_pair_cut_is_minimum :
    IsMinimumListedControlCut pairSystem pairPolicy independentTopology
      [.leftDomain, .rightDomain] := by
  refine ⟨independent_pair_is_a_listed_control_cut, ?_⟩
  intro candidate hcandidate
  rcases hcandidate.canForge with
    ⟨quorum, hquorum, hlisted, hcontrolled⟩
  have hboth : .left ∈ quorum ∧ .right ∈ quorum :=
    pair_members_of_nodup_subset_length
      hquorum.1
      (by
        intro signer hsigner
        have := hlisted signer hsigner
        simpa [independentTopology] using this)
      hquorum.2.2.1
  have hleft := hcontrolled .left hboth.1
  have hright := hcontrolled .right hboth.2
  have hleftMem : .leftDomain ∈ candidate := by
    simpa [ControlledBy, independentTopology, pairSystem] using hleft
  have hrightMem : .rightDomain ∈ candidate := by
    simpa [ControlledBy, independentTopology, pairSystem] using hright
  have candidateLength : 2 ≤ candidate.length :=
    two_le_length_of_distinct_members
      (by decide : PairDomain.leftDomain ≠ .rightDomain)
      hleftMem hrightMem
  have minimumCost :=
    control_cut_cost_eq_length_of_unit_cost independentTopology
      (by intro domain; cases domain <;> rfl)
      [.leftDomain, .rightDomain]
  have candidateCost :=
    control_cut_cost_eq_length_of_unit_cost independentTopology
      (by intro domain; cases domain <;> rfl)
      candidate
  rw [minimumCost, candidateCost]
  exact candidateLength

def independentCertificate :
    EffectiveAuthorityCertificate pairSystem pairPolicy independentTopology where
  preStatePolicy := by
    simp [PolicyBoundAt, pairPolicy, pairSystem, independentTopology]
  topologyCoverage := independent_topology_is_closed
  minimumCut := [.leftDomain, .rightDomain]
  minimumListedCut := independent_pair_cut_is_minimum
  exceedsThreatBudget := by
    simp [ControlCutCost, independentTopology, pairPolicy]

def independentLawfulAct :
    LawfulAuthorityAct pairSystem pairPolicy independentTopology where
  act := ()
  signers := [.left, .right]
  upstreamVerified := by
    simp [UpstreamVerifiedAt, pairSystem, independentTopology]
  eligibleKeyQuorum := pair_quorum_is_key_and_actor_distinct.2.2.2
  signersListed := by
    intro signer hsigner
    cases signer <;> simp [independentTopology]
  effectiveAuthority := independentCertificate

theorem lawful_pair_has_actual_min_cut_above_budget :
    EffectiveControlCutExceedsBudget
      pairSystem pairPolicy independentTopology := by
  exact lawful_act_effective_control_min_cut_exceeds
    pairSystem pairPolicy independentTopology independentLawfulAct

inductive HiddenSigner
  | visibleLeft
  | visibleRight
  | hiddenLeft
  deriving DecidableEq

inductive HiddenKey
  | visibleLeftKey
  | visibleRightKey
  | hiddenLeftKey
  deriving DecidableEq

inductive HiddenActor
  | visibleLeftActor
  | visibleRightActor
  | hiddenLeftActor
  deriving DecidableEq

inductive HiddenProcess
  | visibleLeftProcess
  | visibleRightProcess
  | hiddenLeftProcess
  deriving DecidableEq

inductive HiddenDomain
  | leftDomain
  | rightDomain
  deriving DecidableEq

def hiddenSystem : AuthoritySystem where
  Context := Unit
  Signer := HiddenSigner
  KeyQ := HiddenKey
  ActorQ := HiddenActor
  ProcessQ := HiddenProcess
  ControlDomain := HiddenDomain
  ActQ := Unit
  eligible := fun _ => True
  keyOf
    | .visibleLeft => .visibleLeftKey
    | .visibleRight => .visibleRightKey
    | .hiddenLeft => .hiddenLeftKey
  actorOf
    | .visibleLeft => .visibleLeftActor
    | .visibleRight => .visibleRightActor
    | .hiddenLeft => .hiddenLeftActor
  processOf
    | .visibleLeft => .visibleLeftProcess
    | .visibleRight => .visibleRightProcess
    | .hiddenLeft => .hiddenLeftProcess
  thresholdAt := fun _ => 2
  threatBudgetAt := fun _ => 1
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt := fun _ _ _ => False
  controlDepends
    | _, .visibleLeft, domain => domain = .leftDomain
    | _, .visibleRight, domain => domain = .rightDomain
    | _, .hiddenLeft, domain => domain = .leftDomain

def hiddenPolicy : AuthorityPolicy hiddenSystem where
  threshold := 2
  threatBudget := 1

def incompleteTopology : FiniteControlTopology hiddenSystem where
  context := ()
  listedSigners := [.visibleLeft, .visibleRight]
  listedDomains := [.leftDomain, .rightDomain]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains
    | .visibleLeft => [.leftDomain]
    | .visibleRight => [.rightDomain]
    | .hiddenLeft => [.leftDomain]
  dependencyDomainsNoDup := by
    intro signer
    cases signer <;> simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer with
    | visibleLeft =>
        change domain ∈ [.leftDomain] ↔ domain = .leftDomain
        exact mem_singleton_exact
    | visibleRight =>
        change domain ∈ [.rightDomain] ↔ domain = .rightDomain
        exact mem_singleton_exact
    | hiddenLeft =>
        change domain ∈ [.leftDomain] ↔ domain = .leftDomain
        exact mem_singleton_exact
  dependencyDomainsListed := by
    intro signer domain member
    cases signer <;> simp at member ⊢ <;> simp [member]
  keyCustodyDomain
    | .visibleLeftKey => .leftDomain
    | .visibleRightKey => .rightDomain
    | .hiddenLeftKey => .leftDomain
  processHostDomain
    | .visibleLeftProcess => .leftDomain
    | .visibleRightProcess => .rightDomain
    | .hiddenLeftProcess => .leftDomain
  actorAuthorityRootDomain
    | .visibleLeftActor => .leftDomain
    | .visibleRightActor => .rightDomain
    | .hiddenLeftActor => .leftDomain
  mandatoryControlPaths := by
    intro signer _
    cases signer <;>
      exact
        ⟨mem_singleton_exact.2 rfl,
          mem_singleton_exact.2 rfl,
          mem_singleton_exact.2 rfl⟩
  domainCost := fun _ => 1
  domainCostExact := by
    intro _
    rfl
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

theorem incomplete_topology_omits_an_eligible_signer :
    ¬ ClosedWorldCoverage hiddenSystem incompleteTopology := by
  intro coverage
  have := coverage.eligibleSignerListed .hiddenLeft True.intro
  simp [incompleteTopology] at this

theorem hidden_pair_is_an_eligible_key_quorum :
    EligibleKeyQuorum hiddenSystem hiddenPolicy
      [.visibleLeft, .hiddenLeft] := by
  simp [EligibleKeyQuorum, DistinctKeys, SignerCountMeetsThreshold,
    hiddenPolicy, hiddenSystem]

theorem hidden_signer_creates_affordable_actual_cut :
    IsActualControlCut hiddenSystem hiddenPolicy incompleteTopology
      [.leftDomain] := by
  refine ⟨by simp, ?_⟩
  exact
    ⟨[.visibleLeft, .hiddenLeft],
      hidden_pair_is_an_eligible_key_quorum, by
    intro signer hsigner
    cases signer with
    | visibleLeft =>
        exact ⟨.leftDomain, mem_singleton_exact.2 rfl, rfl⟩
    | visibleRight =>
        simp at hsigner
    | hiddenLeft =>
        exact ⟨.leftDomain, mem_singleton_exact.2 rfl, rfl⟩⟩

/--
The finite listed view can only justify an actual min-cut through the explicit
closed-world proof.  Here the omitted signer creates an affordable real cut.
-/
theorem closed_world_topology_coverage_is_load_bearing :
    ¬ ClosedWorldCoverage hiddenSystem incompleteTopology ∧
      ¬ EffectiveControlCutExceedsBudget
        hiddenSystem hiddenPolicy incompleteTopology := by
  refine ⟨incomplete_topology_omits_an_eligible_signer, ?_⟩
  exact affordable_actual_cut_refutes_effective_authority
    hiddenSystem hiddenPolicy incompleteTopology [.leftDomain]
    hidden_signer_creates_affordable_actual_cut
    (by simp [ControlCutCost, incompleteTopology, hiddenPolicy])

#print axioms minimum_listed_control_cut_is_actual
#print axioms affordable_actual_cut_refutes_effective_authority
#print axioms lawful_act_uses_pre_state_policy
#print axioms lawful_act_effective_control_min_cut_exceeds
#print axioms relaxed_policy_cannot_bind_pre_state
#print axioms relaxed_policy_cannot_form_certificate
#print axioms relaxed_policy_cannot_prove_effective_authority
#print axioms inflated_domain_cost_cannot_match_pre_state
#print axioms two_public_keys_one_custodian_countermodel
#print axioms three_handles_one_signing_key_countermodel
#print axioms distinct_actors_one_process_countermodel
#print axioms three_keys_one_host_countermodel
#print axioms shared_host_cut_cost_equals_budget
#print axioms omitted_shared_host_dependency_cannot_be_exact
#print axioms lawful_pair_has_actual_min_cut_above_budget
#print axioms closed_world_topology_coverage_is_load_bearing

end Residua.RCC.EffectiveAuthorityQuorum.Tests


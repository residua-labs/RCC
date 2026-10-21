/-!
# RCC-34 Effective Authority Quorum

A key-distinct or identity-distinct threshold is not yet an effective authority
quorum.  This finite kernel certifies the minimum control-domain cut needed to
forge an eligible distinct-key signer set and requires that cut to be strictly
larger than the declared threat budget.

The finite logical topology is caller-supplied but proof-carrying.
`ClosedWorldCoverage` seals both all eligible signers and every logical control
domain.  Each signer has one exact finite dependency list that must contain its
declared key-custody, process-host, and actor-authority-root paths.  This is
load-bearing when lifting a minimum cut over listed signers to a minimum cut
over the actual eligible signer world.

Real custody, process, host, operator, and institutional mappings are observed
facts or explicit assumptions outside this kernel.  This file proves min-cut
claims relative to the sealed logical topology; it does not infer physical
independence from distinct keys, actor addresses, or process handles.

Constructive Prelude-only Lean 4.14; no Mathlib or repository
detector/registry integration.
-/

namespace Residua.RCC.EffectiveAuthorityQuorum

universe u

/--
Typed signer metadata.  This kernel models signer eligibility and key identity,
not act/message-bound signature verification.  `eligible`, `keyOf`, `actorOf`,
and `processOf` are epoch-static projections; changing any of them requires a
new `AuthoritySystem`/epoch rather than reusing a topology context.
-/
structure AuthoritySystem where
  Context : Type u
  Signer : Type u
  KeyQ : Type u
  ActorQ : Type u
  ProcessQ : Type u
  ControlDomain : Type u
  ActQ : Type u
  eligible : Signer → Prop
  keyOf : Signer → KeyQ
  actorOf : Signer → ActorQ
  processOf : Signer → ProcessQ
  /--
  The threshold, threat budget, and domain-cost schedule authorized by the
  pre-state policy at one sealed topology context.
  -/
  thresholdAt : Context → Nat
  threatBudgetAt : Context → Nat
  controlDomainCostAt : Context → ControlDomain → Nat
  /--
  Upstream act-bound verification evidence at the same sealed context.  The
  RCC-39 runtime adapter must refine this relation with concrete signatures,
  message bytes, and an admitted receipt.
  -/
  upstreamVerifiedAt : Context → ActQ → List Signer → Prop
  /--
  The authoritative logical dependency relation at one sealed topology
  context.  Concrete extraction and physical truth are refinement/assumption
  obligations outside this relational kernel.
  -/
  controlDepends : Context → Signer → ControlDomain → Prop

/-- Threshold and adversarial control-domain budget declared by policy. -/
structure AuthorityPolicy (S : AuthoritySystem) where
  threshold : Nat
  threatBudget : Nat

/-- Abstract boundary for act-bound signer verification supplied upstream. -/
def UpstreamVerifiedAt (S : AuthoritySystem)
    (context : S.Context) (act : S.ActQ)
    (signers : List S.Signer) : Prop :=
  S.upstreamVerifiedAt context act signers

/--
A finite logical control topology.

`dependencyDomains` is the complete dependency relation used by the kernel,
not a permissive predicate that may have an unsealed scanner behind it.
`keyCustodyDomain`, `processHostDomain`, and `actorAuthorityRootDomain` expose
the three mandatory control paths.  Additional dependencies may be listed, but
none of these paths may be omitted.

The lists are internally sealed here; `ClosedWorldCoverage` separately proves
that they cover the full eligible signer and logical-domain carriers.  Cut
costs must equal the pre-state cost model selected by the same context.
-/
structure FiniteControlTopology (S : AuthoritySystem) where
  context : S.Context
  listedSigners : List S.Signer
  listedDomains : List S.ControlDomain
  listedSignersNoDup : listedSigners.Nodup
  listedDomainsNoDup : listedDomains.Nodup
  dependencyDomains : S.Signer → List S.ControlDomain
  dependencyDomainsNoDup :
    ∀ signer, (dependencyDomains signer).Nodup
  dependencyDomainsExact :
    ∀ signer domain,
      domain ∈ dependencyDomains signer ↔
        S.controlDepends context signer domain
  dependencyDomainsListed :
    ∀ signer domain,
      domain ∈ dependencyDomains signer → domain ∈ listedDomains
  keyCustodyDomain : S.KeyQ → S.ControlDomain
  processHostDomain : S.ProcessQ → S.ControlDomain
  actorAuthorityRootDomain : S.ActorQ → S.ControlDomain
  mandatoryControlPaths :
    ∀ signer, S.eligible signer →
      keyCustodyDomain (S.keyOf signer) ∈ dependencyDomains signer ∧
        processHostDomain (S.processOf signer) ∈ dependencyDomains signer ∧
          actorAuthorityRootDomain (S.actorOf signer) ∈
            dependencyDomains signer
  domainCost : S.ControlDomain → Nat
  domainCostExact :
    ∀ domain,
      domainCost domain = S.controlDomainCostAt context domain
  domainCostPositive : ∀ domain, 0 < domainCost domain

/--
The concrete policy used by a certificate is exactly the policy authorized at
the topology's sealed pre-state context.

This is the local RCC-34 binding.  Deriving the context and its policy from a
durable RCC-39 admission receipt remains a downstream refinement obligation.
-/
def PolicyBoundAt (S : AuthoritySystem)
    (topology : FiniteControlTopology S)
    (policy : AuthorityPolicy S) : Prop :=
  policy.threshold = S.thresholdAt topology.context ∧
    policy.threatBudget = S.threatBudgetAt topology.context

/--
Closed-world certificate for the two quantified carriers used by RCC-34.

The domain clause is the load-bearing negative-claim premise: a caller cannot
seal only a convenient subset of the logical control-domain carrier and call
the resulting minimum global.
-/
structure ClosedWorldCoverage (S : AuthoritySystem)
    (topology : FiniteControlTopology S) : Prop where
  eligibleSignerListed :
    ∀ signer, S.eligible signer → signer ∈ topology.listedSigners
  domainListed :
    ∀ domain, domain ∈ topology.listedDomains

/-- Naive signer/handle count, weaker than an eligible distinct-key quorum. -/
def SignerCountMeetsThreshold {S : AuthoritySystem}
    (policy : AuthorityPolicy S) (signers : List S.Signer) : Prop :=
  policy.threshold ≤ signers.length

/-- All signing keys in a proposed quorum are distinct. -/
def DistinctKeys (S : AuthoritySystem) (signers : List S.Signer) : Prop :=
  (signers.map S.keyOf).Nodup

/-- Logical actor-address distinctness; this is not control independence. -/
def DistinctActors (S : AuthoritySystem) (signers : List S.Signer) : Prop :=
  (signers.map S.actorOf).Nodup

/-- Process-handle distinctness; this is not physical or operator independence. -/
def DistinctProcesses (S : AuthoritySystem) (signers : List S.Signer) : Prop :=
  (signers.map S.processOf).Nodup

/--
An eligible distinct-key signer set has no duplicate signer or key, reaches
the threshold, and contains only eligible signers.  It does not assert that
any signature was checked against a particular act or message.  Actor and
process counts are intentionally absent from this definition.
-/
def EligibleKeyQuorum (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (signers : List S.Signer) : Prop :=
  signers.Nodup ∧
    DistinctKeys S signers ∧
    SignerCountMeetsThreshold policy signers ∧
    ∀ signer, signer ∈ signers → S.eligible signer

/-- A finite fault-domain set controls a signer through any sealed dependency. -/
def ControlledBy {S : AuthoritySystem}
    (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) (signer : S.Signer) : Prop :=
  ∃ domain,
    domain ∈ domains ∧
      S.controlDepends topology.context signer domain

/-- Additive policy cost of a canonical logical control-domain cut. -/
def ControlCutCost {S : AuthoritySystem}
    (topology : FiniteControlTopology S) :
    List S.ControlDomain → Nat
  | [] => 0
  | domain :: rest =>
      topology.domainCost domain + ControlCutCost topology rest

/-- An actual forgery may use any eligible signer, listed or not. -/
def CanForgeActual (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop :=
  ∃ signers,
    EligibleKeyQuorum S policy signers ∧
      ∀ signer, signer ∈ signers → ControlledBy topology domains signer

/-- Finite analysis restricts the forged quorum to topology-listed signers. -/
def CanForgeListed (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop :=
  ∃ signers,
    EligibleKeyQuorum S policy signers ∧
      (∀ signer, signer ∈ signers → signer ∈ topology.listedSigners) ∧
      ∀ signer, signer ∈ signers → ControlledBy topology domains signer

/-- A duplicate-free domain set capable of forging an actual lawful quorum. -/
structure IsActualControlCut (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop where
  domainsNodup : domains.Nodup
  canForge : CanForgeActual S policy topology domains

/-- A duplicate-free domain set capable of forging within the finite listing. -/
structure IsListedControlCut (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop where
  domainsNodup : domains.Nodup
  canForge : CanForgeListed S policy topology domains

/-- A smallest actual control-domain set capable of forging a lawful quorum. -/
structure IsMinimumActualControlCut (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop where
  isCut : IsActualControlCut S policy topology domains
  minimal :
    ∀ candidate,
      IsActualControlCut S policy topology candidate →
        ControlCutCost topology domains ≤ ControlCutCost topology candidate

/-- A smallest listed control-domain set capable of forging a lawful quorum. -/
structure IsMinimumListedControlCut (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain) : Prop where
  isCut : IsListedControlCut S policy topology domains
  minimal :
    ∀ candidate,
      IsListedControlCut S policy topology candidate →
        ControlCutCost topology domains ≤ ControlCutCost topology candidate

/-- The normative RCC-34 condition over the actual eligible signer world. -/
def EffectiveControlCutExceedsBudget (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S) : Prop :=
  PolicyBoundAt S topology policy ∧
    ∃ domains,
      IsMinimumActualControlCut S policy topology domains ∧
        policy.threatBudget < ControlCutCost topology domains

/-- Listed forging always implies actual forging. -/
theorem listed_forgery_is_actual
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain)
    (hforge : CanForgeListed S policy topology domains) :
    CanForgeActual S policy topology domains := by
  rcases hforge with ⟨signers, hlawful, hlisted, hcontrolled⟩
  exact ⟨signers, hlawful, hcontrolled⟩

/--
Closed-world coverage is exactly the premise needed to bring an arbitrary
actual forged quorum back into the finite signer listing.
-/
theorem actual_forgery_is_listed_of_closed_world
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (coverage : ClosedWorldCoverage S topology)
    (domains : List S.ControlDomain)
    (hforge : CanForgeActual S policy topology domains) :
    CanForgeListed S policy topology domains := by
  rcases hforge with ⟨signers, hlawful, hcontrolled⟩
  refine ⟨signers, hlawful, ?_, hcontrolled⟩
  intro signer hsigner
  exact coverage.eligibleSignerListed signer
    (hlawful.2.2.2 signer hsigner)

/--
A listed minimum cut is an actual minimum cut only under closed-world topology
coverage.  Removing `coverage` makes the actual-to-listed step unavailable.
-/
theorem minimum_listed_control_cut_is_actual
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (coverage : ClosedWorldCoverage S topology)
    (domains : List S.ControlDomain)
    (minimum : IsMinimumListedControlCut S policy topology domains) :
    IsMinimumActualControlCut S policy topology domains := by
  refine ⟨?_, ?_⟩
  · exact
      ⟨minimum.isCut.domainsNodup,
        listed_forgery_is_actual
          S policy topology domains minimum.isCut.canForge⟩
  · intro candidate hcandidate
    apply minimum.minimal candidate
    exact
      ⟨hcandidate.domainsNodup,
        actual_forgery_is_listed_of_closed_world
          S policy topology coverage candidate hcandidate.canForge⟩

/--
Any actual forgery cut at or below the threat budget refutes the existence of a
minimum actual cut strictly above that budget.
-/
theorem affordable_actual_cut_refutes_effective_authority
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (domains : List S.ControlDomain)
    (hcut : IsActualControlCut S policy topology domains)
    (haffordable :
      ControlCutCost topology domains ≤ policy.threatBudget) :
    ¬ EffectiveControlCutExceedsBudget S policy topology := by
  intro ⟨_, heffective⟩
  rcases heffective with ⟨minimumDomains, hminimum, habove⟩
  have hminimumAffordable :
      ControlCutCost topology minimumDomains ≤ policy.threatBudget :=
    Nat.le_trans (hminimum.minimal domains hcut) haffordable
  exact (Nat.not_lt_of_ge hminimumAffordable) habove

/-- Unit-cost topology cuts have cost exactly equal to cardinality. -/
theorem control_cut_cost_eq_length_of_unit_cost
    {S : AuthoritySystem}
    (topology : FiniteControlTopology S)
    (unitCost : ∀ domain, topology.domainCost domain = 1) :
    ∀ domains,
      ControlCutCost topology domains = domains.length := by
  intro domains
  induction domains with
  | nil =>
      rfl
  | cons domain rest ih =>
      simp only [ControlCutCost, unitCost domain, ih, List.length_cons]
      exact Nat.add_comm 1 rest.length

/-- A finite list containing an element has length at least one. -/
theorem one_le_length_of_member {α : Type u}
    {element : α} {items : List α} (hmember : element ∈ items) :
    1 ≤ items.length := by
  cases items with
  | nil => simp at hmember
  | cons head tail => simp

/-- Two distinct members force a finite list to have length at least two. -/
theorem two_le_length_of_distinct_members {α : Type u}
    {left right : α} {items : List α}
    (hdistinct : left ≠ right)
    (hleft : left ∈ items) (hright : right ∈ items) :
    2 ≤ items.length := by
  cases items with
  | nil => simp at hleft
  | cons head tail =>
      cases tail with
      | nil =>
          have hleftEq : left = head := by simpa using hleft
          have hrightEq : right = head := by simpa using hright
          exact (hdistinct (hleftEq.trans hrightEq.symm)).elim
      | cons second rest => simp

/--
A duplicate-free list of length at least two whose members all lie in a
two-element universe contains both universe elements.
-/
theorem pair_members_of_nodup_subset_length {α : Type u}
    {left right : α} {items : List α}
    (hnodup : items.Nodup)
    (hsubset : ∀ item, item ∈ items → item = left ∨ item = right)
    (hlength : 2 ≤ items.length) :
    left ∈ items ∧ right ∈ items := by
  cases items with
  | nil => simp at hlength
  | cons first tail =>
      cases tail with
      | nil => simp at hlength
      | cons second rest =>
          have hfirst : first = left ∨ first = right :=
            hsubset first (by simp)
          have hsecond : second = left ∨ second = right :=
            hsubset second (by simp)
          have hne : first ≠ second := by
            intro heq
            subst second
            simp at hnodup
          rcases hfirst with hfirstLeft | hfirstRight <;>
            rcases hsecond with hsecondLeft | hsecondRight
          · exact
              (hne (hfirstLeft.trans hsecondLeft.symm)).elim
          · constructor
            · simp [hfirstLeft]
            · simp [hsecondRight]
          · constructor
            · simp [hsecondLeft]
            · simp [hfirstRight]
          · exact
              (hne (hfirstRight.trans hsecondRight.symm)).elim

/--
A proof-carrying effective-authority certificate.  Key or actor counts cannot
construct this object without the topology coverage and control-cut proofs.
-/
structure EffectiveAuthorityCertificate (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S) where
  preStatePolicy : PolicyBoundAt S topology policy
  topologyCoverage : ClosedWorldCoverage S topology
  minimumCut : List S.ControlDomain
  minimumListedCut :
    IsMinimumListedControlCut S policy topology minimumCut
  exceedsThreatBudget :
    policy.threatBudget < ControlCutCost topology minimumCut

/--
An authority act carries an upstream-verified eligible key quorum and an
effective-authority certificate.  Binding concrete signatures to the act bytes
belongs to the downstream RCC-39 admission receipt.
-/
structure LawfulAuthorityAct (S : AuthoritySystem)
    (policy : AuthorityPolicy S) (topology : FiniteControlTopology S) where
  act : S.ActQ
  signers : List S.Signer
  upstreamVerified :
    UpstreamVerifiedAt S topology.context act signers
  eligibleKeyQuorum : EligibleKeyQuorum S policy signers
  signersListed :
    ∀ signer, signer ∈ signers → signer ∈ topology.listedSigners
  effectiveAuthority : EffectiveAuthorityCertificate S policy topology

/-- Every certified lawful act uses the policy authorized by its sealed pre-state context. -/
theorem lawful_act_uses_pre_state_policy
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (act : LawfulAuthorityAct S policy topology) :
    PolicyBoundAt S topology policy :=
  act.effectiveAuthority.preStatePolicy

/--
RCC-34: the effective control-domain min-cut of every lawful authority act is
strictly larger than the policy's declared threat budget.
-/
theorem lawful_act_effective_control_min_cut_exceeds
    (S : AuthoritySystem) (policy : AuthorityPolicy S)
    (topology : FiniteControlTopology S)
    (act : LawfulAuthorityAct S policy topology) :
    EffectiveControlCutExceedsBudget S policy topology := by
  exact
    ⟨act.effectiveAuthority.preStatePolicy,
      act.effectiveAuthority.minimumCut,
        minimum_listed_control_cut_is_actual
          S policy topology act.effectiveAuthority.topologyCoverage
          act.effectiveAuthority.minimumCut
          act.effectiveAuthority.minimumListedCut,
        act.effectiveAuthority.exceedsThreatBudget⟩

end Residua.RCC.EffectiveAuthorityQuorum

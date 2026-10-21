import RCC.QuorumFinalityAdapter
import RCCTests.QuorumIntersectionSafety
import RCCTests.DurableVoteLock

/-!
# RCC-40 ↔ RCC-41 Quorum Finality Adapter Tests

The positive witness derives RCC-40 honest non-equivocation from RCC-41
proof-carrying continuity.  The negative witnesses pin the two independent
failure surfaces: an unsafe two-of-three quorum and a same-proposal,
opposite-verdict signer pair with no continuity proof.
-/

namespace Residua.RCC.QuorumFinalityAdapter.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.DurableVoteLock
open Residua.RCC.EffectiveAuthorityQuorum
open Residua.RCC.QuorumIntersectionSafety
open Residua.RCC.QuorumFinalityAdapter
open Residua.RCC.DurableVoteLock.Tests

private theorem mem_singleton_eq {α : Type} {value only : α}
    (listed : value ∈ [only]) : value = only := by
  rcases List.mem_cons.mp listed with equal | impossible
  · exact equal
  · cases impossible

def oneSignerConfig : QuorumConfiguration Token where
  members := [.signerA]
  quorums := [[.signerA]]
  allowedFaultSets := [[]]

def safeReleases :
    List (ReleasedSignature Token exactVoteSignatureScheme) :=
  [releaseP]

def noFaults : List Token := []

theorem one_signer_intersection_safe :
    QuorumIntersectionSafe (quorumSystem oneSignerConfig) := by
  intro first firstLawful second secondLawful fault faultAllowed
  rcases firstLawful with ⟨firstListed, _, _⟩
  rcases secondLawful with ⟨secondListed, _, _⟩
  rcases faultAllowed with ⟨faultListed, _, _⟩
  change first ∈ [[.signerA]] at firstListed
  change second ∈ [[.signerA]] at secondListed
  change fault ∈ [[]] at faultListed
  have firstEq : first = [.signerA] := mem_singleton_eq firstListed
  have secondEq : second = [.signerA] := mem_singleton_eq secondListed
  have faultEq : fault = [] := mem_singleton_eq faultListed
  subst first
  subst second
  subst fault
  exact ⟨.signerA, by simp, by simp, by simp⟩

theorem no_faults_allowed :
    AllowedFaultSet (quorumSystem oneSignerConfig) noFaults := by
  refine
    ⟨List.mem_cons.mpr (Or.inl rfl), .nil, ?_⟩
  intro signer impossible
  cases impossible

def safeContinuity :
    HonestSignerContinuity
      oneSignerConfig exactVoteSignatureScheme safeReleases noFaults where
  pairwise := by
    intro first firstIn second secondIn sameSigner signerMember signerHonest
      sameSlot
    simp [safeReleases] at firstIn secondIn
    subst first
    subst second
    exact {
      sameSigner := rfl
      lockContinuity := .forward (.restore rfl)
    }

def safeAdapter :
    QuorumFinalityAdapter
      oneSignerConfig exactVoteSignatureScheme safeReleases noFaults where
  intersectionSafe := one_signer_intersection_safe
  faultAllowed := no_faults_allowed
  continuity := safeContinuity

def proposalSlot : DecisionSlot Token :=
  decisionSlot (releasedVote releaseP)

def proposalJudgment : CanonicalJudgment Token :=
  canonicalJudgment (releasedVote releaseP)

def validQC :
    ValidQC
      (quorumSystem oneSignerConfig)
      (releaseLocks oneSignerConfig safeReleases)
      proposalSlot proposalJudgment where
  quorum := [.signerA]
  lawful := by
    refine
      ⟨List.mem_cons.mpr (Or.inl rfl),
        .cons (by simp) .nil, ?_⟩
    intro signer listed
    simpa [quorumSystem, oneSignerConfig] using listed
  votes := by
    intro signer listed
    have signerEq : signer = .signerA := by
      simpa using listed
    subst signer
    refine ⟨releaseLockedVote oneSignerConfig releaseP, ?_, rfl, rfl, rfl⟩
    simp [releaseLocks, safeReleases]

def quorumProposal :
    Proposal (DecisionSlot Token) Token (CanonicalJudgment Token) where
  slot := proposalSlot
  expectedParent := .headA
  judgment := proposalJudgment

/-- A separately named same-slot proposal used to construct a second finality. -/
def quorumProposalReplica :
    Proposal (DecisionSlot Token) Token (CanonicalJudgment Token) where
  slot := proposalSlot
  expectedParent := .headA
  judgment := proposalJudgment

/-! ## RCC-34 effective-authority realization -/

inductive AuthorityContext
  | current
  | other
  deriving DecidableEq

def authoritySystem : AuthoritySystem where
  Context := AuthorityContext
  Signer := Unit
  KeyQ := Unit
  ActorQ := Unit
  ProcessQ := Unit
  ControlDomain := Unit
  ActQ := Token
  eligible := fun _ => True
  keyOf := fun _ => ()
  actorOf := fun _ => ()
  processOf := fun _ => ()
  thresholdAt := fun _ => 1
  threatBudgetAt := fun _ => 0
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt :=
    fun _ act signers => act = .proposalP ∧ signers = [()]
  controlDepends := fun _ _ _ => True

def authorityPolicy : AuthorityPolicy authoritySystem where
  threshold := 1
  threatBudget := 0

def authorityTopology : FiniteControlTopology authoritySystem where
  context := .current
  listedSigners := [()]
  listedDomains := [()]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains := fun _ => [()]
  dependencyDomainsNoDup := by
    intro _
    simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer
    cases domain
    constructor
    · intro _
      trivial
    · intro _
      exact List.mem_cons.mpr (Or.inl rfl)
  dependencyDomainsListed := by
    intro signer domain _
    cases signer
    cases domain
    exact List.mem_cons.mpr (Or.inl rfl)
  keyCustodyDomain := fun _ => ()
  processHostDomain := fun _ => ()
  actorAuthorityRootDomain := fun _ => ()
  mandatoryControlPaths := by
    intro signer _
    cases signer
    simp
  domainCost := fun _ => 1
  domainCostExact := by
    intro domain
    cases domain
    rfl
  domainCostPositive := by
    intro domain
    cases domain
    decide

def authorityCoverage :
    ClosedWorldCoverage authoritySystem authorityTopology where
  eligibleSignerListed := by
    intro signer _
    cases signer
    exact List.mem_cons.mpr (Or.inl rfl)
  domainListed := by
    intro domain
    cases domain
    exact List.mem_cons.mpr (Or.inl rfl)

theorem singleton_domain_is_listed_cut :
    IsListedControlCut authoritySystem authorityPolicy authorityTopology
      [()] := by
  refine ⟨by simp, ?_⟩
  exact
    ⟨[()],
      by
        simp [EligibleKeyQuorum, DistinctKeys,
          SignerCountMeetsThreshold, authoritySystem, authorityPolicy],
      by
        intro signer _
        cases signer
        simp [authorityTopology],
      by
        intro signer _
        cases signer
        exact ⟨(), by simp, by simp [authoritySystem, authorityTopology]⟩⟩

theorem singleton_domain_cut_is_minimum :
    IsMinimumListedControlCut
      authoritySystem authorityPolicy authorityTopology [()] := by
  refine ⟨singleton_domain_is_listed_cut, ?_⟩
  intro candidate candidateCut
  rcases candidateCut.canForge with
    ⟨signers, lawful, _, controlled⟩
  have signerPresent : () ∈ signers := by
    cases signers with
    | nil =>
        simp [EligibleKeyQuorum, SignerCountMeetsThreshold,
          authorityPolicy] at lawful
    | cons signer rest =>
        cases signer
        exact List.mem_cons.mpr (Or.inl rfl)
  obtain ⟨domain, domainPresent, _⟩ := controlled () signerPresent
  cases domain
  have oneLe : 1 ≤ candidate.length :=
    one_le_length_of_member domainPresent
  have minimumCost :=
    control_cut_cost_eq_length_of_unit_cost authorityTopology
      (by intro domain; cases domain; rfl) [()]
  have candidateCost :=
    control_cut_cost_eq_length_of_unit_cost authorityTopology
      (by intro domain; cases domain; rfl) candidate
  rw [minimumCost, candidateCost]
  exact oneLe

def authorityCertificate :
    EffectiveAuthorityCertificate
      authoritySystem authorityPolicy authorityTopology where
  preStatePolicy := by
    simp [PolicyBoundAt, authoritySystem, authorityPolicy, authorityTopology]
  topologyCoverage := authorityCoverage
  minimumCut := [()]
  minimumListedCut := singleton_domain_cut_is_minimum
  exceedsThreatBudget := by
    simp [ControlCutCost, authorityTopology, authorityPolicy]

def lawfulAuthorityAct :
    LawfulAuthorityAct
      authoritySystem authorityPolicy authorityTopology where
  act := .proposalP
  signers := [()]
  upstreamVerified := by
    simp [UpstreamVerifiedAt, authoritySystem]
  eligibleKeyQuorum := by
    simp [EligibleKeyQuorum, DistinctKeys,
      SignerCountMeetsThreshold, authoritySystem, authorityPolicy]
  signersListed := by
    intro signer _
    cases signer
    simp [authorityTopology]
  effectiveAuthority := authorityCertificate

def authorityBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := fun _ => .signerA
  signerQInjective := by
    intro first second _
    cases first
    cases second
    rfl
  actFor := fun proposal => proposal.judgment.proposalClassQ
  configQ := fun _ => .configA
  policyQ := fun _ => .policyA
  contextEpochQ
    | .current => .epochA
    | .other => .epochB

def effectiveAuthorityEvidence :
    EffectiveQuorumAuthorityEvidence
      authoritySystem authorityPolicy authorityTopology authorityBinding
      safeAdapter quorumProposal where
  lawfulAct := lawfulAuthorityAct
  qc := validQC
  actBound := rfl
  signerSetBound := by
    intro signer
    have mapped :
        lawfulAuthorityAct.signers.map authorityBinding.signerQ =
          [Token.signerA] :=
      rfl
    have quorum : validQC.quorum = [Token.signerA] :=
      rfl
    have listsEqual :
        lawfulAuthorityAct.signers.map authorityBinding.signerQ =
          validQC.quorum :=
      mapped.trans quorum.symm
    exact
      ⟨fun member =>
        Eq.mp (congrArg (fun items => signer ∈ items) listsEqual) member,
      fun member =>
        Eq.mpr (congrArg (fun items => signer ∈ items) listsEqual) member⟩
  configBound := rfl
  epochBound := rfl
  policyBound := rfl

def effectiveAuthorityEvidenceReplica :
    EffectiveQuorumAuthorityEvidence
      authoritySystem authorityPolicy authorityTopology authorityBinding
      safeAdapter quorumProposalReplica :=
  effectiveAuthorityEvidence

/-! ## Independent canonical linearization -/

inductive TestLinearizationReceipt :
    Proposal (DecisionSlot Token) Token (CanonicalJudgment Token) →
      Token → Type
  | current : TestLinearizationReceipt quorumProposal .headA

def canonicalLinearizer :
    CanonicalLinearizer
      (DecisionSlot Token) Token (CanonicalJudgment Token) where
  canonicalHead := .headA
  Receipt := TestLinearizationReceipt

def quorumLinearizationReceipt :
    canonicalLinearizer.Receipt
      quorumProposal canonicalLinearizer.canonicalHead :=
  .current

def quorumLinearizationReceiptReplica :
    canonicalLinearizer.Receipt
      quorumProposalReplica canonicalLinearizer.canonicalHead :=
  .current

def quorumFinality :
    QuorumFinalityCert
      authoritySystem authorityPolicy authorityTopology authorityBinding
      safeAdapter canonicalLinearizer quorumProposal :=
  certifyAuthorizedQC
    effectiveAuthorityEvidence quorumLinearizationReceipt rfl

/-- A second finality certificate, constructed independently for the replica proposal. -/
def quorumFinalityReplica :
    QuorumFinalityCert
      authoritySystem authorityPolicy authorityTopology authorityBinding
      safeAdapter canonicalLinearizer quorumProposalReplica :=
  certifyAuthorizedQC
    effectiveAuthorityEvidenceReplica quorumLinearizationReceiptReplica rfl

theorem positive_same_slot_finalities_agree :
    quorumProposal.judgment = quorumProposal.judgment :=
  same_slot_quorum_finalities_judgment_equivalent
    quorumFinality quorumFinality rfl

theorem positive_distinct_same_slot_finalities_agree :
    quorumFinality.finality.authorization.proposal.judgment =
      quorumFinalityReplica.finality.authorization.proposal.judgment :=
  same_slot_quorum_finalities_judgment_equivalent
    quorumFinality quorumFinalityReplica rfl

theorem finalized_quorum_implies_authorized :
    AuthorizedWithReceipt
      (DecisionSlot Token) Token (CanonicalJudgment Token)
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter)
      quorumProposal :=
  quorum_finality_implies_authorized quorumFinality

theorem finality_retains_effective_authority_act :
    quorumFinality.finality.authorization.authorityEvidence.lawfulAct.act =
      Token.proposalP :=
  rfl

theorem finality_retains_exact_qc :
    quorumFinality.finality.authorization.authorityEvidence.qc.quorum =
      [.signerA] :=
  rfl

theorem finality_uses_independent_canonical_head :
    quorumFinality.finality.authorization.proposal.expectedParent =
      canonicalLinearizer.canonicalHead :=
  quorumFinality.finality.parentBound

/-! ## Authority-coordinate and linearizer countermodels -/

def wrongConfigBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := authorityBinding.signerQ
  signerQInjective := authorityBinding.signerQInjective
  actFor := authorityBinding.actFor
  configQ := fun _ => .configB
  policyQ := authorityBinding.policyQ
  contextEpochQ := authorityBinding.contextEpochQ

theorem wrong_config_cannot_construct_authority_evidence :
    ¬ Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology wrongConfigBinding
        safeAdapter quorumProposal) := by
  rintro ⟨evidence⟩
  have bound := evidence.configBound
  change Token.configA = Token.configB at bound
  exact (by decide : Token.configA ≠ Token.configB) bound

def wrongEpochBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := authorityBinding.signerQ
  signerQInjective := authorityBinding.signerQInjective
  actFor := authorityBinding.actFor
  configQ := authorityBinding.configQ
  policyQ := authorityBinding.policyQ
  contextEpochQ := fun _ => .epochB

theorem wrong_context_epoch_cannot_construct_authority_evidence :
    ¬ Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology wrongEpochBinding
        safeAdapter quorumProposal) := by
  rintro ⟨evidence⟩
  have bound := evidence.epochBound
  change Token.epochA = Token.epochB at bound
  exact (by decide : Token.epochA ≠ Token.epochB) bound

def wrongPolicyBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := authorityBinding.signerQ
  signerQInjective := authorityBinding.signerQInjective
  actFor := authorityBinding.actFor
  configQ := authorityBinding.configQ
  policyQ := fun _ => .policyB
  contextEpochQ := authorityBinding.contextEpochQ

theorem wrong_policy_cannot_construct_authority_evidence :
    ¬ Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology wrongPolicyBinding
        safeAdapter quorumProposal) := by
  rintro ⟨evidence⟩
  have bound := evidence.policyBound
  change Token.policyA = Token.policyB at bound
  exact (by decide : Token.policyA ≠ Token.policyB) bound

def wrongActBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := authorityBinding.signerQ
  signerQInjective := authorityBinding.signerQInjective
  actFor := fun _ => .proposalQ
  configQ := authorityBinding.configQ
  policyQ := authorityBinding.policyQ
  contextEpochQ := authorityBinding.contextEpochQ

theorem wrong_act_cannot_construct_authority_evidence :
    ¬ Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology wrongActBinding
        safeAdapter quorumProposal) := by
  rintro ⟨evidence⟩
  have verifiedBundle :
      evidence.lawfulAct.act = Token.proposalP ∧
        evidence.lawfulAct.signers = [()] := by
    exact evidence.lawfulAct.upstreamVerified
  have verified :
      evidence.lawfulAct.act = Token.proposalP :=
    verifiedBundle.1
  have bound :
      evidence.lawfulAct.act = Token.proposalQ := by
    simpa [wrongActBinding] using evidence.actBound
  exact (by decide : Token.proposalP ≠ Token.proposalQ)
    (verified.symm.trans bound)

def wrongSignerBinding :
    EffectiveAuthorityBinding Token authoritySystem where
  signerQ := fun _ => .proposalQ
  signerQInjective := by
    intro first second _
    cases first
    cases second
    rfl
  actFor := authorityBinding.actFor
  configQ := authorityBinding.configQ
  policyQ := authorityBinding.policyQ
  contextEpochQ := authorityBinding.contextEpochQ

theorem wrong_signer_set_cannot_construct_authority_evidence :
    ¬ Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology wrongSignerBinding
        safeAdapter quorumProposal) := by
  rintro ⟨evidence⟩
  have verifiedBundle :
      evidence.lawfulAct.act = Token.proposalP ∧
        evidence.lawfulAct.signers = [()] := by
    exact evidence.lawfulAct.upstreamVerified
  have signers :
      evidence.lawfulAct.signers = [()] :=
    verifiedBundle.2
  have mismatch := (evidence.signerSetBound Token.proposalQ).1
  have leftMembership :
      Token.proposalQ ∈
        evidence.lawfulAct.signers.map wrongSignerBinding.signerQ := by
    rw [signers]
    change Token.proposalQ ∈ [Token.proposalQ]
    exact List.mem_cons.mpr (Or.inl rfl)
  have impossible : Token.proposalQ ∈ evidence.qc.quorum :=
    mismatch leftMembership
  have quorumListed := evidence.qc.lawful.1
  change evidence.qc.quorum ∈ [[.signerA]] at quorumListed
  have quorumBound : evidence.qc.quorum = [.signerA] :=
    mem_singleton_eq quorumListed
  rw [quorumBound] at impossible
  have impossibleEquality : Token.proposalQ = Token.signerA :=
    mem_singleton_eq impossible
  exact (by decide : Token.proposalQ ≠ Token.signerA) impossibleEquality

def staleProposal :
    Proposal (DecisionSlot Token) Token (CanonicalJudgment Token) where
  slot := proposalSlot
  expectedParent := .headB
  judgment := proposalJudgment

def staleEffectiveAuthorityEvidence :
    EffectiveQuorumAuthorityEvidence
      authoritySystem authorityPolicy authorityTopology authorityBinding
      safeAdapter staleProposal where
  lawfulAct := lawfulAuthorityAct
  qc := validQC
  actBound := rfl
  signerSetBound := by
    intro signer
    have mapped :
        lawfulAuthorityAct.signers.map authorityBinding.signerQ =
          [Token.signerA] :=
      rfl
    have quorum : validQC.quorum = [Token.signerA] :=
      rfl
    have listsEqual :
        lawfulAuthorityAct.signers.map authorityBinding.signerQ =
          validQC.quorum :=
      mapped.trans quorum.symm
    exact
      ⟨fun member =>
        Eq.mp (congrArg (fun items => signer ∈ items) listsEqual) member,
      fun member =>
        Eq.mpr (congrArg (fun items => signer ∈ items) listsEqual) member⟩
  configBound := rfl
  epochBound := rfl
  policyBound := rfl

theorem stale_parent_authorized_but_not_finalized :
    Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter staleProposal) ∧
      ¬ Nonempty
        (QuorumFinalityCert
          authoritySystem authorityPolicy authorityTopology authorityBinding
          safeAdapter canonicalLinearizer staleProposal) := by
  refine ⟨⟨staleEffectiveAuthorityEvidence⟩, ?_⟩
  rintro ⟨certificate⟩
  have proposalParentBound :
      staleProposal.expectedParent =
        certificate.finality.authorization.proposal.expectedParent :=
    congrArg Proposal.expectedParent certificate.proposalBound.symm
  have impossible :
      staleProposal.expectedParent = canonicalLinearizer.canonicalHead :=
    proposalParentBound.trans certificate.finality.parentBound
  exact (by decide : Token.headB ≠ Token.headA) impossible

def refusingAuthoritySystem : AuthoritySystem where
  Context := AuthorityContext
  Signer := Unit
  KeyQ := Unit
  ActorQ := Unit
  ProcessQ := Unit
  ControlDomain := Unit
  ActQ := Token
  eligible := fun _ => True
  keyOf := fun _ => ()
  actorOf := fun _ => ()
  processOf := fun _ => ()
  thresholdAt := fun _ => 1
  threatBudgetAt := fun _ => 0
  controlDomainCostAt := fun _ _ => 1
  upstreamVerifiedAt := fun _ _ _ => False
  controlDepends := fun _ _ _ => True

def refusingPolicy : AuthorityPolicy refusingAuthoritySystem where
  threshold := 1
  threatBudget := 0

def refusingTopology : FiniteControlTopology refusingAuthoritySystem where
  context := .current
  listedSigners := [()]
  listedDomains := [()]
  listedSignersNoDup := by simp
  listedDomainsNoDup := by simp
  dependencyDomains := fun _ => [()]
  dependencyDomainsNoDup := by
    intro _
    simp
  dependencyDomainsExact := by
    intro signer domain
    cases signer
    cases domain
    constructor
    · intro _
      trivial
    · intro _
      exact List.mem_cons.mpr (Or.inl rfl)
  dependencyDomainsListed := by
    intro signer domain _
    cases signer
    cases domain
    exact List.mem_cons.mpr (Or.inl rfl)
  keyCustodyDomain := fun _ => ()
  processHostDomain := fun _ => ()
  actorAuthorityRootDomain := fun _ => ()
  mandatoryControlPaths := by
    intro signer _
    cases signer
    simp
  domainCost := fun _ => 1
  domainCostExact := by
    intro domain
    cases domain
    rfl
  domainCostPositive := by
    intro domain
    cases domain
    decide

def refusingBinding :
    EffectiveAuthorityBinding Token refusingAuthoritySystem where
  signerQ := fun _ => .signerA
  signerQInjective := by
    intro first second _
    cases first
    cases second
    rfl
  actFor := fun proposal => proposal.judgment.proposalClassQ
  configQ := fun _ => .configA
  policyQ := fun _ => .policyA
  contextEpochQ
    | .current => .epochA
    | .other => .epochB

theorem qc_only_cannot_construct_effective_authority :
    Nonempty
      (ValidQC
        (quorumSystem oneSignerConfig)
        (releaseLocks oneSignerConfig safeReleases)
        quorumProposal.slot quorumProposal.judgment) ∧
      ¬ Nonempty
        (EffectiveQuorumAuthorityEvidence
          refusingAuthoritySystem refusingPolicy refusingTopology
          refusingBinding safeAdapter quorumProposal) := by
  refine ⟨⟨validQC⟩, ?_⟩
  rintro ⟨evidence⟩
  exact evidence.lawfulAct.upstreamVerified

theorem qc_only_cannot_construct_finality :
    ¬ Nonempty
      (QuorumFinalityCert
        refusingAuthoritySystem refusingPolicy refusingTopology
        refusingBinding safeAdapter canonicalLinearizer quorumProposal) := by
  rintro ⟨certificate⟩
  exact
    certificate.finality.authorization.authorityEvidence.lawfulAct.upstreamVerified

theorem absent_linearizer_receipt_prevents_finality :
    let noReceiptLinearizer :
        CanonicalLinearizer
          (DecisionSlot Token) Token (CanonicalJudgment Token) := {
      canonicalHead := .headA
      Receipt := fun _ _ => Empty
    }
    ¬ Nonempty
      (QuorumFinalityCert
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter noReceiptLinearizer quorumProposal) := by
  dsimp
  rintro ⟨certificate⟩
  exact Empty.elim certificate.finality.linearizationEvidence.receipt

/--
CM-RCC40-ADAPTER-01: the existing two-of-three, one-fault split cannot supply
the adapter's RCC-40 intersection proof.
-/
theorem two_of_three_faulty_split_still_unsafe :
    ¬ QuorumIntersectionSafe
      Residua.RCC.QuorumIntersectionSafety.Tests.twoOfThree :=
  Residua.RCC.QuorumIntersectionSafety.Tests.two_of_three_f_one_general_intersection_fails

def verdictConflictReleases :
    List (ReleasedSignature Token exactVoteSignatureScheme) :=
  [releaseP, releasePVerdictAfterLostLock]

/--
CM-RCC40-ADAPTER-02: removing RCC-41 continuity leaves no honest-signer bridge.
The votes share every decision-slot coordinate, including round and policy, but
their canonical `(proposal, verdict)` judgments conflict.
-/
theorem verdict_only_conflict_has_no_honest_continuity :
    ¬ HonestSignerContinuity
      oneSignerConfig exactVoteSignatureScheme verdictConflictReleases
        noFaults := by
  intro continuity
  have nonfaulty :=
    continuity.pairwise
      releaseP (by simp [verdictConflictReleases])
      releasePVerdictAfterLostLock (by simp [verdictConflictReleases])
      rfl
      (by simp [releasedVote, releaseP, voteP, oneSignerConfig])
      (by simp [noFaults])
      rfl
  exact verdict_only_lost_lock_is_not_nonfaulty nonfaulty

theorem verdict_only_conflict_cannot_construct_adapter :
    ¬ Nonempty
      (QuorumFinalityAdapter
        oneSignerConfig exactVoteSignatureScheme verdictConflictReleases
          noFaults) := by
  rintro ⟨adapter⟩
  exact verdict_only_conflict_has_no_honest_continuity adapter.continuity

theorem verdict_is_part_of_canonical_judgment :
    canonicalJudgment (releasedVote releaseP) ≠
      canonicalJudgment (releasedVote releasePVerdictAfterLostLock) := by
  decide

#print axioms one_signer_intersection_safe
#print axioms honest_signer_continuity_implies_non_equivocation
#print axioms same_slot_quorum_finalities_judgment_equivalent
#print axioms quorum_finality_implies_authorized
#print axioms positive_same_slot_finalities_agree
#print axioms positive_distinct_same_slot_finalities_agree
#print axioms finalized_quorum_implies_authorized
#print axioms finality_retains_effective_authority_act
#print axioms finality_retains_exact_qc
#print axioms finality_uses_independent_canonical_head
#print axioms wrong_config_cannot_construct_authority_evidence
#print axioms wrong_context_epoch_cannot_construct_authority_evidence
#print axioms wrong_policy_cannot_construct_authority_evidence
#print axioms wrong_act_cannot_construct_authority_evidence
#print axioms wrong_signer_set_cannot_construct_authority_evidence
#print axioms stale_parent_authorized_but_not_finalized
#print axioms qc_only_cannot_construct_effective_authority
#print axioms qc_only_cannot_construct_finality
#print axioms absent_linearizer_receipt_prevents_finality
#print axioms two_of_three_faulty_split_still_unsafe
#print axioms verdict_only_conflict_has_no_honest_continuity
#print axioms verdict_only_conflict_cannot_construct_adapter
#print axioms verdict_is_part_of_canonical_judgment

end Residua.RCC.QuorumFinalityAdapter.Tests

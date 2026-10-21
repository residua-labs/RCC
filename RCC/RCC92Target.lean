import RCCTests.QuorumFinalityAdapter

/-! RCC-92 candidate: quorum finality, continuity, and authority binding. -/

namespace Residua.RCC.RCC92Target

universe uQ uSystem uReceipt

open Residua.RCC.QuorumFinalityAdapter.Tests
open Residua.RCC.AuthorizationFinality
open Residua.RCC.DurableVoteLock
open Residua.RCC.EffectiveAuthorityQuorum
open Residua.RCC.QuorumIntersectionSafety
open Residua.RCC.QuorumFinalityAdapter
open Residua.RCC.DurableVoteLock.Tests

def oneSignerIntersectionSafe := one_signer_intersection_safe
def noFaultsAllowed := no_faults_allowed
def sameSlotFinalitiesAgree := positive_distinct_same_slot_finalities_agree
def finalityImpliesAuthorized := finalized_quorum_implies_authorized
def finalityRetainsAct := finality_retains_effective_authority_act
def finalityRetainsQC := finality_retains_exact_qc
def finalityUsesCanonicalHead := finality_uses_independent_canonical_head
def staleParentRefused := stale_parent_authorized_but_not_finalized
def qcOnlyCannotAuthority := qc_only_cannot_construct_effective_authority
def qcOnlyCannotFinality := qc_only_cannot_construct_finality
def absentReceiptRefused := absent_linearizer_receipt_prevents_finality
def unsafeSplitRefused := two_of_three_faulty_split_still_unsafe
def verdictConflictNoContinuity := verdict_only_conflict_has_no_honest_continuity
def verdictConflictNoAdapter := verdict_only_conflict_cannot_construct_adapter
def verdictPartOfJudgment := verdict_is_part_of_canonical_judgment

structure Certificate where
  oneSignerIntersectionSafe :
    QuorumIntersectionSafe (quorumSystem oneSignerConfig)
  noFaultsAllowed :
    AllowedFaultSet (quorumSystem oneSignerConfig) noFaults
  sameSlotFinalitiesAgree :
    ∀ {Q : Type uQ}
      {system : AuthoritySystem.{uSystem}}
      {policy : AuthorityPolicy system}
      {topology : FiniteControlTopology system}
      {binding : EffectiveAuthorityBinding Q system}
      {config : QuorumConfiguration Q}
      {scheme : SignatureScheme Q}
      {releases : List (ReleasedSignature Q scheme)}
      {faultSet : List Q}
      {adapter :
        QuorumFinalityAdapter config scheme releases faultSet}
      {linearizer :
        CanonicalLinearizer.{uQ, uQ, uQ, uReceipt}
          (DecisionSlot Q) Q (CanonicalJudgment Q)}
      {firstProposal secondProposal :
        Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)}
      (first :
        QuorumFinalityCert
          system policy topology binding adapter linearizer firstProposal)
      (second :
        QuorumFinalityCert
          system policy topology binding adapter linearizer secondProposal)
      (sameSlot : firstProposal.slot = secondProposal.slot),
      first.finality.authorization.proposal.judgment =
        second.finality.authorization.proposal.judgment
  finalityImpliesAuthorized :
    AuthorizedWithReceipt
      (DecisionSlot Token) Token (CanonicalJudgment Token)
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter)
      quorumProposal
  finalityRetainsAct :
    quorumFinality.finality.authorization.authorityEvidence.lawfulAct.act =
      Token.proposalP
  finalityRetainsQC :
    quorumFinality.finality.authorization.authorityEvidence.qc.quorum =
      [.signerA]
  finalityUsesCanonicalHead :
    quorumFinality.finality.authorization.proposal.expectedParent =
      canonicalLinearizer.canonicalHead
  staleParentRefused :
    Nonempty
      (EffectiveQuorumAuthorityEvidence
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter staleProposal) ∧
      ¬ Nonempty
        (QuorumFinalityCert
          authoritySystem authorityPolicy authorityTopology authorityBinding
          safeAdapter canonicalLinearizer staleProposal)
  qcOnlyCannotAuthority :
    Nonempty
      (ValidQC
        (quorumSystem oneSignerConfig)
        (releaseLocks oneSignerConfig safeReleases)
        quorumProposal.slot quorumProposal.judgment) ∧
      ¬ Nonempty
        (EffectiveQuorumAuthorityEvidence
          refusingAuthoritySystem refusingPolicy refusingTopology
          refusingBinding safeAdapter quorumProposal)
  qcOnlyCannotFinality :
    ¬ Nonempty
      (QuorumFinalityCert
        refusingAuthoritySystem refusingPolicy refusingTopology
        refusingBinding safeAdapter canonicalLinearizer quorumProposal)
  absentReceiptRefused :
    (let noReceiptLinearizer :
        CanonicalLinearizer
          (DecisionSlot Token) Token (CanonicalJudgment Token) := {
      canonicalHead := .headA
      Receipt := fun _ _ => Empty
    }
    ¬ Nonempty
      (QuorumFinalityCert
        authoritySystem authorityPolicy authorityTopology authorityBinding
        safeAdapter noReceiptLinearizer quorumProposal))
  unsafeSplitRefused :
    ¬ QuorumIntersectionSafe
      Residua.RCC.QuorumIntersectionSafety.Tests.twoOfThree
  verdictConflictNoContinuity :
    ¬ HonestSignerContinuity
      oneSignerConfig exactVoteSignatureScheme verdictConflictReleases
        noFaults
  verdictConflictNoAdapter :
    ¬ Nonempty
      (QuorumFinalityAdapter
        oneSignerConfig exactVoteSignatureScheme verdictConflictReleases
          noFaults)
  verdictPartOfJudgment :
    canonicalJudgment (releasedVote releaseP) ≠
      canonicalJudgment (releasedVote releasePVerdictAfterLostLock)

def certificate : Certificate where
  oneSignerIntersectionSafe := one_signer_intersection_safe
  noFaultsAllowed := no_faults_allowed
  sameSlotFinalitiesAgree := by
    intro Q system policy topology binding config scheme releases faultSet
      adapter linearizer firstProposal secondProposal first second sameSlot
    have h := same_slot_quorum_finalities_judgment_equivalent
      first second sameSlot
    simpa [first.proposalBound, second.proposalBound] using h
  finalityImpliesAuthorized := finalized_quorum_implies_authorized
  finalityRetainsAct := finality_retains_effective_authority_act
  finalityRetainsQC := finality_retains_exact_qc
  finalityUsesCanonicalHead := finality_uses_independent_canonical_head
  staleParentRefused := stale_parent_authorized_but_not_finalized
  qcOnlyCannotAuthority := qc_only_cannot_construct_effective_authority
  qcOnlyCannotFinality := qc_only_cannot_construct_finality
  absentReceiptRefused := absent_linearizer_receipt_prevents_finality
  unsafeSplitRefused := two_of_three_faulty_split_still_unsafe
  verdictConflictNoContinuity := verdict_only_conflict_has_no_honest_continuity
  verdictConflictNoAdapter := verdict_only_conflict_cannot_construct_adapter
  verdictPartOfJudgment := verdict_is_part_of_canonical_judgment

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC92Target

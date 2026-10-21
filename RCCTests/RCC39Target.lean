import RCC.RCC39Target

/-! Independent proof-level checks for the RCC-39 target certificate. -/

namespace Residua.RCC.RCC39Target.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.RCC39Target

theorem exact_proposal_binding :
    finality.authorization.proposal.expectedParent = .genesis ∧
      effectSettlement.proposal = finality.authorization.proposal ∧
      historyRecord.proposal = finality.authorization.proposal ∧
      admitted.finality.authorization.proposal = proposal :=
  ⟨(Certificate.canonicalParentBound certificate),
    (Certificate.effectBindsExactProposal certificate),
    (Certificate.historyBindsExactProposal certificate),
    (Certificate.admittedBindsExactProposal certificate)⟩

theorem proposal_domain_is_non_degenerate :
    forgedProposal ≠ proposal :=
  certificate.proposalDomainIsNonDegenerate

theorem forged_evidence_is_refused :
    (¬ authorityEvidenceAccepted proposal false) ∧
      (¬ linearizationEvidenceAccepted proposal .genesis false) ∧
      (¬ effectEvidenceAccepted proposal false) ∧
      (¬ historyEvidenceAccepted proposal false) :=
  ⟨certificate.forgedAuthorityEvidenceRefused,
    certificate.forgedLinearizationEvidenceRefused,
    certificate.forgedEffectEvidenceRefused,
    certificate.forgedHistoryEvidenceRefused⟩

theorem admission_chain_retains_finality_and_authorization :
    FinalizedWithReceipts DemoSlot DemoHead DemoJudgment
      DemoAuthorityEvidence DemoLinearizationEvidence proposal .genesis ∧
      AuthorizedWithReceipt DemoSlot DemoHead DemoJudgment
        DemoAuthorityEvidence proposal :=
  ⟨Certificate.admissionImpliesFinality certificate,
    Certificate.admissionImpliesAuthorization certificate⟩

theorem finality_certificate_keeps_parent_fence :
    finality.authorization.proposal.expectedParent = .genesis :=
  finality.parentBound

#print axioms exact_proposal_binding
#print axioms admission_chain_retains_finality_and_authorization
#print axioms finality_certificate_keeps_parent_fence

end Residua.RCC.RCC39Target.Tests

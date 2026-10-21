import RCC.AuthorizationFinality

/-!
# RCC-39 target package

This finite fixture instantiates the generic authorization/finality boundary
with one slot, one canonical parent head, and one judgment.  It proves the
structural binding chain: authorization, canonical-head linearization,
settled effect evidence, and durable history evidence all refer to the exact
same proposal.  The generic source intentionally does not claim semantic
adequacy of `Unit` evidence; that remains an instance-owned obligation.

This target does not construct threshold authority, a production linearizer,
an external effect protocol, or durable storage.  Those remain RCC-34,
RCC-40..42, RCC-31, and runtime realization obligations.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC39Target

open Residua.RCC.AuthorizationFinality

inductive DemoSlot
  | deploy
  | rollback
  deriving DecidableEq, Repr

inductive DemoHead
  | genesis
  | afterDeploy
  deriving DecidableEq, Repr

inductive DemoJudgment
  | activate
  | deactivate
  deriving DecidableEq, Repr

abbrev DemoProposal := Proposal DemoSlot DemoHead DemoJudgment
/-
The generic authorization/finality kernel is indexed by evidence families, but
does not decide whether an inhabitant is semantically adequate.  A `Unit`
family would therefore prove only index plumbing: every forged receipt would
be indistinguishable from the real one.  Use a two-valued evidence domain and
state the instance-level acceptance predicates explicitly below.
-/
abbrev DemoAuthorityEvidence (_proposal : DemoProposal) := Bool
abbrev DemoLinearizationEvidence (_proposal : DemoProposal) (_head : DemoHead) := Bool
abbrev DemoEffectEvidence (_proposal : DemoProposal) := Bool
abbrev DemoHistoryEvidence (_proposal : DemoProposal) := Bool

def proposal : DemoProposal :=
  { slot := .deploy, expectedParent := .genesis, judgment := .activate }

def forgedProposal : DemoProposal :=
  { slot := .rollback, expectedParent := .genesis, judgment := .deactivate }

theorem forgedProposal_is_distinct : forgedProposal ≠ proposal := by
  intro h
  have hslot : forgedProposal.slot = proposal.slot :=
    congrArg (fun candidate : DemoProposal => candidate.slot) h
  simp [forgedProposal, proposal] at hslot

def authorityEvidenceAccepted
    (p : DemoProposal) (evidence : Bool) : Prop :=
  evidence = true ∧ p = proposal

def linearizationEvidenceAccepted
    (p : DemoProposal) (_head : DemoHead) (evidence : Bool) : Prop :=
  evidence = true ∧ p = proposal

def effectEvidenceAccepted
    (p : DemoProposal) (evidence : Bool) : Prop :=
  evidence = true ∧ p = proposal

def historyEvidenceAccepted
    (p : DemoProposal) (evidence : Bool) : Prop :=
  evidence = true ∧ p = proposal

def authorized :
    AuthorizedProposal DemoSlot DemoHead DemoJudgment DemoAuthorityEvidence :=
  { proposal := proposal, authorityEvidence := true }

def finality :
    FinalityCert DemoSlot DemoHead DemoJudgment DemoAuthorityEvidence
      DemoLinearizationEvidence .genesis :=
  { authorization := authorized
    linearizationEvidence := true
    parentBound := rfl }

def effectSettlement :
    EffectSettlementCert DemoSlot DemoHead DemoJudgment DemoEffectEvidence :=
  { proposal := proposal, effectEvidence := true }

def historyRecord :
    HistoryRecordCert DemoSlot DemoHead DemoJudgment DemoHistoryEvidence :=
  { proposal := proposal, historyEvidence := true }

def admitted :
    AdmittedCert DemoSlot DemoHead DemoJudgment DemoAuthorityEvidence
      DemoLinearizationEvidence DemoEffectEvidence DemoHistoryEvidence .genesis :=
  { finality := finality
    effectSettlement := effectSettlement
    historyRecord := historyRecord
    effectBindsProposal := rfl
    historyBindsProposal := rfl }

structure Certificate : Prop where
  proposalDomainIsNonDegenerate : forgedProposal ≠ proposal
  authorityEvidenceIsAccepted :
    authorityEvidenceAccepted proposal authorized.authorityEvidence
  linearizationEvidenceIsAccepted :
    linearizationEvidenceAccepted proposal .genesis finality.linearizationEvidence
  effectEvidenceIsAccepted :
    effectEvidenceAccepted proposal effectSettlement.effectEvidence
  historyEvidenceIsAccepted :
    historyEvidenceAccepted proposal historyRecord.historyEvidence
  forgedAuthorityEvidenceRefused :
    ¬ authorityEvidenceAccepted proposal false
  forgedLinearizationEvidenceRefused :
    ¬ linearizationEvidenceAccepted proposal .genesis false
  forgedEffectEvidenceRefused :
    ¬ effectEvidenceAccepted proposal false
  forgedHistoryEvidenceRefused :
    ¬ historyEvidenceAccepted proposal false
  forgedProposalAuthorityRefused :
    ¬ authorityEvidenceAccepted forgedProposal true
  forgedProposalLinearizationRefused :
    ¬ linearizationEvidenceAccepted forgedProposal .genesis true
  forgedProposalEffectRefused :
    ¬ effectEvidenceAccepted forgedProposal true
  forgedProposalHistoryRefused :
    ¬ historyEvidenceAccepted forgedProposal true
  canonicalParentBound :
    finality.authorization.proposal.expectedParent = .genesis
  effectBindsExactProposal :
    effectSettlement.proposal = finality.authorization.proposal
  historyBindsExactProposal :
    historyRecord.proposal = finality.authorization.proposal
  admittedBindsExactProposal :
    admitted.finality.authorization.proposal = proposal
  admissionImpliesFinality :
    FinalizedWithReceipts DemoSlot DemoHead DemoJudgment
      DemoAuthorityEvidence DemoLinearizationEvidence proposal .genesis
  admissionImpliesAuthorization :
    AuthorizedWithReceipt DemoSlot DemoHead DemoJudgment
      DemoAuthorityEvidence proposal

def certificate : Certificate where
  proposalDomainIsNonDegenerate := forgedProposal_is_distinct
  authorityEvidenceIsAccepted := ⟨rfl, rfl⟩
  linearizationEvidenceIsAccepted := ⟨rfl, rfl⟩
  effectEvidenceIsAccepted := ⟨rfl, rfl⟩
  historyEvidenceIsAccepted := ⟨rfl, rfl⟩
  forgedAuthorityEvidenceRefused := by
    simp [authorityEvidenceAccepted]
  forgedLinearizationEvidenceRefused := by
    simp [linearizationEvidenceAccepted]
  forgedEffectEvidenceRefused := by
    simp [effectEvidenceAccepted]
  forgedHistoryEvidenceRefused := by
    simp [historyEvidenceAccepted]
  forgedProposalAuthorityRefused := by
    intro h
    simp only [authorityEvidenceAccepted] at h
    exact forgedProposal_is_distinct h.2
  forgedProposalLinearizationRefused := by
    intro h
    simp only [linearizationEvidenceAccepted] at h
    exact forgedProposal_is_distinct h.2
  forgedProposalEffectRefused := by
    intro h
    simp only [effectEvidenceAccepted] at h
    exact forgedProposal_is_distinct h.2
  forgedProposalHistoryRefused := by
    intro h
    simp only [historyEvidenceAccepted] at h
    exact forgedProposal_is_distinct h.2
  canonicalParentBound := finality.parentBound
  effectBindsExactProposal := admitted.effectBindsProposal
  historyBindsExactProposal := admitted.historyBindsProposal
  admittedBindsExactProposal := rfl
  admissionImpliesFinality := admitted_implies_finalized
    (show AdmittedWithReceipts DemoSlot DemoHead DemoJudgment
      DemoAuthorityEvidence DemoLinearizationEvidence DemoEffectEvidence
      DemoHistoryEvidence proposal .genesis from ⟨admitted, rfl⟩)
  admissionImpliesAuthorization := admitted_implies_authorized
    (show AdmittedWithReceipts DemoSlot DemoHead DemoJudgment
      DemoAuthorityEvidence DemoLinearizationEvidence DemoEffectEvidence
      DemoHistoryEvidence proposal .genesis from ⟨admitted, rfl⟩)

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC39Target

import RCC.FailureCoverage

/-!
# RCC-32 Failure-Mode Evidence Coverage Witnesses

The positive witness covers every mandatory failure in a finite, sealed
universe and one opaque evidence context.  Countermodels pin the refusal
surface:

* an empty evidence list;
* a forged, unadmitted evidence item;
* evidence for the wrong failure mode;
* optional-grade evidence presented for a mandatory failure;
* evidence replayed at another context;
* an unsealed / incomplete failure universe.

The artifact does not claim that the declared universe is a complete model of
all real threats.
-/

namespace Residua.RCC.FailureCoverage.Tests

open Residua.RCC.FailureCoverage

inductive DemoFailure
  | specWrong
  | implementationBug
  | sourceCutIncomplete
  | runtimeBug
  deriving DecidableEq

def demoUniverse : FailureUniverse DemoFailure where
  inScope := fun failure =>
    failure = .specWrong ∨
      failure = .implementationBug ∨
      failure = .sourceCutIncomplete
  mandatory := fun failure =>
    failure = .specWrong ∨ failure = .sourceCutIncomplete
  mandatoryInScope := by
    intro failure mandatory
    rcases mandatory with specWrong | sourceCutIncomplete
    · exact Or.inl specWrong
    · exact Or.inr (Or.inr sourceCutIncomplete)
  declared := [.specWrong, .implementationBug, .sourceCutIncomplete]

def demoSeal : FailureUniverseSeal demoUniverse where
  declaredSound := by
    intro failure member
    simp [demoUniverse] at member ⊢
    exact member
  declaredComplete := by
    intro failure inScope
    cases failure <;> simp [demoUniverse] at inScope ⊢

inductive DemoContext
  | current
  | stale
  deriving DecidableEq

inductive DemoEvidence
  | specProof
  | sourceCutSeal
  | implementationParity
  | optionalSpecReview
  | forgedSpecClaim
  deriving DecidableEq

/--
The current context admits four concrete evidence items.  The forged claim is
deliberately denied, and the stale context admits nothing.  Coverage and
admission are independent relations.
-/
def demoSystem :
    FailureEvidenceSystem DemoContext DemoFailure DemoEvidence where
  modelAt := fun _ => demoUniverse
  AdmittedAt := fun context evidence =>
    match context, evidence with
    | .current, .specProof => True
    | .current, .sourceCutSeal => True
    | .current, .implementationParity => True
    | .current, .optionalSpecReview => True
    | _, _ => False
  CoversAt := fun _ evidence failure grade =>
    match evidence, failure, grade with
    | .specProof, .specWrong, .mandatory => True
    | .sourceCutSeal, .sourceCutIncomplete, .mandatory => True
    | .implementationParity, .implementationBug, .mandatory => True
    | .optionalSpecReview, .specWrong, .optional => True
    | .forgedSpecClaim, .specWrong, .mandatory => True
    | _, _, _ => False

def validEvidence : List DemoEvidence :=
  [.specProof, .sourceCutSeal, .implementationParity]

theorem source_cut_seal_is_admitted_mandatory_coverage :
    CoversMandatoryAt demoSystem .current .sourceCutSeal
      .sourceCutIncomplete := by
  simp [CoversMandatoryAt, demoSystem]

def validCoverage :
    FailureCoverageCertificate demoSystem .current demoSeal validEvidence where
  mandatoryNonempty := ⟨.specWrong, Or.inl rfl⟩
  everyMandatoryCovered := by
    intro failure mandatory
    rcases mandatory with specWrong | sourceCutIncomplete
    · subst failure
      exact ⟨.specProof, by simp [validEvidence],
        by simp [CoversMandatoryAt, demoSystem]⟩
    · subst failure
      exact ⟨.sourceCutSeal, by simp [validEvidence],
        by simp [CoversMandatoryAt, demoSystem]⟩

theorem valid_bundle_covers_every_mandatory_failure :
    ∀ failure, demoUniverse.mandatory failure →
      ∃ evidence, evidence ∈ validEvidence ∧
        CoversMandatoryAt demoSystem .current evidence failure :=
  every_mandatory_failure_has_covering_evidence
    demoSystem .current demoSeal validEvidence validCoverage

theorem valid_bundle_has_no_uncovered_mandatory_failure :
    ¬ ∃ failure,
      UncoveredMandatory demoSystem .current validEvidence failure :=
  failure_coverage_has_no_uncovered_mandatory
    demoSystem .current demoSeal validEvidence validCoverage

/-! CM-COVERAGE-01: empty evidence may not close by vacuous iteration. -/

theorem empty_evidence_is_rejected :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal) [] := by
  intro admitted
  exact coverage_bundle_nonempty demoSystem .current demoSeal [] admitted rfl

/-!
CM-COVERAGE-02: a self-labelled mandatory claim cannot cover anything unless
the exact context admits the evidence item.
-/

theorem unadmitted_mandatory_claim_is_rejected :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.forgedSpecClaim, .sourceCutSeal] := by
  intro admitted
  obtain ⟨evidence, member, covers⟩ :=
    admitted.everyMandatoryCovered .specWrong (Or.inl rfl)
  simp at member
  rcases member with rfl | rfl
  · exact covers.1
  · exact covers.2

/-! CM-COVERAGE-03: covering another failure does not cover the required one. -/

theorem wrong_failure_evidence_is_rejected :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.implementationParity, .sourceCutSeal] := by
  intro admitted
  obtain ⟨evidence, member, covers⟩ :=
    admitted.everyMandatoryCovered .specWrong (Or.inl rfl)
  simp at member
  rcases member with rfl | rfl <;> exact covers.2

/-! CM-COVERAGE-04: optional evidence cannot satisfy a mandatory requirement. -/

theorem optional_evidence_cannot_masquerade_as_mandatory :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.optionalSpecReview, .sourceCutSeal] := by
  intro admitted
  obtain ⟨evidence, member, covers⟩ :=
    admitted.everyMandatoryCovered .specWrong (Or.inl rfl)
  simp at member
  rcases member with rfl | rfl <;> exact covers.2

/-!
CM-COVERAGE-05: evidence admitted at the current context cannot be replayed at
another context without a new admission/transport relation.
-/

theorem cross_context_evidence_reuse_is_rejected :
    ¬ CoverageAdmissible demoSystem .stale (.sealed demoSeal)
      [.specProof, .sourceCutSeal] := by
  intro admitted
  obtain ⟨evidence, member, covers⟩ :=
    admitted.everyMandatoryCovered .specWrong (Or.inl rfl)
  simp at member
  rcases member with rfl | rfl <;> exact covers.1

/-! CM-COVERAGE-06: an empty enumeration cannot prove absence in an open world. -/

def incompletelyEnumeratedUniverse : FailureUniverse DemoFailure where
  inScope := fun failure => failure = .specWrong
  mandatory := fun failure => failure = .specWrong
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared := []

theorem empty_enumeration_cannot_seal_nonempty_scope :
    ¬ FailureUniverseSeal incompletelyEnumeratedUniverse := by
  intro coverageSeal
  have listed :=
    coverageSeal.declaredComplete .specWrong
      (by simp [incompletelyEnumeratedUniverse])
  simp [incompletelyEnumeratedUniverse] at listed

theorem unsealed_universe_is_rejected_even_with_valid_evidence :
    ¬ CoverageAdmissible demoSystem .current .unsealed validEvidence := by
  simp [CoverageAdmissible]

/-!
The only lawful negative conclusion is relative to a finite sealed universe.
This theorem must consume the seal's completeness proof.
-/
theorem not_declared_means_out_of_declared_scope
    (failure : DemoFailure)
    (notDeclared : failure ∉ demoUniverse.declared) :
    ¬ demoUniverse.inScope failure :=
  not_declared_not_in_scope demoUniverse demoSeal failure notDeclared

#print axioms every_mandatory_failure_has_covering_evidence
#print axioms covering_evidence_is_admitted
#print axioms coverage_bundle_nonempty
#print axioms failure_coverage_has_no_uncovered_mandatory
#print axioms not_declared_not_in_scope
#print axioms source_cut_seal_is_admitted_mandatory_coverage
#print axioms valid_bundle_covers_every_mandatory_failure
#print axioms valid_bundle_has_no_uncovered_mandatory_failure
#print axioms empty_evidence_is_rejected
#print axioms unadmitted_mandatory_claim_is_rejected
#print axioms wrong_failure_evidence_is_rejected
#print axioms optional_evidence_cannot_masquerade_as_mandatory
#print axioms cross_context_evidence_reuse_is_rejected
#print axioms empty_enumeration_cannot_seal_nonempty_scope
#print axioms unsealed_universe_is_rejected_even_with_valid_evidence

end Residua.RCC.FailureCoverage.Tests

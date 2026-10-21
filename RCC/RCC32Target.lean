import RCC.FailureCoverage
import RCCTests.FailureCoverage

/-!
# RCC-32 target package

This candidate packages failure-mode evidence coverage relative to one sealed
finite universe and one exact evidence context.  Every mandatory failure has
admitted mandatory-grade evidence; empty evidence, unadmitted or wrong-grade
claims, stale-context reuse, and unsealed/under-enumerated universes are
refused.  Completeness of the declared universe as a model of all real-world
threats remains an explicit instance obligation.

Fixture-level discharge: ConcreteWitness (demoUniverse) + MutantRefusal (7 refusals). No generic theorems (the prior generic_* were tautologies — exact coverage.everyMandatoryCovered, premise assumes conclusion; removed in an earlier revision).

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC32Target

open Residua.RCC.FailureCoverage
open Residua.RCC.FailureCoverage.Tests

universe u v w


structure ConcreteWitness : Prop where
  sealedUniverse : FailureUniverseSeal demoUniverse
  mandatoryCoverage :
    ∀ failure, demoUniverse.mandatory failure →
      ∃ evidence, evidence ∈ validEvidence ∧
        CoversMandatoryAt demoSystem .current evidence failure
  noUncoveredMandatory :
    ¬ ∃ failure,
      UncoveredMandatory demoSystem .current validEvidence failure
  evidenceNonempty : validEvidence ≠ []
  negativeClaimScoped :
    ∀ failure, failure ∉ demoUniverse.declared →
      ¬ demoUniverse.inScope failure

structure MutantRefusal : Prop where
  emptyEvidenceRefused :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal) []
  unadmittedEvidenceRefused :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.forgedSpecClaim, .sourceCutSeal]
  wrongFailureRefused :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.implementationParity, .sourceCutSeal]
  optionalGradeRefused :
    ¬ CoverageAdmissible demoSystem .current (.sealed demoSeal)
      [.optionalSpecReview, .sourceCutSeal]
  crossContextReuseRefused :
    ¬ CoverageAdmissible demoSystem .stale (.sealed demoSeal)
      [.specProof, .sourceCutSeal]
  emptyEnumerationRefused :
    ¬ FailureUniverseSeal incompletelyEnumeratedUniverse
  unsealedUniverseRefused :
    ¬ CoverageAdmissible demoSystem .current .unsealed validEvidence

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { sealedUniverse := demoSeal
      mandatoryCoverage := valid_bundle_covers_every_mandatory_failure
      noUncoveredMandatory := valid_bundle_has_no_uncovered_mandatory_failure
      evidenceNonempty :=
        coverage_bundle_nonempty
          demoSystem .current demoSeal validEvidence validCoverage
      negativeClaimScoped := not_declared_means_out_of_declared_scope }
  mutants :=
    { emptyEvidenceRefused := empty_evidence_is_rejected
      unadmittedEvidenceRefused := unadmitted_mandatory_claim_is_rejected
      wrongFailureRefused := wrong_failure_evidence_is_rejected
      optionalGradeRefused := optional_evidence_cannot_masquerade_as_mandatory
      crossContextReuseRefused := cross_context_evidence_reuse_is_rejected
      emptyEnumerationRefused := empty_enumeration_cannot_seal_nonempty_scope
      unsealedUniverseRefused :=
        unsealed_universe_is_rejected_even_with_valid_evidence }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC32Target

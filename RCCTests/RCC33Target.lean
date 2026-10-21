import RCC.RCC33Target

/-!
# RCC-33 target tests

These are proof-level positive and adversarial witnesses for the concrete
RCC-33 target.  They intentionally exercise the empty-bundle, optional-item,
threshold, and sealed-universe refusal paths rather than treating a generic
theorem as a discharge by itself.
-/

namespace Residua.RCC.RCC33Target.Tests

open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause
open Residua.RCC.RCC33Target

theorem positive_minimum_cut_certificate :
    IndependentAtLeast demoTopology .commonCause [.sourceEvidence] 1 :=
  certificate.positiveIndependent

theorem mandatory_failure_is_bound :
    (demoTopology.evidenceSystem.modelAt demoTopology.context).mandatory
      .commonCause :=
  certificate.mandatoryFailureBound

theorem empty_support_is_refused :
    ¬ AdmittedSupportBundle demoTopology .commonCause [] :=
  certificate.emptyBundleRefused

theorem optional_support_is_refused :
    ¬ AdmittedSupportBundle demoTopology .commonCause [.optionalEvidence] :=
  certificate.optionalEvidenceRefused

theorem threshold_above_minimum_is_refused :
    ¬ IndependentAtLeast demoTopology .commonCause [.sourceEvidence] 2 :=
  certificate.aboveMinimumRefused

theorem unsealed_universe_is_refused :
    ¬ CoverageAdmissible demoSystem .current .unsealed [.sourceEvidence] :=
  certificate.unsealedCoverageRefused

theorem full_domain_cut_is_explicit :
    ValidCut demoTopology demoTopology.faultDomainUniverse ∧
      BreaksBundle demoTopology .commonCause [.sourceEvidence]
        demoTopology.faultDomainUniverse :=
  full_domain_universe_breaks_support demoTopology .commonCause
    [.sourceEvidence] demoBundle

#print axioms positive_minimum_cut_certificate
#print axioms empty_support_is_refused
#print axioms optional_support_is_refused
#print axioms threshold_above_minimum_is_refused
#print axioms unsealed_universe_is_refused

end Residua.RCC.RCC33Target.Tests

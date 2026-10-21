import RCC.EvidenceProfile
import RCCTests.EvidenceProfile

/-!
# RCC-35 target package

This candidate packages evidence-profile dimensions as non-compensable
requirements.  Runtime binding, specification coverage, freshness, and
policy-bound cut evidence are typed dimensions; surplus in another dimension
cannot discharge a missing mandatory dimension.  The official registry is
intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC35Target

open Residua.RCC.EvidenceProfile
open Residua.RCC.EvidenceProfile.Tests

structure PositiveWitness : Prop where
  exactProfileMeetsItself : Meets exactRequired exactRequired
  fullCertificateMeetsPolicy :
    Meets (profileOf fullProfileCertificate)
      (requiredAt testPolicies .full .release)

structure MutantRefusal : Prop where
  proofCannotCompensateRuntime :
    ProfileCertificate
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False
  enginesCannotCompensateCoverage :
    ProfileCertificate
      (testTopology .enginesOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False
  staleCannotCompensateFreshness :
    ProfileCertificate
      (testTopology .staleOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False
  nakedNatCannotForgeRuntime :
    ¬ GradeDerived
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release proofOnlyCoverage
      .runtimeBindingGrade 100
  emptyPolicyRejected :
    ¬ ∃ policy : GoalEvidencePolicy TestFailure,
      policy.required = allZeroProfile
  relaxedPolicyDoesNotTransport :
    ¬ Meets (profileOf relaxedCertificate)
      (requiredAt testPolicies .full .release)
  aliasesCannotForgeImplementationCut :
    ProfileCertificate
      (testTopology .aliasOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False

structure Certificate : Prop where
  witness : PositiveWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { exactProfileMeetsItself := exact_profile_meets_itself
      fullCertificateMeetsPolicy := full_certificate_meets_pre_state_policy }
  mutants :=
    { proofCannotCompensateRuntime :=
        high_proof_without_runtime_has_no_profile_certificate
      enginesCannotCompensateCoverage :=
        many_engines_without_spec_coverage_has_no_profile_certificate
      staleCannotCompensateFreshness :=
        stale_receipts_have_no_profile_certificate
      nakedNatCannotForgeRuntime := naked_nat_cannot_forge_runtime_grade
      emptyPolicyRejected := all_zero_policy_is_rejected
      relaxedPolicyDoesNotTransport :=
        relaxed_certificate_cannot_transport_to_full_context
      aliasesCannotForgeImplementationCut :=
        aliases_cannot_forge_profile_certificate }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC35Target


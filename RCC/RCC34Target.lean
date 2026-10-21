import RCC.EffectiveAuthorityQuorum
import RCCTests.FormalCoreEffectiveAuthorityQuorum

/-!
# RCC-34 target package

This candidate packages effective-authority quorum as a pre-state-bound,
closed-world minimum-control-cut certificate.  It records both the positive
independent-control witness and countermodels showing why key/actor counts,
omitted dependencies, relaxed policy bindings, and incomplete topology
coverage cannot establish effective authority.  The official registry is
intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC34Target

open Residua.RCC.EffectiveAuthorityQuorum
open Residua.RCC.EffectiveAuthorityQuorum.Tests

universe u

theorem generic_lawful_act_has_effective_control_certificate
    {S : AuthoritySystem} {policy : AuthorityPolicy S}
    {topology : FiniteControlTopology S}
    (act : LawfulAuthorityAct S policy topology) :
    EffectiveControlCutExceedsBudget S policy topology :=
  lawful_act_effective_control_min_cut_exceeds S policy topology act

structure PositiveWitness : Prop where
  independentPairCut :
    IsMinimumListedControlCut pairSystem pairPolicy independentTopology
      [.leftDomain, .rightDomain]
  lawfulPairCertificate :
    EffectiveControlCutExceedsBudget pairSystem pairPolicy independentTopology

structure MutantRefusal : Prop where
  relaxedPolicyNotPreStateBound :
    ¬ PolicyBoundAt pairSystem independentTopology relaxedPairPolicy
  relaxedPolicyCannotFormCertificate :
    EffectiveAuthorityCertificate
        pairSystem relaxedPairPolicy independentTopology → False
  twoKeysOneCustodianNotEffective :
    ¬ EffectiveControlCutExceedsBudget
      pairSystem pairPolicy oneCustodianTopology
  threeKeysOneHostNotEffective :
    ¬ EffectiveControlCutExceedsBudget
      hostSystem hostPolicy sharedHostTopology
  threeHandlesOneSigningKeyNotQuorum :
    ¬ EligibleKeyQuorum handleSystem handlePolicy
      [.authorHandle, .reviewerHandle, .disposerHandle]
  omittedSharedHostDependencyRejected :
    ¬ ∀ signer domain,
      domain ∈ omittedSharedHostDependencies signer ↔
        hostSystem.controlDepends () signer domain
  incompleteTopologyRejected :
    ¬ ClosedWorldCoverage hiddenSystem incompleteTopology
  incompleteTopologyCannotProveEffectiveAuthority :
    ¬ EffectiveControlCutExceedsBudget
      hiddenSystem hiddenPolicy incompleteTopology

structure Certificate : Prop where
  witness : PositiveWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { independentPairCut := independent_pair_cut_is_minimum
      lawfulPairCertificate := lawful_pair_has_actual_min_cut_above_budget }
  mutants :=
    { relaxedPolicyNotPreStateBound := relaxed_policy_cannot_bind_pre_state
      relaxedPolicyCannotFormCertificate :=
        relaxed_policy_cannot_form_certificate
      twoKeysOneCustodianNotEffective :=
        two_public_keys_one_custodian_countermodel.2
      threeKeysOneHostNotEffective :=
        three_keys_one_host_countermodel.2.2
      threeHandlesOneSigningKeyNotQuorum :=
        three_handles_one_signing_key_countermodel.2.2.2
      omittedSharedHostDependencyRejected :=
        omitted_shared_host_dependency_cannot_be_exact
      incompleteTopologyRejected :=
        incomplete_topology_omits_an_eligible_signer
      incompleteTopologyCannotProveEffectiveAuthority := by
        exact closed_world_topology_coverage_is_load_bearing.2 }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC34Target


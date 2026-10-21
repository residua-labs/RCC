import RCC.RCC36Target

/-! Independent proof-level checks for the RCC-36 target certificate. -/

namespace Residua.RCC.RCC36Target.Tests

open Residua.RCC.NoDoubleCounting
open Residua.RCC.NoDoubleCounting.Tests
open Residua.RCC.RCC36Target

theorem aliases_collapse_without_erasing_raw_multiplicity :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases actorClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases actorAliasClaim) ∧
      [actorClaim, actorAliasClaim].length = 2 ∧
      countContributions topologyContributions = 1 :=
  ⟨Certificate.aliasKeyStable certificate,
    Certificate.rawMultiplicityRemainsVisible certificate,
    Certificate.canonicalAliasMultiplicityCollapses certificate⟩

theorem sealed_universe_rejects_ghosts_and_omissions :
    (∀ contribution, Covered topologyContributions contribution →
      ∃ claim, claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
        canonicalContributionAt demoIdentity .topologyAlias claim = contribution) ∧
    (∀ {claim}, claim ∈ (sealedClaimsAt .topologyAlias).declared →
      Covered topologyContributions
        (canonicalContributionAt demoIdentity .topologyAlias claim)) :=
  ⟨Certificate.ghostContributionRefused certificate,
    Certificate.omittedClaimRefused certificate⟩

theorem stale_context_and_conflicting_identity_refuse :
    canonicalContributionAt demoIdentity .topologyAlias actorClaim ≠
      canonicalContributionAt demoIdentity .alternateSnapshot actorClaim ∧
      ¬ Covered alternateContributions
        (canonicalContributionAt demoIdentity .topologyAlias actorClaim) :=
  ⟨Certificate.crossContextReuseRefused certificate,
    Certificate.crossContextCoverageRefused certificate⟩

theorem canonical_fold_is_order_and_alias_stable :
    foldClaims demoIdentity .topologyAlias
        [actorAliasClaim, actorClaim] =
      foldClaims demoIdentity .topologyAlias [actorClaim] ∧
      foldClaims demoIdentity .aliases [actorClaim, receiptClaim] =
      foldClaims demoIdentity .aliases [receiptClaim, actorClaim] ∧
      (∀ contribution,
        foldClaims demoIdentity .topologyAlias
            (sealedClaimsAt .topologyAlias).declared contribution = true ↔
          Covered topologyContributions contribution) :=
  ⟨Certificate.aliasFoldIdempotent certificate,
    Certificate.foldPermutationInvariant certificate,
    Certificate.foldMatchesSealedCarrier certificate⟩

#print axioms aliases_collapse_without_erasing_raw_multiplicity
#print axioms sealed_universe_rejects_ghosts_and_omissions
#print axioms stale_context_and_conflicting_identity_refuse
#print axioms canonical_fold_is_order_and_alias_stable

end Residua.RCC.RCC36Target.Tests

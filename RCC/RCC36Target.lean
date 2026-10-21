import RCCTests.NoDoubleCounting

/-!
# RCC-36 target package

This target packages the existing concrete canonical-contribution fixture as a
target-level certificate.  It proves that raw aliases do not create extra
canonical contributions, distinct lineages/failures remain distinct, sealed
universes reject ghosts and omissions, and context changes refuse stale reuse.

The target consumes the proof-carrying RCC-36 fixture and does not alter the
global RCC registry, source window, Nanoda root, or official closure count.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC36Target

open Residua.RCC.NoDoubleCounting
open Residua.RCC.NoDoubleCounting.Tests

structure Certificate : Prop where
  aliasKeyStable :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases actorClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases actorAliasClaim)
  rawMultiplicityRemainsVisible :
    [actorClaim, actorAliasClaim].length = 2
  canonicalAliasMultiplicityCollapses :
    countContributions topologyContributions = 1
  distinctLineagesRemainDistinct :
    countContributions twoRealContributions = 2
  distinctFailuresRemainDistinct :
    countContributions crossFailureContributions = 2
  ghostContributionRefused :
    ∀ contribution, Covered topologyContributions contribution →
      ∃ claim, claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
        canonicalContributionAt demoIdentity .topologyAlias claim = contribution
  omittedClaimRefused :
    ∀ {claim}, claim ∈ (sealedClaimsAt .topologyAlias).declared →
      Covered topologyContributions
        (canonicalContributionAt demoIdentity .topologyAlias claim)
  sameClaimCannotConflict :
    ∀ left right,
      canonicalContributionAt demoIdentity .topologyAlias actorClaim = left →
      canonicalContributionAt demoIdentity .topologyAlias actorClaim = right →
      left = right
  crossContextReuseRefused :
    canonicalContributionAt demoIdentity .topologyAlias actorClaim ≠
      canonicalContributionAt demoIdentity .alternateSnapshot actorClaim
  crossContextCoverageRefused :
    ¬ Covered alternateContributions
      (canonicalContributionAt demoIdentity .topologyAlias actorClaim)
  aliasFoldIdempotent :
    foldClaims demoIdentity .topologyAlias
        [actorAliasClaim, actorClaim] =
      foldClaims demoIdentity .topologyAlias [actorClaim]
  foldPermutationInvariant :
    foldClaims demoIdentity .aliases [actorClaim, receiptClaim] =
      foldClaims demoIdentity .aliases [receiptClaim, actorClaim]
  foldMatchesSealedCarrier :
    ∀ contribution,
      foldClaims demoIdentity .topologyAlias
          (sealedClaimsAt .topologyAlias).declared contribution = true ↔
        Covered topologyContributions contribution
  topologyOriginComplete :
    ∀ contribution, contribution ∈ canonicalTopology.evidenceUniverse →
      ∃ claim, claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
        canonicalContributionAt demoIdentity .topologyAlias claim = contribution
  declaredRelationExact :
    ∀ left right : DemoContribution,
      contributionKey left = contributionKey right ↔
        SameContribution left right

def certificate : Certificate where
  aliasKeyStable := actor_aliases_derive_same_key
  rawMultiplicityRemainsVisible := actor_raw_count_two
  canonicalAliasMultiplicityCollapses := actor_canonical_count_one
  distinctLineagesRemainDistinct := two_real_lineages_count_two
  distinctFailuresRemainDistinct := same_lineage_different_failure_counts_two
  ghostContributionRefused := ghost_universe_impossible
  omittedClaimRefused := omitted_universe_impossible
  sameClaimCannotConflict := same_raw_conflicting_contribution_impossible
  crossContextReuseRefused := cross_context_reuse_refused
  crossContextCoverageRefused := cross_context_coverage_reuse_refused
  aliasFoldIdempotent := alias_duplicate_fold_invariant
  foldPermutationInvariant := claim_permutation_invariant
  foldMatchesSealedCarrier := fold_matches_authoritative_carrier
  topologyOriginComplete := canonical_topology_item_has_raw_origin
  declaredRelationExact := contribution_key_uses_declared_relation

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC36Target

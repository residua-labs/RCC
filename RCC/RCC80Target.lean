import RCCTests.NoDoubleCounting

/-! RCC-80 candidate: canonical contribution identity and no-double-counting. -/

namespace Residua.RCC.RCC80Target

open Residua.RCC.NoDoubleCounting
open Residua.RCC.NoDoubleCounting.Tests

def actorAliasSameKey := actor_aliases_derive_same_key
def receiptAliasSameKey := receipt_aliases_derive_same_key
def encodingAliasSameKey := encoding_aliases_derive_same_key
def rawMultiplicityPreserved := actor_raw_count_two
def aliasCarrierDeduplicated := actor_canonical_count_one
def distinctLineagesRemainDistinct := two_real_lineages_count_two
def distinctFailuresRemainDistinct := same_lineage_different_failure_counts_two
def noGhostContribution := ghost_universe_impossible
def noOmittedClaim (claim : DemoClaim)
    (member : claim ∈ (sealedClaimsAt .topologyAlias).declared) :=
  omitted_universe_impossible member
def noConflictingContribution :
    ∀ contribution : DemoContribution,
      Covered topologyContributions contribution ↔
        ∃ claim,
          claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
            canonicalContributionAt demoIdentity .topologyAlias claim =
              contribution := by
  intro contribution
  exact covered_iff_raw_claim_origin topologyContributions contribution
def crossContextRefused := cross_context_reuse_refused
def crossContextCoverageRefused := cross_context_coverage_reuse_refused
def aliasFoldInvariant := alias_duplicate_fold_invariant
def permutationInvariant := claim_permutation_invariant
def foldMatchesCarrier := fold_matches_authoritative_carrier
def topologyOrigin := canonical_topology_item_has_raw_origin
def contributionKeyExact := contribution_key_uses_declared_relation

structure Certificate where
  actorAliasSameKey :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases actorClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases actorAliasClaim)
  receiptAliasSameKey :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases receiptClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases receiptAliasClaim)
  encodingAliasSameKey :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases encodingClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases encodingAliasClaim)
  rawMultiplicityPreserved : [actorClaim, actorAliasClaim].length = 2
  noConflictingContribution :
    ∀ contribution : DemoContribution,
      Covered topologyContributions contribution ↔
        ∃ claim,
          claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
            canonicalContributionAt demoIdentity .topologyAlias claim =
              contribution
  crossContextRefused :
    canonicalContributionAt demoIdentity .topologyAlias actorClaim ≠
      canonicalContributionAt demoIdentity .alternateSnapshot actorClaim
  contributionKeyExact :
    ∀ (left right : DemoContribution),
      contributionKey left = contributionKey right ↔
        SameContribution left right

def certificate : Certificate where
  actorAliasSameKey := actorAliasSameKey
  receiptAliasSameKey := receiptAliasSameKey
  encodingAliasSameKey := encodingAliasSameKey
  rawMultiplicityPreserved := rawMultiplicityPreserved
  noConflictingContribution := noConflictingContribution
  crossContextRefused := crossContextRefused
  contributionKeyExact := contribution_key_uses_declared_relation

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC80Target

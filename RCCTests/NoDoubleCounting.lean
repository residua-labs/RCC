import RCC.NoDoubleCounting

/-!
# RCC-36 Canonical Evidence Contribution Witnesses

These witnesses derive vote identity from a context-indexed lineage authority.
No fixture hand-fills a canonical contribution on a raw evidence row.

The suite includes the load-bearing countermodels:

* aliases count once although raw presentations are distinct;
* distinct lineages and distinct failures remain distinct votes;
* ghost and omitted canonical universes are impossible under the seal;
* one raw claim cannot acquire conflicting canonical identities;
* context changes invalidate reuse;
* fold order and alias duplication do not affect presence; and
* RCC-33/RCC-35 see only the canonical carrier.

AddressKernel/digest collision resistance is deliberately not claimed.
-/

namespace Residua.RCC.NoDoubleCounting.Tests

open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause
open Residua.RCC.EvidenceProfile
open Residua.RCC.NoDoubleCounting

inductive DemoContext
  | aliases
  | twoRealLineages
  | sameLineageDifferentFailure
  | topologyAlias
  | alternateSnapshot
  deriving DecidableEq, Repr

inductive DemoFailure
  | unauthorizedSigning
  | duplicateEffect
  | sourceOmission
  deriving DecidableEq, Repr

inductive DemoLineage
  | signerKey
  | workflowRun
  | evidenceLineage
  | independentOne
  | independentTwo
  | alternateSigner
  deriving DecidableEq, Repr

inductive DemoEvidence
  | actorHandleA
  | actorHandleAlias
  | receiptJson
  | receiptCbor
  | evidenceLegacy
  | evidenceCurrent
  | independentA
  | independentB
  | signerOtherFailure
  deriving DecidableEq, Repr

inductive DemoFaultDomain
  | custody
  deriving DecidableEq, Repr

abbrev DemoClaim := EvidenceClaim DemoEvidence DemoFailure
abbrev DemoContribution :=
  CanonicalContribution DemoFailure DemoLineage

def actorClaim : DemoClaim :=
  ⟨.actorHandleA, .unauthorizedSigning⟩

def actorAliasClaim : DemoClaim :=
  ⟨.actorHandleAlias, .unauthorizedSigning⟩

def receiptClaim : DemoClaim :=
  ⟨.receiptJson, .duplicateEffect⟩

def receiptAliasClaim : DemoClaim :=
  ⟨.receiptCbor, .duplicateEffect⟩

def encodingClaim : DemoClaim :=
  ⟨.evidenceLegacy, .sourceOmission⟩

def encodingAliasClaim : DemoClaim :=
  ⟨.evidenceCurrent, .sourceOmission⟩

def independentAClaim : DemoClaim :=
  ⟨.independentA, .unauthorizedSigning⟩

def independentBClaim : DemoClaim :=
  ⟨.independentB, .unauthorizedSigning⟩

def signerOtherFailureClaim : DemoClaim :=
  ⟨.signerOtherFailure, .duplicateEffect⟩

def rawClaimsAt : DemoContext → List DemoClaim
  | .aliases =>
      [actorClaim, actorAliasClaim,
        receiptClaim, receiptAliasClaim,
        encodingClaim, encodingAliasClaim]
  | .twoRealLineages =>
      [independentAClaim, independentBClaim]
  | .sameLineageDifferentFailure =>
      [actorClaim, signerOtherFailureClaim]
  | .topologyAlias =>
      [actorClaim, actorAliasClaim]
  | .alternateSnapshot =>
      [actorClaim]

def failureListAt : DemoContext → List DemoFailure
  | .aliases =>
      [.unauthorizedSigning, .duplicateEffect, .sourceOmission]
  | .twoRealLineages =>
      [.unauthorizedSigning]
  | .sameLineageDifferentFailure =>
      [.unauthorizedSigning, .duplicateEffect]
  | .topologyAlias =>
      [.unauthorizedSigning]
  | .alternateSnapshot =>
      [.unauthorizedSigning]

def demoFailureUniverse (context : DemoContext) :
    FailureUniverse DemoFailure where
  inScope := fun failure => failure ∈ failureListAt context
  mandatory := fun failure => failure ∈ failureListAt context
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared := failureListAt context

def demoEvidenceSystem :
    FailureEvidenceSystem DemoContext DemoFailure DemoEvidence where
  modelAt := demoFailureUniverse
  AdmittedAt := fun context evidence =>
    ∃ failure, EvidenceClaim.mk evidence failure ∈ rawClaimsAt context
  CoversAt := fun context evidence failure grade =>
    grade = .mandatory ∧
      EvidenceClaim.mk evidence failure ∈ rawClaimsAt context

def demoLineageAt : DemoContext → DemoEvidence → DemoLineage
  | .alternateSnapshot, .actorHandleA => .alternateSigner
  | _, .actorHandleA => .signerKey
  | _, .actorHandleAlias => .signerKey
  | _, .receiptJson => .workflowRun
  | _, .receiptCbor => .workflowRun
  | _, .evidenceLegacy => .evidenceLineage
  | _, .evidenceCurrent => .evidenceLineage
  | _, .independentA => .independentOne
  | _, .independentB => .independentTwo
  | _, .signerOtherFailure => .signerKey

def demoIdentity :
    ContributionIdentitySystem
      DemoContext DemoEvidence DemoFailure DemoLineage where
  evidenceSystem := demoEvidenceSystem
  lineageAt := demoLineageAt
  AliasesAt := fun context _ left right =>
    demoLineageAt context left = demoLineageAt context right
  aliasesExact := by
    intro context failure left right
    rfl

def sealedClaimsAt (context : DemoContext) :
    SealedClaimUniverse demoIdentity context where
  declared := rawClaimsAt context
  nodup := by
    cases context <;> decide
  sound := by
    intro claim member
    cases claim with
    | mk evidence failure =>
        exact
          ⟨⟨failure, member⟩,
            ⟨rfl, member⟩⟩
  complete := by
    intro evidence failure covered
    exact covered.2.2

def keyContribution : DemoContribution :=
  ⟨.unauthorizedSigning, .signerKey⟩

def runContribution : DemoContribution :=
  ⟨.duplicateEffect, .workflowRun⟩

def encodingContribution : DemoContribution :=
  ⟨.sourceOmission, .evidenceLineage⟩

def independentOneContribution : DemoContribution :=
  ⟨.unauthorizedSigning, .independentOne⟩

def independentTwoContribution : DemoContribution :=
  ⟨.unauthorizedSigning, .independentTwo⟩

def signerOtherFailureContribution : DemoContribution :=
  ⟨.duplicateEffect, .signerKey⟩

def alternateContribution : DemoContribution :=
  ⟨.unauthorizedSigning, .alternateSigner⟩

def aliasContributions :
    ContributionUniverse demoIdentity .aliases (sealedClaimsAt .aliases) where
  declared := [keyContribution, runContribution, encodingContribution]
  nodup := by decide
  soundOrigin := by
    intro contribution member
    rcases contribution with ⟨failure, lineage⟩
    cases failure <;> cases lineage <;>
      simp_all
        [keyContribution, runContribution, encodingContribution,
          sealedClaimsAt, rawClaimsAt, actorClaim, actorAliasClaim,
          receiptClaim, receiptAliasClaim, encodingClaim,
          encodingAliasClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]
  completeInclusion := by
    intro claim member
    rcases claim with ⟨evidence, failure⟩
    cases evidence <;> cases failure <;>
      simp_all
        [sealedClaimsAt, rawClaimsAt, actorClaim, actorAliasClaim,
          receiptClaim, receiptAliasClaim, encodingClaim,
          encodingAliasClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt, keyContribution,
          runContribution, encodingContribution]

def twoRealContributions :
    ContributionUniverse demoIdentity .twoRealLineages
      (sealedClaimsAt .twoRealLineages) where
  declared := [independentOneContribution, independentTwoContribution]
  nodup := by decide
  soundOrigin := by
    intro contribution member
    rcases contribution with ⟨failure, lineage⟩
    cases failure <;> cases lineage <;>
      simp_all
        [independentOneContribution, independentTwoContribution,
          sealedClaimsAt, rawClaimsAt, independentAClaim,
          independentBClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]
  completeInclusion := by
    intro claim member
    rcases claim with ⟨evidence, failure⟩
    cases evidence <;> cases failure <;>
      simp_all
        [independentOneContribution, independentTwoContribution,
          sealedClaimsAt, rawClaimsAt, independentAClaim,
          independentBClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]

def crossFailureContributions :
    ContributionUniverse demoIdentity .sameLineageDifferentFailure
      (sealedClaimsAt .sameLineageDifferentFailure) where
  declared := [keyContribution, signerOtherFailureContribution]
  nodup := by decide
  soundOrigin := by
    intro contribution member
    rcases contribution with ⟨failure, lineage⟩
    cases failure <;> cases lineage <;>
      simp_all
        [keyContribution, signerOtherFailureContribution,
          sealedClaimsAt, rawClaimsAt, actorClaim,
          signerOtherFailureClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]
  completeInclusion := by
    intro claim member
    rcases claim with ⟨evidence, failure⟩
    cases evidence <;> cases failure <;>
      simp_all
        [keyContribution, signerOtherFailureContribution,
          sealedClaimsAt, rawClaimsAt, actorClaim,
          signerOtherFailureClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]

def topologyContributions :
    ContributionUniverse demoIdentity .topologyAlias
      (sealedClaimsAt .topologyAlias) where
  declared := [keyContribution]
  nodup := by decide
  soundOrigin := by
    intro contribution member
    rcases contribution with ⟨failure, lineage⟩
    cases failure <;> cases lineage <;>
      simp_all
        [keyContribution, sealedClaimsAt, rawClaimsAt,
          actorClaim, actorAliasClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]
  completeInclusion := by
    intro claim member
    rcases claim with ⟨evidence, failure⟩
    cases evidence <;> cases failure <;>
      simp_all
        [keyContribution, sealedClaimsAt, rawClaimsAt,
          actorClaim, actorAliasClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]

def alternateContributions :
    ContributionUniverse demoIdentity .alternateSnapshot
      (sealedClaimsAt .alternateSnapshot) where
  declared := [alternateContribution]
  nodup := by decide
  soundOrigin := by
    intro contribution member
    rcases contribution with ⟨failure, lineage⟩
    cases failure <;> cases lineage <;>
      simp_all
        [alternateContribution, sealedClaimsAt, rawClaimsAt,
          actorClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]
  completeInclusion := by
    intro claim member
    rcases claim with ⟨evidence, failure⟩
    cases evidence <;> cases failure <;>
      simp_all
        [alternateContribution, sealedClaimsAt, rawClaimsAt,
          actorClaim, canonicalContributionAt,
          demoIdentity, demoLineageAt]

/-! Presentation aliases derive their equality from the lineage authority. -/

theorem actor_aliases_derive_same_key :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases actorClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases actorAliasClaim) := by
  rfl

theorem receipt_aliases_derive_same_key :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases receiptClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases receiptAliasClaim) := by
  rfl

theorem encoding_aliases_derive_same_key :
    contributionKey
        (canonicalContributionAt demoIdentity .aliases encodingClaim) =
      contributionKey
        (canonicalContributionAt demoIdentity .aliases
          encodingAliasClaim) := by
  rfl

/-! Raw multiplicity does not inflate the canonical carrier. -/

theorem actor_raw_count_two :
    [actorClaim, actorAliasClaim].length = 2 := by
  rfl

theorem actor_canonical_count_one :
    countContributions topologyContributions = 1 := by
  rfl

theorem two_real_lineages_count_two :
    countContributions twoRealContributions = 2 := by
  rfl

theorem same_lineage_different_failure_counts_two :
    countContributions crossFailureContributions = 2 := by
  rfl

/-! Exact-image seals rule out ghost and omitted votes. -/

theorem ghost_universe_impossible
    (contribution : DemoContribution)
    (covered : Covered topologyContributions contribution) :
    ∃ claim, claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
      canonicalContributionAt demoIdentity .topologyAlias claim =
        contribution :=
  no_ghost_contribution topologyContributions covered

theorem omitted_universe_impossible
    {claim : DemoClaim}
    (member : claim ∈ (sealedClaimsAt .topologyAlias).declared) :
    Covered topologyContributions
      (canonicalContributionAt demoIdentity .topologyAlias claim) :=
  no_omitted_claim topologyContributions member

theorem same_raw_conflicting_contribution_impossible
    (left right : DemoContribution)
    (leftExact :
      canonicalContributionAt demoIdentity .topologyAlias actorClaim = left)
    (rightExact :
      canonicalContributionAt demoIdentity .topologyAlias actorClaim = right) :
    left = right :=
  same_claim_cannot_have_conflicting_contributions
    demoIdentity .topologyAlias actorClaim left right leftExact rightExact

/-! A contribution derived at one snapshot is not reusable at another. -/

theorem cross_context_reuse_refused :
    canonicalContributionAt demoIdentity .topologyAlias actorClaim ≠
      canonicalContributionAt demoIdentity .alternateSnapshot actorClaim := by
  decide

theorem cross_context_coverage_reuse_refused :
    ¬ Covered alternateContributions
      (canonicalContributionAt demoIdentity .topologyAlias actorClaim) := by
  intro covered
  simp
    [Covered, alternateContributions, alternateContribution,
      canonicalContributionAt, demoIdentity, demoLineageAt, actorClaim]
    at covered

/-! The low-level fold is order- and alias-duplicate invariant. -/

theorem alias_duplicate_fold_invariant :
    foldClaims demoIdentity .topologyAlias
        [actorAliasClaim, actorClaim] =
      foldClaims demoIdentity .topologyAlias [actorClaim] := by
  exact
    insert_alias_claim_idempotent
      demoIdentity .topologyAlias actorClaim actorAliasClaim
      rfl rfl emptyPresence

theorem claim_permutation_invariant :
    foldClaims demoIdentity .aliases [actorClaim, receiptClaim] =
      foldClaims demoIdentity .aliases [receiptClaim, actorClaim] := by
  exact
    fold_claims_permutation_invariant demoIdentity .aliases
      (List.Perm.swap actorClaim receiptClaim []).symm

theorem fold_matches_authoritative_carrier
    (contribution : DemoContribution) :
    foldClaims demoIdentity .topologyAlias
        (sealedClaimsAt .topologyAlias).declared contribution = true ↔
      Covered topologyContributions contribution :=
  fold_claims_agrees_with_universe topologyContributions contribution

/-! RCC-33/RCC-35 adapter: raw aliases cannot inflate their carrier. -/

def topologyEvidenceSystem :
    FailureEvidenceSystem DemoContext DemoFailure DemoContribution where
  modelAt := demoFailureUniverse
  AdmittedAt := fun context contribution =>
    match context with
    | .topologyAlias => contribution = keyContribution
    | _ => False
  CoversAt := fun context contribution failure grade =>
    context = .topologyAlias ∧
      contribution = keyContribution ∧
      failure = .unauthorizedSigning ∧
      grade = .mandatory

def topologyFailureSeal :
    FailureUniverseSeal
      (topologyEvidenceSystem.modelAt .topologyAlias) where
  declaredSound := by
    intro failure member
    simpa
      [topologyEvidenceSystem, demoFailureUniverse, failureListAt]
      using member
  declaredComplete := by
    intro failure inScope
    simpa
      [topologyEvidenceSystem, demoFailureUniverse, failureListAt]
      using inScope

def canonicalTopology :
    SealedFiniteTopology
      DemoContext DemoContribution DemoFailure DemoFaultDomain where
  evidenceSystem := topologyEvidenceSystem
  context := .topologyAlias
  failureUniverseSeal := topologyFailureSeal
  evidenceUniverse := [keyContribution]
  faultDomainUniverse := [.custody]
  evidenceNoDup := by decide
  faultDomainNoDup := by decide
  evidenceSound := by
    intro contribution member
    simp_all [topologyEvidenceSystem]
  evidenceComplete := by
    intro contribution admitted
    simp_all [topologyEvidenceSystem]
  faultDomainComplete := by
    intro domain
    cases domain
    simp
  dependsFor := fun _ _ domain => domain = .custody
  dependencyRooted := by
    intro contribution failure member covers
    exact ⟨.custody, by simp, rfl⟩
  domainCost := fun _ => 1
  domainCostPositive := by
    intro domain
    cases domain
    decide

def canonicalTopologyAdapter :
    CanonicalizedTopology
      demoIdentity .topologyAlias (sealedClaimsAt .topologyAlias)
        topologyContributions DemoFaultDomain where
  topology := canonicalTopology
  contextExact := rfl
  failureUniverseExact := rfl
  evidenceUniverseExact := rfl
  mandatoryCoverageExact := by
    intro contribution failure
    rcases contribution with ⟨contributionFailure, lineage⟩
    cases contributionFailure <;> cases lineage <;> cases failure <;>
      simp
        [CoversMandatoryAt, topologyEvidenceSystem, canonicalTopology,
          Covered, topologyContributions, keyContribution]

theorem raw_nodup_aliases_canonicalize_to_one :
    (sealedClaimsAt .topologyAlias).declared.Nodup ∧
      (sealedClaimsAt .topologyAlias).declared.length = 2 ∧
      canonicalTopology.evidenceUniverse.length = 1 := by
  decide

theorem canonical_topology_item_has_raw_origin
    (contribution : DemoContribution)
    (member : contribution ∈ canonicalTopology.evidenceUniverse) :
    ∃ claim, claim ∈ (sealedClaimsAt .topologyAlias).declared ∧
      canonicalContributionAt demoIdentity .topologyAlias claim =
        contribution :=
  topology_item_has_raw_claim_origin
    canonicalTopologyAdapter contribution member

/-!
The generic RCC-35 bridge is checked at its fully elaborated type.  Any
`ProfileCertificate` over `canonicalTopologyAdapter.topology` can consume only
canonical contributions with sealed raw mandatory-coverage origins.
-/
#check profile_certificate_mandatory_failure_has_raw_claim_origin

/-! The pre-hash key theorem makes no digest collision claim. -/

theorem contribution_key_uses_declared_relation
    (left right : DemoContribution) :
    contributionKey left = contributionKey right ↔
      SameContribution left right :=
  contribution_key_exact left right

#print axioms contribution_key_exact
#print axioms canonical_contribution_eq_iff
#print axioms covered_iff_raw_claim_origin
#print axioms no_ghost_contribution
#print axioms no_omitted_claim
#print axioms same_claim_cannot_have_conflicting_contributions
#print axioms insert_contribution_idempotent
#print axioms insert_contribution_commutative
#print axioms insert_alias_claim_idempotent
#print axioms fold_claims_permutation_invariant
#print axioms fold_claims_agrees_with_universe
#print axioms topology_item_has_raw_claim_origin
#print axioms profile_certificate_mandatory_failure_has_raw_claim_origin
#print axioms actor_aliases_derive_same_key
#print axioms receipt_aliases_derive_same_key
#print axioms encoding_aliases_derive_same_key
#print axioms actor_canonical_count_one
#print axioms two_real_lineages_count_two
#print axioms same_lineage_different_failure_counts_two
#print axioms ghost_universe_impossible
#print axioms omitted_universe_impossible
#print axioms same_raw_conflicting_contribution_impossible
#print axioms cross_context_reuse_refused
#print axioms cross_context_coverage_reuse_refused
#print axioms alias_duplicate_fold_invariant
#print axioms claim_permutation_invariant
#print axioms fold_matches_authoritative_carrier
#print axioms raw_nodup_aliases_canonicalize_to_one
#print axioms canonical_topology_item_has_raw_origin

end Residua.RCC.NoDoubleCounting.Tests

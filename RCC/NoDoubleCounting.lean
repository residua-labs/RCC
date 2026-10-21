import RCC.EvidenceProfile

/-!
# RCC-36 Canonical Evidence Contributions

RCC-36 counts evidence by `(failure, canonical lineage)`.  Presentation
handles, receipt encodings, and actor aliases are raw evidence, not votes.
An instance supplies evidence authority and a lineage projection; it cannot
freely fill a purported canonical contribution.

The authoritative carrier is the exact canonical image of a sealed universe
of admitted mandatory-coverage claims.  A low-level boolean fold is retained
only as an implementation kernel and is proved equivalent to that carrier.

The typed `ContributionKey` is pre-hash.  Digest collision resistance,
AddressKernel realization, and physical authenticity of the lineage
projection remain explicit nonclaims.

Prelude-only Lean 4.14; no Mathlib, no proof holes, and no custom axioms.
-/

namespace Residua.RCC.NoDoubleCounting

open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause
open Residua.RCC.EvidenceProfile

universe u v w x y z

/--
One evidence vote.  Fault-domain topology is deliberately absent: RCC-33 may
use fault domains to grade independence, but it cannot mint a second vote for
the same failure and canonical lineage.
-/
structure CanonicalContribution
    (FailureMode : Type u) (Lineage : Type v) where
  failure : FailureMode
  lineage : Lineage
  deriving DecidableEq, Repr

/-- Exact equality relation declared for canonical contributions. -/
def SameContribution
    {FailureMode : Type u} {Lineage : Type v}
    (left right : CanonicalContribution FailureMode Lineage) : Prop :=
  left.failure = right.failure ∧ left.lineage = right.lineage

/--
Typed structured key before domain-separated encoding and digesting.
RCC-36 never treats a naked digest as injective identity.
-/
structure ContributionKey
    (FailureMode : Type u) (Lineage : Type v) where
  failure : FailureMode
  lineage : Lineage
  deriving DecidableEq, Repr

def contributionKey
    {FailureMode : Type u} {Lineage : Type v}
    (contribution : CanonicalContribution FailureMode Lineage) :
    ContributionKey FailureMode Lineage where
  failure := contribution.failure
  lineage := contribution.lineage

/-- The typed pre-hash key exactly realizes contribution equality. -/
theorem contribution_key_exact
    {FailureMode : Type u} {Lineage : Type v}
    (left right : CanonicalContribution FailureMode Lineage) :
    contributionKey left = contributionKey right ↔
      SameContribution left right := by
  cases left with
  | mk leftFailure leftLineage =>
      cases right with
      | mk rightFailure rightLineage =>
          constructor
          · intro equal
            exact
              ⟨congrArg
                  (fun key : ContributionKey FailureMode Lineage =>
                    key.failure)
                  equal,
                congrArg
                  (fun key : ContributionKey FailureMode Lineage =>
                    key.lineage)
                  equal⟩
          · rintro ⟨failureEqual, lineageEqual⟩
            cases failureEqual
            cases lineageEqual
            rfl

theorem same_contribution_eq
    {FailureMode : Type u} {Lineage : Type v}
    {left right : CanonicalContribution FailureMode Lineage}
    (same : SameContribution left right) :
    left = right := by
  cases left
  cases right
  rcases same with ⟨failureEqual, lineageEqual⟩
  cases failureEqual
  cases lineageEqual
  rfl

/--
The only instance-provided identity coordinates:

* the already admitted RCC-32 evidence authority;
* a context-indexed canonical lineage projection; and
* an alias relation proved exact for that projection at the exact
  context/failure.

There is no caller-owned `contribution` field.
-/
structure ContributionIdentitySystem
    (Context : Type u) (Evidence : Type v)
    (FailureMode : Type w) (Lineage : Type x) where
  evidenceSystem : FailureEvidenceSystem Context FailureMode Evidence
  lineageAt : Context → Evidence → Lineage
  AliasesAt : Context → FailureMode → Evidence → Evidence → Prop
  aliasesExact :
    ∀ context failure left right,
      AliasesAt context failure left right ↔
        lineageAt context left = lineageAt context right

/-- One raw evidence item asserting mandatory coverage for one failure. -/
structure EvidenceClaim (Evidence : Type u) (FailureMode : Type v) where
  evidence : Evidence
  failure : FailureMode
  deriving DecidableEq, Repr

/-- Canonicalize one raw claim at the exact evidence context. -/
def canonicalContributionAt
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (claim : EvidenceClaim Evidence FailureMode) :
    CanonicalContribution FailureMode Lineage where
  failure := claim.failure
  lineage := identity.lineageAt context claim.evidence

/--
Canonical contribution equality is exactly failure equality plus the
instance's lawful same-context, same-failure alias relation.
-/
theorem canonical_contribution_eq_iff
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (left right : EvidenceClaim Evidence FailureMode) :
    canonicalContributionAt identity context left =
        canonicalContributionAt identity context right ↔
      left.failure = right.failure ∧
        identity.AliasesAt
          context left.failure left.evidence right.evidence := by
  constructor
  · intro equal
    have failureEqual :
        left.failure = right.failure :=
      congrArg
        (fun contribution : CanonicalContribution FailureMode Lineage =>
          contribution.failure)
        equal
    have lineageEqual :
        identity.lineageAt context left.evidence =
          identity.lineageAt context right.evidence :=
      congrArg
        (fun contribution : CanonicalContribution FailureMode Lineage =>
          contribution.lineage)
        equal
    exact
      ⟨failureEqual,
        (identity.aliasesExact
          context left.failure left.evidence right.evidence).2
          lineageEqual⟩
  · rintro ⟨failureEqual, aliases⟩
    have lineageEqual :
        identity.lineageAt context left.evidence =
          identity.lineageAt context right.evidence :=
      (identity.aliasesExact
        context left.failure left.evidence right.evidence).1 aliases
    exact
      calc
        CanonicalContribution.mk
              left.failure (identity.lineageAt context left.evidence) =
            CanonicalContribution.mk
              right.failure (identity.lineageAt context left.evidence) :=
          congrArg
            (fun failure =>
              CanonicalContribution.mk
                failure (identity.lineageAt context left.evidence))
            failureEqual
        _ =
            CanonicalContribution.mk
              right.failure (identity.lineageAt context right.evidence) :=
          congrArg
            (fun lineage =>
              CanonicalContribution.mk right.failure lineage)
            lineageEqual

/--
Exact finite enumeration of every admitted mandatory-coverage claim at one
context.  An empty or incomplete scanner cannot certify this structure.
-/
structure SealedClaimUniverse
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context) where
  declared : List (EvidenceClaim Evidence FailureMode)
  nodup : declared.Nodup
  sound :
    ∀ claim, claim ∈ declared →
      CoversMandatoryAt
        identity.evidenceSystem context claim.evidence claim.failure
  complete :
    ∀ evidence failure,
      CoversMandatoryAt identity.evidenceSystem context evidence failure →
        EvidenceClaim.mk evidence failure ∈ declared

/--
Exact duplicate-free canonical image of one sealed raw claim universe.

`soundOrigin` blocks ghost votes.  `completeInclusion` blocks omitted votes.
-/
structure ContributionUniverse
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (claims : SealedClaimUniverse identity context) where
  declared : List (CanonicalContribution FailureMode Lineage)
  nodup : declared.Nodup
  soundOrigin :
    ∀ contribution, contribution ∈ declared →
      ∃ claim, claim ∈ claims.declared ∧
        canonicalContributionAt identity context claim = contribution
  completeInclusion :
    ∀ claim, claim ∈ claims.declared →
      canonicalContributionAt identity context claim ∈ declared

/-- Authoritative coverage is membership in the sealed canonical image. -/
def Covered
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims)
    (contribution : CanonicalContribution FailureMode Lineage) : Prop :=
  contribution ∈ contributionUniverse.declared

/-- Authoritative count: only the sealed canonical image can be counted. -/
def countContributions
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims) : Nat :=
  contributionUniverse.declared.length

/-- Exact origin theorem for every authoritative contribution. -/
theorem covered_iff_raw_claim_origin
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims)
    (contribution : CanonicalContribution FailureMode Lineage) :
    Covered contributionUniverse contribution ↔
      ∃ claim, claim ∈ claims.declared ∧
        canonicalContributionAt identity context claim = contribution := by
  constructor
  · exact contributionUniverse.soundOrigin contribution
  · rintro ⟨claim, member, equal⟩
    rw [← equal]
    exact contributionUniverse.completeInclusion claim member

/-- No authoritative contribution is a ghost without a sealed raw origin. -/
theorem no_ghost_contribution
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims)
    {contribution : CanonicalContribution FailureMode Lineage}
    (covered : Covered contributionUniverse contribution) :
    ∃ claim, claim ∈ claims.declared ∧
      canonicalContributionAt identity context claim = contribution :=
  (covered_iff_raw_claim_origin contributionUniverse contribution).1 covered

/-- No sealed raw claim is omitted from the authoritative canonical image. -/
theorem no_omitted_claim
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims)
    {claim : EvidenceClaim Evidence FailureMode}
    (member : claim ∈ claims.declared) :
    Covered contributionUniverse
      (canonicalContributionAt identity context claim) :=
  contributionUniverse.completeInclusion claim member

/--
One raw claim has one canonical contribution.  A caller cannot assign the same
claim two conflicting vote identities.
-/
theorem same_claim_cannot_have_conflicting_contributions
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (claim : EvidenceClaim Evidence FailureMode)
    (left right : CanonicalContribution FailureMode Lineage)
    (leftExact :
      canonicalContributionAt identity context claim = left)
    (rightExact :
      canonicalContributionAt identity context claim = right) :
    left = right := by
  rw [← leftExact, ← rightExact]

/-! ## Low-level, non-authoritative fold -/

/--
Boolean implementation kernel.  It carries no universe authority by itself;
the theorem `fold_claims_agrees_with_universe` reconnects it to a sealed
`ContributionUniverse`.
-/
abbrev ContributionPresence
    (FailureMode : Type u) (Lineage : Type v) :=
  CanonicalContribution FailureMode Lineage → Bool

def emptyPresence
    {FailureMode : Type u} {Lineage : Type v} :
    ContributionPresence FailureMode Lineage :=
  fun _ => false

def insertContribution
    {FailureMode : Type u} {Lineage : Type v}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (contribution : CanonicalContribution FailureMode Lineage)
    (presence : ContributionPresence FailureMode Lineage) :
    ContributionPresence FailureMode Lineage :=
  fun candidate =>
    if contribution = candidate then true else presence candidate

theorem insert_contribution_idempotent
    {FailureMode : Type u} {Lineage : Type v}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (contribution : CanonicalContribution FailureMode Lineage)
    (presence : ContributionPresence FailureMode Lineage) :
    insertContribution contribution
        (insertContribution contribution presence) =
      insertContribution contribution presence := by
  funext candidate
  by_cases equal : contribution = candidate <;>
    simp [insertContribution, equal]

theorem insert_contribution_commutative
    {FailureMode : Type u} {Lineage : Type v}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (left right : CanonicalContribution FailureMode Lineage)
    (presence : ContributionPresence FailureMode Lineage) :
    insertContribution left (insertContribution right presence) =
      insertContribution right (insertContribution left presence) := by
  funext candidate
  by_cases leftEqual : left = candidate <;>
    by_cases rightEqual : right = candidate <;>
      simp [insertContribution, leftEqual, rightEqual]

/-- Mechanical canonical fold of raw claims; instances do not supply it. -/
def foldClaims
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context) :
    List (EvidenceClaim Evidence FailureMode) →
      ContributionPresence FailureMode Lineage
  | [] => emptyPresence
  | claim :: rest =>
      insertContribution
        (canonicalContributionAt identity context claim)
        (foldClaims identity context rest)

theorem fold_claims_eq_true_iff_origin
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (claims : List (EvidenceClaim Evidence FailureMode))
    (contribution : CanonicalContribution FailureMode Lineage) :
    foldClaims identity context claims contribution = true ↔
      ∃ claim, claim ∈ claims ∧
        canonicalContributionAt identity context claim = contribution := by
  induction claims with
  | nil =>
      simp [foldClaims, emptyPresence]
  | cons claim rest inductionHypothesis =>
      by_cases equal :
          canonicalContributionAt identity context claim = contribution
      · simp [foldClaims, insertContribution, equal]
      · simp [foldClaims, insertContribution, equal, inductionHypothesis]

theorem fold_claims_permutation_invariant
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    {left right : List (EvidenceClaim Evidence FailureMode)}
    (permutation : left.Perm right) :
    foldClaims identity context left =
      foldClaims identity context right := by
  induction permutation with
  | nil =>
      rfl
  | cons claim permutation inductionHypothesis =>
      simp only [foldClaims]
      rw [inductionHypothesis]
  | swap leftClaim rightClaim rest =>
      simp only [foldClaims]
      exact
        (insert_contribution_commutative
          (canonicalContributionAt identity context leftClaim)
          (canonicalContributionAt identity context rightClaim)
          (foldClaims identity context rest)).symm
  | trans leftMiddle middleRight leftRight middleRightResult =>
      exact Eq.trans leftRight middleRightResult

/-- A lawful alias duplicate is idempotent in the low-level fold. -/
theorem insert_alias_claim_idempotent
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (original alias : EvidenceClaim Evidence FailureMode)
    (sameFailure : original.failure = alias.failure)
    (aliases :
      identity.AliasesAt
        context original.failure original.evidence alias.evidence)
    (presence : ContributionPresence FailureMode Lineage) :
    insertContribution
        (canonicalContributionAt identity context alias)
        (insertContribution
          (canonicalContributionAt identity context original)
          presence) =
      insertContribution
        (canonicalContributionAt identity context original)
        presence := by
  have canonicalEqual :
      canonicalContributionAt identity context original =
        canonicalContributionAt identity context alias :=
    (canonical_contribution_eq_iff
      identity context original alias).2 ⟨sameFailure, aliases⟩
  rw [← canonicalEqual]
  exact
    insert_contribution_idempotent
      (canonicalContributionAt identity context original) presence

/-- The mechanical fold is extensionally equal to the sealed carrier. -/
theorem fold_claims_agrees_with_universe
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    [DecidableEq FailureMode] [DecidableEq Lineage]
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    (contributionUniverse : ContributionUniverse identity context claims)
    (contribution : CanonicalContribution FailureMode Lineage) :
    foldClaims identity context claims.declared contribution = true ↔
      Covered contributionUniverse contribution := by
  exact
    (fold_claims_eq_true_iff_origin
      identity context claims.declared contribution).trans
      (covered_iff_raw_claim_origin contributionUniverse contribution).symm

/-! ## RCC-33 / RCC-35 canonical carrier adapter -/

/--
Adapter binding RCC-33's exact-context evidence carrier to the sealed RCC-36
canonical image.  Mandatory coverage is not caller-defined a second time:
it is exactly carrier membership at the contribution's failure coordinate.
-/
structure CanonicalizedTopology
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x}
    (identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage)
    (context : Context)
    (claims : SealedClaimUniverse identity context)
    (contributions : ContributionUniverse identity context claims)
    (FaultDomain : Type y) where
  topology :
    SealedFiniteTopology
      Context (CanonicalContribution FailureMode Lineage)
        FailureMode FaultDomain
  contextExact : topology.context = context
  failureUniverseExact :
    topology.evidenceSystem.modelAt topology.context =
      identity.evidenceSystem.modelAt context
  evidenceUniverseExact :
    topology.evidenceUniverse = contributions.declared
  mandatoryCoverageExact :
    ∀ contribution failure,
      CoversMandatoryAt
          topology.evidenceSystem topology.context contribution failure ↔
        Covered contributions contribution ∧ contribution.failure = failure

/-- Every RCC-33 topology item has a sealed raw claim origin. -/
theorem topology_item_has_raw_claim_origin
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x} {FaultDomain : Type y}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    {contributions : ContributionUniverse identity context claims}
    (adapter :
      CanonicalizedTopology
        identity context claims contributions FaultDomain)
    (contribution : CanonicalContribution FailureMode Lineage)
    (member : contribution ∈ adapter.topology.evidenceUniverse) :
    ∃ claim, claim ∈ claims.declared ∧
      canonicalContributionAt identity context claim = contribution := by
  rw [adapter.evidenceUniverseExact] at member
  exact contributions.soundOrigin contribution member

/--
Generic RCC-35 bridge: every item used by a profile certificate to cover a
mandatory failure is a canonical contribution with a sealed raw claim origin.
-/
theorem profile_certificate_mandatory_failure_has_raw_claim_origin
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {Lineage : Type x} {FaultDomain : Type y}
    {identity :
      ContributionIdentitySystem Context Evidence FailureMode Lineage}
    {context : Context}
    {claims : SealedClaimUniverse identity context}
    {contributions : ContributionUniverse identity context claims}
    {adapter :
      CanonicalizedTopology
        identity context claims contributions FaultDomain}
    {Goal : Type z}
    {policies :
      EvidencePolicySystem adapter.topology.evidenceSystem Goal}
    {directSemantics :
      DirectGradeSemantics
        Context Goal (CanonicalContribution FailureMode Lineage)}
    {cutSemantics :
      CutGradeSemantics
        Context Goal (CanonicalContribution FailureMode Lineage)
          FailureMode FaultDomain}
    {goal : Goal}
    (certificate :
      ProfileCertificate adapter.topology policies
        directSemantics cutSemantics goal)
    (failure : FailureMode)
    (mandatory :
      (adapter.topology.evidenceSystem.modelAt
        adapter.topology.context).mandatory failure) :
    ∃ contribution claim,
      contribution ∈ adapter.topology.evidenceUniverse ∧
        CoversMandatoryAt
          adapter.topology.evidenceSystem adapter.topology.context
            contribution failure ∧
        claim ∈ claims.declared ∧
        claim.failure = failure ∧
        canonicalContributionAt identity context claim = contribution ∧
        CoversMandatoryAt identity.evidenceSystem context
          claim.evidence claim.failure := by
  obtain ⟨contribution, member, covers⟩ :=
    certificate.coverage.everyMandatoryCovered failure mandatory
  obtain ⟨claim, rawMember, origin⟩ :=
    topology_item_has_raw_claim_origin adapter contribution member
  have contributionFailure : contribution.failure = failure :=
    ((adapter.mandatoryCoverageExact contribution failure).mp covers).2
  have claimFailure : claim.failure = failure :=
    (congrArg
      (fun canonical : CanonicalContribution FailureMode Lineage =>
        canonical.failure)
      origin).trans contributionFailure
  exact
    ⟨contribution, claim, member, covers, rawMember,
      claimFailure, origin, claims.sound claim rawMember⟩

end Residua.RCC.NoDoubleCounting

import RCC.CommonCauseIndependence

/-!
# RCC-35 Non-Compensable Evidence Profiles

Evidence adequacy is a componentwise partial order over named dimensions.
Surplus in one dimension cannot compensate for a deficit in another.

The low-level profile algebra remains useful on its own.  The authoritative
RCC-35 API below does not accept freely reported required or actual profiles:

* requirements come only from a context-and-goal-indexed pre-state policy;
* RCC-32 certifies failure coverage over the topology's exact evidence bundle;
* direct grades require an explicit, typed grade-semantics relation;
* only cut dimensions use RCC-33 common-cause independence; and
* `profileOf` is projected from proof-carrying dimension witnesses.

This finite kernel does not prove that a real-world item deserves a direct
grade, that the declared logical topology matches physical control, or that
aliases have been canonicalized.  Those remain runtime-refinement,
source-window, and RCC-36 obligations.

Prelude-only Lean 4.14; no Mathlib, no proof holes, and no custom axioms.
-/

namespace Residua.RCC.EvidenceProfile

open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause

universe u v w x y

/-- The frozen v1 evidence dimensions from RCC §22.3. -/
inductive EvidenceDimension where
  | logicalGrade
  | coverageGrade
  | runtimeBindingGrade
  | implementationCut
  | custodyCut
  | operatorCut
  | modelLineageCut
  | reflectionLevel
  | freshnessGrade
  deriving DecidableEq, Repr

/-- The complete closed vocabulary used by the v1 profile. -/
def allDimensions : List EvidenceDimension :=
  [ .logicalGrade
  , .coverageGrade
  , .runtimeBindingGrade
  , .implementationCut
  , .custodyCut
  , .operatorCut
  , .modelLineageCut
  , .reflectionLevel
  , .freshnessGrade
  ]

/-- Every v1 dimension is represented explicitly in `allDimensions`. -/
theorem dimension_covered (dimension : EvidenceDimension) :
    dimension ∈ allDimensions := by
  cases dimension <;> decide

/-- The closed dimension vocabulary contains no duplicate entry. -/
theorem allDimensions_nodup : allDimensions.Nodup := by
  decide

/-- `allDimensions` is the exact, duplicate-free enumeration of the v1 type. -/
theorem allDimensions_exact :
    allDimensions.Nodup ∧
      ∀ dimension : EvidenceDimension, dimension ∈ allDimensions := by
  exact ⟨allDimensions_nodup, dimension_covered⟩

/--
A profile assigns an independent grade to every named dimension.  A zero
requirement makes one dimension optional without removing it from the schema.
-/
abbrev EvidenceProfile := EvidenceDimension → Nat

/--
`actual` meets `required` exactly when every required dimension is met
componentwise.
-/
def Meets (actual required : EvidenceProfile) : Prop :=
  ∀ dimension, required dimension ≤ actual dimension

theorem meets_refl (profile : EvidenceProfile) :
    Meets profile profile := by
  intro dimension
  exact Nat.le_refl (profile dimension)

theorem meets_trans
    {stronger middle weaker : EvidenceProfile}
    (hsm : Meets stronger middle)
    (hmw : Meets middle weaker) :
    Meets stronger weaker := by
  intro dimension
  exact Nat.le_trans (hmw dimension) (hsm dimension)

theorem meets_antisymm
    {left right : EvidenceProfile}
    (hlr : Meets left right)
    (hrl : Meets right left) :
    left = right := by
  funext dimension
  exact Nat.le_antisymm (hrl dimension) (hlr dimension)

/--
One deficient mandatory dimension rejects the whole profile.  No values of
the other dimensions occur in the premise, so no surplus can compensate.
-/
theorem deficit_refuses
    {actual required : EvidenceProfile}
    (dimension : EvidenceDimension)
    (deficit : actual dimension < required dimension) :
    ¬ Meets actual required := by
  intro hmeets
  exact (Nat.not_le_of_lt deficit) (hmeets dimension)

/-- Meeting a profile exposes the exact componentwise witness for any field. -/
theorem meets_dimension
    {actual required : EvidenceProfile}
    (hmeets : Meets actual required)
    (dimension : EvidenceDimension) :
    required dimension ≤ actual dimension :=
  hmeets dimension

/-! ## Proof-carrying RCC-35 policy and witnesses -/

/--
Dimensions whose grades are justified directly by an instance-specific,
typed relation rather than by RCC-32 coverage or an RCC-33 cut.
-/
inductive DirectDimension where
  | logicalGrade
  | runtimeBindingGrade
  | reflectionLevel
  | freshnessGrade
  deriving DecidableEq, Repr

namespace DirectDimension

/-- Embed one direct dimension into the complete RCC-35 vocabulary. -/
def toEvidenceDimension : DirectDimension → EvidenceDimension
  | .logicalGrade => .logicalGrade
  | .runtimeBindingGrade => .runtimeBindingGrade
  | .reflectionLevel => .reflectionLevel
  | .freshnessGrade => .freshnessGrade

end DirectDimension

/-- Dimensions whose grades are common-cause minimum-cut lower bounds. -/
inductive CutDimension where
  | implementationCut
  | custodyCut
  | operatorCut
  | modelLineageCut
  deriving DecidableEq, Repr

namespace CutDimension

/-- Embed one cut dimension into the complete RCC-35 vocabulary. -/
def toEvidenceDimension : CutDimension → EvidenceDimension
  | .implementationCut => .implementationCut
  | .custodyCut => .custodyCut
  | .operatorCut => .operatorCut
  | .modelLineageCut => .modelLineageCut

end CutDimension

/--
One goal's admitted evidence policy.

Mandatory dimensions are not a second caller-controlled set: they are exactly
the dimensions whose required grade is positive.  A well-formed policy cannot
be all zero.  Cut dimensions additionally have an exact partial mapping:
`cutFailure dimension = some failure` iff that cut dimension is mandatory.
Coverage is boolean at RCC-32's current grade, so v1 permits requirements zero
or one for `coverageGrade`.
-/
structure GoalEvidencePolicy (FailureMode : Type u) where
  required : EvidenceProfile
  mandatoryNonempty :
    ∃ dimension : EvidenceDimension, 0 < required dimension
  cutFailure : CutDimension → Option FailureMode
  cutFailureExact :
    ∀ dimension,
      (∃ failure, cutFailure dimension = some failure) ↔
        0 < required dimension.toEvidenceDimension
  coverageAtMostOne : required .coverageGrade ≤ 1

/-- Mandatory status is definitionally the positive part of the profile. -/
def MandatoryDimension
    {FailureMode : Type u}
    (policy : GoalEvidencePolicy FailureMode)
    (dimension : EvidenceDimension) : Prop :=
  0 < policy.required dimension

/--
The only authority for goal requirements is the pre-state policy projection at
the exact evidence context.  A mapped cut failure must be mandatory in
RCC-32's failure universe at that same context.
-/
structure EvidencePolicySystem
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (evidenceSystem :
      FailureEvidenceSystem Context FailureMode Evidence)
    (Goal : Type x) where
  preStatePolicyAt : Context → Goal → GoalEvidencePolicy FailureMode
  mappedFailureMandatory :
    ∀ context goal dimension failure,
      (preStatePolicyAt context goal).cutFailure dimension = some failure →
        (evidenceSystem.modelAt context).mandatory failure

/-- Authoritative context-and-goal-indexed required profile. -/
def requiredAt
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    {Goal : Type x}
    {evidenceSystem :
      FailureEvidenceSystem Context FailureMode Evidence}
    (policies : EvidencePolicySystem evidenceSystem Goal)
    (context : Context)
    (goal : Goal) : EvidenceProfile :=
  (policies.preStatePolicyAt context goal).required

/--
Instance obligation for grades that are neither RCC-32 coverage nor RCC-33
minimum cuts.  A grade is accepted only through `SupportedAt`; a bare `Nat`
has no authority.  Downward closure records the meaning of an ordinal grade.
-/
structure DirectGradeSemantics
    (Context : Type u) (Goal : Type v) (Evidence : Type w) where
  SupportedAt :
    Context → Goal → DirectDimension → List Evidence → Nat → Prop
  zeroSupported :
    ∀ context goal dimension evidence,
      SupportedAt context goal dimension evidence 0
  downwardClosed :
    ∀ context goal dimension evidence stronger weaker,
      SupportedAt context goal dimension evidence stronger →
        weaker ≤ stronger →
          SupportedAt context goal dimension evidence weaker

/--
Pre-state authority for the logical dependency and cost functions consumed by
an RCC-33 cut grade.  These are canonical coordinates indexed by context, goal,
cut dimension, and failure mode.  `CutTopologyBound` below requires pointwise
equality, so one fixed authority cannot admit both an original topology and a
record update that silently inflates `domainCost` or changes `dependsFor`.

The coordinates do not claim that the admitted logical topology matches the
physical world or that domain aliases are canonical.  Those remain
source-refinement and RCC-36 obligations.
-/
structure CutGradeSemantics
    (Context : Type u) (Goal : Type v) (Evidence : Type w)
    (FailureMode : Type x) (FaultDomain : Type y) where
  DependsAt :
    Context → Goal → CutDimension → FailureMode →
      Evidence → FaultDomain → Prop
  CostAt :
    Context → Goal → CutDimension → FailureMode →
      FaultDomain → Nat

/-- Exact binding from an RCC-33 topology to pre-state cut semantics. -/
def CutTopologyBound
    {Context : Type u} {Goal : Type v} {Evidence : Type w}
    {FailureMode : Type x} {FaultDomain : Type y}
    (semantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain)
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (goal : Goal)
    (dimension : CutDimension)
    (failure : FailureMode) : Prop :=
  (∀ evidence domain,
      topology.dependsFor evidence failure domain ↔
        semantics.DependsAt topology.context goal dimension failure
          evidence domain) ∧
    ∀ domain,
      topology.domainCost domain =
        semantics.CostAt topology.context goal dimension failure domain

/--
The four lawful derivations of one dimension's actual grade.

`coverage` is fixed to RCC-32's admitted mandatory-coverage grade.  `cut`
alone consumes RCC-33 and binds the policy's exact failure mapping.  Direct
dimensions consume the explicit instance relation.  The indices prevent one
kind of proof from being reused as another dimension.
-/
inductive GradeDerived
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (policies :
      EvidencePolicySystem topology.evidenceSystem Goal)
    (directSemantics : DirectGradeSemantics Context Goal Evidence)
    (cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain)
    (goal : Goal)
    (_coverage :
      FailureCoverageCertificate
        topology.evidenceSystem topology.context
        topology.failureUniverseSeal topology.evidenceUniverse) :
    EvidenceDimension → Nat → Prop where
  | zero (dimension : EvidenceDimension) :
      GradeDerived topology policies directSemantics cutSemantics goal
        _coverage dimension 0
  | logical
      (grade : Nat)
      (supported :
        directSemantics.SupportedAt topology.context goal .logicalGrade
          topology.evidenceUniverse grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .logicalGrade grade
  | runtimeBinding
      (grade : Nat)
      (supported :
        directSemantics.SupportedAt topology.context goal .runtimeBindingGrade
          topology.evidenceUniverse grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .runtimeBindingGrade grade
  | reflection
      (grade : Nat)
      (supported :
        directSemantics.SupportedAt topology.context goal .reflectionLevel
          topology.evidenceUniverse grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .reflectionLevel grade
  | freshness
      (grade : Nat)
      (supported :
        directSemantics.SupportedAt topology.context goal .freshnessGrade
          topology.evidenceUniverse grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .freshnessGrade grade
  | coverage :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .coverageGrade 1
  | implementationCut
      (failure : FailureMode)
      (bundle : List Evidence)
      (grade : Nat)
      (mapped :
        (policies.preStatePolicyAt topology.context goal).cutFailure
            .implementationCut =
          some failure)
      (topologyBound :
        CutTopologyBound cutSemantics topology goal .implementationCut failure)
      (independent :
        IndependentAtLeast topology failure bundle grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .implementationCut grade
  | custodyCut
      (failure : FailureMode)
      (bundle : List Evidence)
      (grade : Nat)
      (mapped :
        (policies.preStatePolicyAt topology.context goal).cutFailure
            .custodyCut =
          some failure)
      (topologyBound :
        CutTopologyBound cutSemantics topology goal .custodyCut failure)
      (independent :
        IndependentAtLeast topology failure bundle grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .custodyCut grade
  | operatorCut
      (failure : FailureMode)
      (bundle : List Evidence)
      (grade : Nat)
      (mapped :
        (policies.preStatePolicyAt topology.context goal).cutFailure
            .operatorCut =
          some failure)
      (topologyBound :
        CutTopologyBound cutSemantics topology goal .operatorCut failure)
      (independent :
        IndependentAtLeast topology failure bundle grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .operatorCut grade
  | modelLineageCut
      (failure : FailureMode)
      (bundle : List Evidence)
      (grade : Nat)
      (mapped :
        (policies.preStatePolicyAt topology.context goal).cutFailure
            .modelLineageCut =
          some failure)
      (topologyBound :
        CutTopologyBound cutSemantics topology goal .modelLineageCut failure)
      (independent :
        IndependentAtLeast topology failure bundle grade) :
      GradeDerived topology policies directSemantics cutSemantics goal _coverage
        .modelLineageCut grade

/--
One dimension's actual grade is both lawfully derived and no weaker than the
authoritative pre-state requirement.
-/
structure DimensionWitness
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (policies :
      EvidencePolicySystem topology.evidenceSystem Goal)
    (directSemantics : DirectGradeSemantics Context Goal Evidence)
    (cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain)
    (goal : Goal)
    (coverage :
      FailureCoverageCertificate
        topology.evidenceSystem topology.context
        topology.failureUniverseSeal topology.evidenceUniverse)
    (dimension : EvidenceDimension) where
  grade : Nat
  derived :
    GradeDerived topology policies directSemantics cutSemantics goal
      coverage dimension grade
  meetsRequired :
    requiredAt policies topology.context goal dimension ≤ grade

/--
The authoritative RCC-35 certificate.  Callers provide neither a free
`required` profile nor a free `actual` profile.  The evidence bundle is exactly
the RCC-33 topology's admitted universe for RCC-32 coverage and direct grades;
cut grades use RCC-33-admitted same-context support sub-bundles.  The context
is definitionally the topology's context.
-/
structure ProfileCertificate
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (policies :
      EvidencePolicySystem topology.evidenceSystem Goal)
    (directSemantics : DirectGradeSemantics Context Goal Evidence)
    (cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain)
    (goal : Goal) where
  coverage :
    FailureCoverageCertificate
      topology.evidenceSystem topology.context
      topology.failureUniverseSeal topology.evidenceUniverse
  dimension :
    ∀ evidenceDimension,
      DimensionWitness topology policies directSemantics cutSemantics goal
        coverage
        evidenceDimension

/-- The actual profile is only the projection of certified witnesses. -/
def profileOf
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {policies :
      EvidencePolicySystem topology.evidenceSystem Goal}
    {directSemantics : DirectGradeSemantics Context Goal Evidence}
    {cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain}
    {goal : Goal}
    (certificate :
      ProfileCertificate topology policies directSemantics cutSemantics goal) :
    EvidenceProfile :=
  fun dimension => (certificate.dimension dimension).grade

/--
A mandatory cut dimension mechanically exposes the exact policy-mapped
failure, an RCC-33 bundle, and a grade meeting the pre-state threshold.
-/
theorem certified_mandatory_cut
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {policies :
      EvidencePolicySystem topology.evidenceSystem Goal}
    {directSemantics : DirectGradeSemantics Context Goal Evidence}
    {cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain}
    {goal : Goal}
    (certificate :
      ProfileCertificate topology policies directSemantics cutSemantics goal)
    (dimension : CutDimension)
    (mandatory :
      0 <
        requiredAt policies topology.context goal
          dimension.toEvidenceDimension) :
    ∃ failure bundle grade,
      (policies.preStatePolicyAt topology.context goal).cutFailure dimension =
          some failure ∧
        CutTopologyBound cutSemantics topology goal dimension failure ∧
        IndependentAtLeast topology failure bundle grade ∧
        requiredAt policies topology.context goal
            dimension.toEvidenceDimension ≤
          grade := by
  cases dimension with
  | implementationCut =>
      obtain ⟨grade, derived, meets⟩ :=
        certificate.dimension EvidenceDimension.implementationCut
      cases derived with
      | zero _ =>
          exact False.elim
            ((Nat.not_lt_zero _) (Nat.lt_of_lt_of_le mandatory meets))
      | implementationCut failure bundle grade mapped bound independent =>
          exact ⟨failure, bundle, grade, mapped, bound, independent, meets⟩
  | custodyCut =>
      obtain ⟨grade, derived, meets⟩ :=
        certificate.dimension EvidenceDimension.custodyCut
      cases derived with
      | zero _ =>
          exact False.elim
            ((Nat.not_lt_zero _) (Nat.lt_of_lt_of_le mandatory meets))
      | custodyCut failure bundle grade mapped bound independent =>
          exact ⟨failure, bundle, grade, mapped, bound, independent, meets⟩
  | operatorCut =>
      obtain ⟨grade, derived, meets⟩ :=
        certificate.dimension EvidenceDimension.operatorCut
      cases derived with
      | zero _ =>
          exact False.elim
            ((Nat.not_lt_zero _) (Nat.lt_of_lt_of_le mandatory meets))
      | operatorCut failure bundle grade mapped bound independent =>
          exact ⟨failure, bundle, grade, mapped, bound, independent, meets⟩
  | modelLineageCut =>
      obtain ⟨grade, derived, meets⟩ :=
        certificate.dimension EvidenceDimension.modelLineageCut
      cases derived with
      | zero _ =>
          exact False.elim
            ((Nat.not_lt_zero _) (Nat.lt_of_lt_of_le mandatory meets))
      | modelLineageCut failure bundle grade mapped bound independent =>
          exact ⟨failure, bundle, grade, mapped, bound, independent, meets⟩

/-- RCC-35: a proof-carrying profile meets its exact pre-state requirement. -/
theorem certified_profile_meets_required
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {Goal : Type y}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {policies :
      EvidencePolicySystem topology.evidenceSystem Goal}
    {directSemantics : DirectGradeSemantics Context Goal Evidence}
    {cutSemantics :
      CutGradeSemantics Context Goal Evidence FailureMode FaultDomain}
    {goal : Goal}
    (certificate :
      ProfileCertificate topology policies directSemantics cutSemantics goal) :
    Meets (profileOf certificate)
      (requiredAt policies topology.context goal) := by
  intro dimension
  exact (certificate.dimension dimension).meetsRequired

end Residua.RCC.EvidenceProfile

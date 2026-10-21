import RCC.EvidenceProfile

/-!
# RCC-35 Evidence Profile Witnesses

Evidence strength is componentwise.  Surplus in proof, implementation, or
receipt-related dimensions cannot compensate for a missing mandatory
dimension.

The finite fixtures below instantiate admitted logical relations only.  They
do not claim that production evidence deserves these grades, that the logical
fault topology matches physical control, or that RCC-36 has canonicalized
real aliases.
-/

namespace Residua.RCC.EvidenceProfile.Tests

open Residua.RCC.EvidenceProfile
open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause

def requiredRuntimeBound : EvidenceProfile
  | .logicalGrade => 4
  | .runtimeBindingGrade => 1
  | _ => 0

def highProofWithoutRuntime : EvidenceProfile
  | .logicalGrade => 100
  | .runtimeBindingGrade => 0
  | _ => 100

def requiredCoverage : EvidenceProfile
  | .coverageGrade => 1
  | _ => 0

def manyEnginesWithoutCoverage : EvidenceProfile
  | .coverageGrade => 0
  | .implementationCut => 100
  | _ => 100

def requiredFreshness : EvidenceProfile
  | .freshnessGrade => 1
  | _ => 0

def manyReceiptsButStale : EvidenceProfile
  | .freshnessGrade => 0
  | _ => 100

theorem high_proof_cannot_compensate_missing_runtime_binding :
    ¬ Meets highProofWithoutRuntime requiredRuntimeBound := by
  exact deficit_refuses .runtimeBindingGrade (by decide)

theorem engine_diversity_cannot_compensate_missing_coverage :
    ¬ Meets manyEnginesWithoutCoverage requiredCoverage := by
  exact deficit_refuses .coverageGrade (by decide)

theorem receipt_quantity_cannot_compensate_missing_freshness :
    ¬ Meets manyReceiptsButStale requiredFreshness := by
  exact deficit_refuses .freshnessGrade (by decide)

def exactRequired : EvidenceProfile
  | .logicalGrade => 4
  | .coverageGrade => 2
  | .runtimeBindingGrade => 1
  | .implementationCut => 2
  | .custodyCut => 2
  | .operatorCut => 2
  | .modelLineageCut => 2
  | .reflectionLevel => 1
  | .freshnessGrade => 1

theorem exact_profile_meets_itself : Meets exactRequired exactRequired :=
  meets_refl exactRequired

theorem componentwise_order_is_antisymmetric
    (left right : EvidenceProfile)
    (hlr : Meets left right)
    (hrl : Meets right left) :
    left = right :=
  meets_antisymm hlr hrl

/-! ## Concrete RCC-32/RCC-33 fixture -/

inductive TestContext where
  | full
  | proofOnly
  | enginesOnly
  | staleOnly
  | aliasOnly
  | relaxed
  deriving DecidableEq, Repr

inductive TestGoal where
  | release
  deriving DecidableEq, Repr

inductive TestFailure where
  | baseline
  | specificationWrong
  | implementationCommonCause
  deriving DecidableEq, Repr

inductive TestEvidence where
  | formalProof
  | runtimeReceipt
  | specificationReview
  | engineA
  | engineB
  | freshReceipt
  | staleReceiptA
  | staleReceiptB
  | aliasA
  | aliasB
  deriving DecidableEq, Repr

inductive TestDomain where
  | left
  | right
  | shared
  deriving DecidableEq, Repr

def mandatoryFailure : TestContext → TestFailure → Prop
  | .full, _ => True
  | .proofOnly, .baseline => True
  | .enginesOnly, .specificationWrong => True
  | .staleOnly, .baseline => True
  | .aliasOnly, .baseline => True
  | .aliasOnly, .implementationCommonCause => True
  | .relaxed, .baseline => True
  | _, _ => False

def failureModel (context : TestContext) :
    FailureUniverse TestFailure where
  inScope := fun _ => True
  mandatory := mandatoryFailure context
  mandatoryInScope := by
    intro _ _
    trivial
  declared :=
    [ .baseline
    , .specificationWrong
    , .implementationCommonCause
    ]

def failureModelSeal (context : TestContext) :
    FailureUniverseSeal (failureModel context) where
  declaredSound := by
    intro _ _
    trivial
  declaredComplete := by
    intro failure _
    cases failure <;> simp [failureModel]

def admittedEvidence : TestContext → List TestEvidence
  | .full =>
      [ .formalProof
      , .runtimeReceipt
      , .specificationReview
      , .engineA
      , .engineB
      , .freshReceipt
      ]
  | .proofOnly => [.formalProof]
  | .enginesOnly => [.engineA, .engineB]
  | .staleOnly => [.staleReceiptA, .staleReceiptB]
  | .aliasOnly => [.aliasA, .aliasB]
  | .relaxed => [.formalProof]

def coversFailure :
    TestContext → TestEvidence → TestFailure → Prop
  | .full, .formalProof, .baseline => True
  | .full, .specificationReview, .specificationWrong => True
  | .full, .engineA, .implementationCommonCause => True
  | .full, .engineB, .implementationCommonCause => True
  | .proofOnly, .formalProof, .baseline => True
  | .staleOnly, .staleReceiptA, .baseline => True
  | .staleOnly, .staleReceiptB, .baseline => True
  | .aliasOnly, .aliasA, .baseline => True
  | .aliasOnly, .aliasB, .baseline => True
  | .aliasOnly, .aliasA, .implementationCommonCause => True
  | .aliasOnly, .aliasB, .implementationCommonCause => True
  | .relaxed, .formalProof, .baseline => True
  | _, _, _ => False

def testEvidenceSystem :
    FailureEvidenceSystem TestContext TestFailure TestEvidence where
  modelAt := failureModel
  AdmittedAt := fun context evidence =>
    evidence ∈ admittedEvidence context
  CoversAt := fun context evidence failure grade =>
    match grade with
    | .mandatory => coversFailure context evidence failure
    | .optional => False

def evidenceRoot : TestEvidence → TestDomain
  | .engineB => .right
  | .aliasA => .shared
  | .aliasB => .shared
  | _ => .left

def testTopology (context : TestContext) :
    SealedFiniteTopology
      TestContext TestEvidence TestFailure TestDomain where
  evidenceSystem := testEvidenceSystem
  context := context
  failureUniverseSeal := failureModelSeal context
  evidenceUniverse := admittedEvidence context
  faultDomainUniverse := [.left, .right, .shared]
  evidenceNoDup := by
    cases context <;> decide
  faultDomainNoDup := by
    decide
  evidenceSound := by
    intro evidence member
    exact member
  evidenceComplete := by
    intro evidence admitted
    exact admitted
  faultDomainComplete := by
    intro domain
    cases domain <;> simp
  dependsFor := fun evidence _ domain =>
    evidenceRoot evidence = domain
  dependencyRooted := by
    intro evidence _ _ _
    exact ⟨evidenceRoot evidence, by
      cases evidence <;> simp [evidenceRoot], rfl⟩
  domainCost := fun _ => 1
  domainCostPositive := by
    intro _
    exact Nat.zero_lt_succ 0

def fullCoverage :
    FailureCoverageCertificate
      testEvidenceSystem .full (failureModelSeal .full)
      (admittedEvidence .full) where
  mandatoryNonempty := ⟨.baseline, by trivial⟩
  everyMandatoryCovered := by
    intro failure _
    cases failure with
    | baseline =>
        exact
          ⟨.formalProof, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | specificationWrong =>
        exact
          ⟨.specificationReview, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | implementationCommonCause =>
        exact
          ⟨.engineA, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩

def proofOnlyCoverage :
    FailureCoverageCertificate
      testEvidenceSystem .proofOnly (failureModelSeal .proofOnly)
      (admittedEvidence .proofOnly) where
  mandatoryNonempty := ⟨.baseline, by trivial⟩
  everyMandatoryCovered := by
    intro failure mandatory
    cases failure with
    | baseline =>
        exact
          ⟨.formalProof, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | specificationWrong =>
        exact False.elim mandatory
    | implementationCommonCause =>
        exact False.elim mandatory

def staleCoverage :
    FailureCoverageCertificate
      testEvidenceSystem .staleOnly (failureModelSeal .staleOnly)
      (admittedEvidence .staleOnly) where
  mandatoryNonempty := ⟨.baseline, by trivial⟩
  everyMandatoryCovered := by
    intro failure mandatory
    cases failure with
    | baseline =>
        exact
          ⟨.staleReceiptA, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | specificationWrong =>
        exact False.elim mandatory
    | implementationCommonCause =>
        exact False.elim mandatory

def aliasCoverage :
    FailureCoverageCertificate
      testEvidenceSystem .aliasOnly (failureModelSeal .aliasOnly)
      (admittedEvidence .aliasOnly) where
  mandatoryNonempty := ⟨.baseline, by trivial⟩
  everyMandatoryCovered := by
    intro failure mandatory
    cases failure with
    | baseline =>
        exact
          ⟨.aliasA, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | specificationWrong =>
        exact False.elim mandatory
    | implementationCommonCause =>
        exact
          ⟨.aliasA, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩

def relaxedCoverage :
    FailureCoverageCertificate
      testEvidenceSystem .relaxed (failureModelSeal .relaxed)
      (admittedEvidence .relaxed) where
  mandatoryNonempty := ⟨.baseline, by trivial⟩
  everyMandatoryCovered := by
    intro failure mandatory
    cases failure with
    | baseline =>
        exact
          ⟨.formalProof, by simp [admittedEvidence],
            by
              simp [CoversMandatoryAt, testEvidenceSystem,
                admittedEvidence, coversFailure]⟩
    | specificationWrong =>
        exact False.elim mandatory
    | implementationCommonCause =>
        exact False.elim mandatory

theorem engines_have_no_specification_coverage :
    ¬ FailureCoverageCertificate
      testEvidenceSystem .enginesOnly (failureModelSeal .enginesOnly)
      (admittedEvidence .enginesOnly) := by
  intro coverage
  obtain ⟨item, _, covered⟩ :=
    coverage.everyMandatoryCovered .specificationWrong (by trivial)
  cases item <;>
    simp [CoversMandatoryAt, testEvidenceSystem,
      admittedEvidence, coversFailure] at covered

def requiredProfileAt : TestContext → EvidenceProfile
  | .full, .logicalGrade => 1
  | .full, .coverageGrade => 1
  | .full, .runtimeBindingGrade => 1
  | .full, .implementationCut => 2
  | .full, .freshnessGrade => 1
  | .proofOnly, .logicalGrade => 4
  | .proofOnly, .coverageGrade => 1
  | .proofOnly, .runtimeBindingGrade => 1
  | .enginesOnly, .coverageGrade => 1
  | .staleOnly, .coverageGrade => 1
  | .staleOnly, .freshnessGrade => 1
  | .aliasOnly, .coverageGrade => 1
  | .aliasOnly, .implementationCut => 2
  | .relaxed, .coverageGrade => 1
  | _, _ => 0

def cutFailureAt :
    TestContext → CutDimension → Option TestFailure
  | .full, .implementationCut => some .implementationCommonCause
  | .aliasOnly, .implementationCut => some .implementationCommonCause
  | _, _ => none

def goalPolicyAt (context : TestContext) :
    GoalEvidencePolicy TestFailure where
  required := requiredProfileAt context
  mandatoryNonempty := by
    cases context with
    | full => exact ⟨.logicalGrade, by decide⟩
    | proofOnly => exact ⟨.runtimeBindingGrade, by decide⟩
    | enginesOnly => exact ⟨.coverageGrade, by decide⟩
    | staleOnly => exact ⟨.freshnessGrade, by decide⟩
    | aliasOnly => exact ⟨.implementationCut, by decide⟩
    | relaxed => exact ⟨.coverageGrade, by decide⟩
  cutFailure := cutFailureAt context
  cutFailureExact := by
    intro dimension
    cases context <;> cases dimension <;>
      simp [cutFailureAt, requiredProfileAt,
        CutDimension.toEvidenceDimension]
  coverageAtMostOne := by
    cases context <;> exact Nat.le_refl 1

def testPolicies :
    EvidencePolicySystem testEvidenceSystem TestGoal where
  preStatePolicyAt := fun context _ => goalPolicyAt context
  mappedFailureMandatory := by
    intro context _ dimension failure mapped
    cases context <;> cases dimension <;>
      simp [goalPolicyAt, cutFailureAt] at mapped
    all_goals
      subst failure
      trivial

def directMaximum
    (dimension : DirectDimension)
    (evidence : List TestEvidence) : Nat :=
  match dimension with
  | .logicalGrade =>
      if TestEvidence.formalProof ∈ evidence then 100 else 0
  | .runtimeBindingGrade =>
      if TestEvidence.runtimeReceipt ∈ evidence then 1 else 0
  | .reflectionLevel => 0
  | .freshnessGrade =>
      if TestEvidence.freshReceipt ∈ evidence then 1 else 0

def testDirectSemantics :
    DirectGradeSemantics TestContext TestGoal TestEvidence where
  SupportedAt := fun _ _ dimension evidence grade =>
    grade ≤ directMaximum dimension evidence
  zeroSupported := by
    intro _ _ _ _
    exact Nat.zero_le _
  downwardClosed := by
    intro _ _ _ _ stronger weaker supported weakerBelow
    exact Nat.le_trans weakerBelow supported

def testCutSemantics :
    CutGradeSemantics
      TestContext TestGoal TestEvidence TestFailure TestDomain where
  DependsAt := fun _ _ _ _ evidence domain =>
    evidenceRoot evidence = domain
  CostAt := fun _ _ _ _ _ => 1

theorem test_topology_binds_authoritative_cut
    (context : TestContext)
    (dimension : CutDimension)
    (failure : TestFailure) :
    CutTopologyBound testCutSemantics (testTopology context)
      .release dimension failure := by
  constructor
  · intro _ _
    rfl
  · intro _
    rfl

theorem unit_test_cut_cost_eq_length
    (context : TestContext)
    (cut : List TestDomain) :
    CutCost (testTopology context) cut = cut.length := by
  induction cut with
  | nil =>
      rfl
  | cons domain rest ih =>
      change 1 + CutCost (testTopology context) rest = rest.length + 1
      rw [ih]
      exact Nat.add_comm 1 rest.length

theorem left_and_right_members_force_length_two
    (cut : List TestDomain)
    (leftMember : TestDomain.left ∈ cut)
    (rightMember : TestDomain.right ∈ cut) :
    2 ≤ cut.length := by
  cases cut with
  | nil =>
      simp at leftMember
  | cons first rest =>
      cases rest with
      | nil =>
          cases first <;> simp_all
      | cons second tail =>
          simp

def fullImplementationSupport :
    AdmittedSupportBundle
      (testTopology .full) .implementationCommonCause
      [.engineA, .engineB] where
  failureMandatory := by
    trivial
  nonempty := by
    decide
  everyItemSupports := by
    intro evidence member
    simp at member
    rcases member with left | right
    · subst evidence
      constructor
      · simp [testTopology, admittedEvidence]
      · simp [CoversMandatoryAt, testTopology, testEvidenceSystem,
          coversFailure, admittedEvidence]
    · subst evidence
      constructor
      · simp [testTopology, admittedEvidence]
      · simp [CoversMandatoryAt, testTopology, testEvidenceSystem,
          coversFailure, admittedEvidence]

def fullImplementationIndependent :
    IndependentAtLeast
      (testTopology .full) .implementationCommonCause
      [.engineA, .engineB] 2 := by
  constructor
  · exact fullImplementationSupport
  · intro cut _ breaks
    have leftMember : TestDomain.left ∈ cut := by
      obtain ⟨domain, member, depends⟩ :=
        breaks .engineA (by simp)
      cases domain <;>
        simp [testTopology, evidenceRoot] at depends
      exact member
    have rightMember : TestDomain.right ∈ cut := by
      obtain ⟨domain, member, depends⟩ :=
        breaks .engineB (by simp)
      cases domain <;>
        simp [testTopology, evidenceRoot] at depends
      exact member
    rw [unit_test_cut_cost_eq_length]
    exact left_and_right_members_force_length_two cut
      leftMember rightMember

def fullProfileCertificate :
    ProfileCertificate
      (testTopology .full) testPolicies testDirectSemantics
      testCutSemantics .release where
  coverage := fullCoverage
  dimension := by
    intro dimension
    cases dimension with
    | logicalGrade =>
        exact
          { grade := 1
            derived := .logical 1 (by
              simp [testDirectSemantics, directMaximum, testTopology,
                admittedEvidence])
            meetsRequired := Nat.le_refl 1 }
    | coverageGrade =>
        exact
          { grade := 1
            derived := .coverage
            meetsRequired := Nat.le_refl 1 }
    | runtimeBindingGrade =>
        exact
          { grade := 1
            derived := .runtimeBinding 1 (by
              simp [testDirectSemantics, directMaximum, testTopology,
                admittedEvidence])
            meetsRequired := Nat.le_refl 1 }
    | implementationCut =>
        exact
          { grade := 2
            derived := by
              exact GradeDerived.implementationCut
                (failure := TestFailure.implementationCommonCause)
                (bundle := [.engineA, .engineB])
                (grade := 2)
                (mapped := by rfl)
                (topologyBound :=
                  test_topology_binds_authoritative_cut
                    .full .implementationCut
                    .implementationCommonCause)
                (independent := fullImplementationIndependent)
            meetsRequired := Nat.le_refl 2 }
    | custodyCut =>
        exact
          { grade := 0
            derived := .zero .custodyCut
            meetsRequired := Nat.zero_le _ }
    | operatorCut =>
        exact
          { grade := 0
            derived := .zero .operatorCut
            meetsRequired := Nat.zero_le _ }
    | modelLineageCut =>
        exact
          { grade := 0
            derived := .zero .modelLineageCut
            meetsRequired := Nat.zero_le _ }
    | reflectionLevel =>
        exact
          { grade := 0
            derived := .zero .reflectionLevel
            meetsRequired := Nat.zero_le _ }
    | freshnessGrade =>
        exact
          { grade := 1
            derived := .freshness 1 (by
              simp [testDirectSemantics, directMaximum, testTopology,
                admittedEvidence])
            meetsRequired := Nat.le_refl 1 }

theorem full_certificate_meets_pre_state_policy :
    Meets (profileOf fullProfileCertificate)
      (requiredAt testPolicies .full .release) :=
  certified_profile_meets_required fullProfileCertificate

theorem full_certificate_extracts_authoritative_implementation_cut :
    ∃ failure bundle grade,
      (testPolicies.preStatePolicyAt .full .release).cutFailure
          .implementationCut =
        some failure ∧
      CutTopologyBound testCutSemantics (testTopology .full)
        .release .implementationCut failure ∧
      IndependentAtLeast (testTopology .full) failure bundle grade ∧
      requiredAt testPolicies .full .release .implementationCut ≤ grade := by
  exact certified_mandatory_cut fullProfileCertificate
    .implementationCut (by decide)

def proofOnlyLogicalWitness :
    DimensionWitness
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release proofOnlyCoverage .logicalGrade where
  grade := 100
  derived := .logical 100 (by
    simp [testDirectSemantics, directMaximum, testTopology,
      admittedEvidence])
  meetsRequired := by
    decide

theorem high_proof_grade_is_typed_not_self_reported :
    proofOnlyLogicalWitness.grade = 100 := by
  rfl

theorem high_proof_without_runtime_has_no_runtime_witness :
    DimensionWitness
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release proofOnlyCoverage
      .runtimeBindingGrade → False := by
  rintro ⟨grade, derived, meets⟩
  have required : 1 ≤ grade := by
    simpa [requiredAt, testPolicies, goalPolicyAt, requiredProfileAt] using meets
  cases derived with
  | zero _ =>
      exact (Nat.not_succ_le_zero 0) required
  | runtimeBinding grade supported =>
      have atMostZero : grade ≤ 0 := by
        simpa [testDirectSemantics, directMaximum, testTopology,
          admittedEvidence] using supported
      exact (Nat.not_succ_le_zero 0) (Nat.le_trans required atMostZero)

theorem high_proof_without_runtime_has_no_profile_certificate :
    ProfileCertificate
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False := by
  intro certificate
  exact high_proof_without_runtime_has_no_runtime_witness
    (certificate.dimension .runtimeBindingGrade)

theorem many_engines_without_spec_coverage_has_no_profile_certificate :
    ProfileCertificate
      (testTopology .enginesOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False := by
  intro certificate
  exact engines_have_no_specification_coverage certificate.coverage

theorem stale_receipts_have_no_freshness_witness :
    DimensionWitness
      (testTopology .staleOnly) testPolicies testDirectSemantics
      testCutSemantics .release staleCoverage .freshnessGrade → False := by
  rintro ⟨grade, derived, meets⟩
  have required : 1 ≤ grade := by
    simpa [requiredAt, testPolicies, goalPolicyAt, requiredProfileAt] using meets
  cases derived with
  | zero _ =>
      exact (Nat.not_succ_le_zero 0) required
  | freshness grade supported =>
      have atMostZero : grade ≤ 0 := by
        simpa [testDirectSemantics, directMaximum, testTopology,
          admittedEvidence] using supported
      exact (Nat.not_succ_le_zero 0) (Nat.le_trans required atMostZero)

theorem stale_receipts_have_no_profile_certificate :
    ProfileCertificate
      (testTopology .staleOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False := by
  intro certificate
  exact stale_receipts_have_no_freshness_witness
    (certificate.dimension .freshnessGrade)

theorem naked_nat_cannot_forge_runtime_grade :
    ¬ GradeDerived
      (testTopology .proofOnly) testPolicies testDirectSemantics
      testCutSemantics .release proofOnlyCoverage
      .runtimeBindingGrade 100 := by
  intro derived
  cases derived with
  | runtimeBinding _ supported =>
      simp [testDirectSemantics, directMaximum, testTopology,
        admittedEvidence] at supported

def allZeroProfile : EvidenceProfile := fun _ => 0

theorem all_zero_policy_is_rejected :
    ¬ ∃ policy : GoalEvidencePolicy TestFailure,
      policy.required = allZeroProfile := by
  rintro ⟨policy, requiredIsZero⟩
  obtain ⟨dimension, mandatory⟩ := policy.mandatoryNonempty
  rw [requiredIsZero] at mandatory
  exact (Nat.not_lt_zero _) mandatory

def relaxedCertificate :
    ProfileCertificate
      (testTopology .relaxed) testPolicies testDirectSemantics
      testCutSemantics .release where
  coverage := relaxedCoverage
  dimension := by
    intro dimension
    cases dimension with
    | coverageGrade =>
        exact
          { grade := 1
            derived := .coverage
            meetsRequired := by
              exact Nat.le_refl 1 }
    | logicalGrade =>
        exact
          { grade := 0
            derived := .zero .logicalGrade
            meetsRequired := Nat.zero_le _ }
    | runtimeBindingGrade =>
        exact
          { grade := 0
            derived := .zero .runtimeBindingGrade
            meetsRequired := Nat.zero_le _ }
    | implementationCut =>
        exact
          { grade := 0
            derived := .zero .implementationCut
            meetsRequired := Nat.zero_le _ }
    | custodyCut =>
        exact
          { grade := 0
            derived := .zero .custodyCut
            meetsRequired := Nat.zero_le _ }
    | operatorCut =>
        exact
          { grade := 0
            derived := .zero .operatorCut
            meetsRequired := Nat.zero_le _ }
    | modelLineageCut =>
        exact
          { grade := 0
            derived := .zero .modelLineageCut
            meetsRequired := Nat.zero_le _ }
    | reflectionLevel =>
        exact
          { grade := 0
            derived := .zero .reflectionLevel
            meetsRequired := Nat.zero_le _ }
    | freshnessGrade =>
        exact
          { grade := 0
            derived := .zero .freshnessGrade
            meetsRequired := Nat.zero_le _ }

theorem relaxed_certificate_meets_only_its_pre_state_policy :
    Meets (profileOf relaxedCertificate)
      (requiredAt testPolicies .relaxed .release) :=
  certified_profile_meets_required relaxedCertificate

theorem relaxed_certificate_cannot_transport_to_full_context :
    ¬ Meets (profileOf relaxedCertificate)
      (requiredAt testPolicies .full .release) := by
  exact deficit_refuses .runtimeBindingGrade (by decide)

theorem aliases_share_one_breaking_domain
    (bundle : List TestEvidence)
    (support :
      AdmittedSupportBundle
        (testTopology .aliasOnly) .implementationCommonCause bundle) :
    BreaksBundle
      (testTopology .aliasOnly) .implementationCommonCause bundle
      [.shared] := by
  intro evidence member
  have inUniverse :=
    (support.everyItemSupports evidence member).1
  have rootShared : evidenceRoot evidence = .shared := by
    simp [testTopology, admittedEvidence] at inUniverse
    rcases inUniverse with left | right
    · subst evidence
      rfl
    · subst evidence
      rfl
  exact ⟨.shared, by simp, rootShared⟩

theorem aliases_cannot_forge_cut_dimension_witness :
    DimensionWitness
      (testTopology .aliasOnly) testPolicies testDirectSemantics
      testCutSemantics .release aliasCoverage .implementationCut → False := by
  rintro ⟨grade, derived, meets⟩
  have required : 2 ≤ grade := by
    simpa [requiredAt, testPolicies, goalPolicyAt, requiredProfileAt] using meets
  cases derived with
  | zero _ =>
      exact (by
        have impossible : ¬ 2 ≤ 0 := by decide
        exact impossible required)
  | implementationCut failure bundle grade mapped _ independent =>
      cases failure <;>
        simp [testPolicies, goalPolicyAt, cutFailureAt, testTopology] at mapped
      have valid : ValidCut (testTopology .aliasOnly) [.shared] := by
        constructor
        · decide
        · intro domain member
          simp at member
          subst domain
          simp [testTopology]
      have atMostOne : grade ≤ 1 := by
        simpa [CutCost, testTopology] using
          independent.2 [.shared] valid
            (aliases_share_one_breaking_domain bundle independent.1)
      have impossible : ¬ 2 ≤ 1 := by decide
      exact impossible (Nat.le_trans required atMostOne)

theorem aliases_cannot_forge_profile_certificate :
    ProfileCertificate
      (testTopology .aliasOnly) testPolicies testDirectSemantics
      testCutSemantics .release → False := by
  intro certificate
  exact aliases_cannot_forge_cut_dimension_witness
    (certificate.dimension .implementationCut)

def inflatedAliasTopology :
    SealedFiniteTopology
      TestContext TestEvidence TestFailure TestDomain :=
  { testTopology .aliasOnly with
    domainCost := fun _ => 100
    domainCostPositive := by
      intro _
      exact Nat.zero_lt_succ 99 }

theorem inflated_cost_topology_is_not_authoritatively_bound :
    ¬ CutTopologyBound testCutSemantics inflatedAliasTopology
      .release .implementationCut .implementationCommonCause := by
  intro bound
  have sharedCost := bound.2 TestDomain.shared
  simp [inflatedAliasTopology, testCutSemantics] at sharedCost

theorem inflated_cost_cannot_forge_cut_grade :
    GradeDerived
      inflatedAliasTopology testPolicies testDirectSemantics
      testCutSemantics .release aliasCoverage .implementationCut 100 →
      False := by
  intro derived
  cases derived with
  | implementationCut _ _ _ _ bound _ =>
      exact inflated_cost_topology_is_not_authoritatively_bound bound

#print axioms high_proof_cannot_compensate_missing_runtime_binding
#print axioms engine_diversity_cannot_compensate_missing_coverage
#print axioms receipt_quantity_cannot_compensate_missing_freshness
#print axioms exact_profile_meets_itself
#print axioms componentwise_order_is_antisymmetric
#print axioms Residua.RCC.EvidenceProfile.certified_mandatory_cut
#print axioms Residua.RCC.EvidenceProfile.certified_profile_meets_required
#print axioms engines_have_no_specification_coverage
#print axioms test_topology_binds_authoritative_cut
#print axioms full_certificate_meets_pre_state_policy
#print axioms full_certificate_extracts_authoritative_implementation_cut
#print axioms high_proof_grade_is_typed_not_self_reported
#print axioms high_proof_without_runtime_has_no_runtime_witness
#print axioms high_proof_without_runtime_has_no_profile_certificate
#print axioms many_engines_without_spec_coverage_has_no_profile_certificate
#print axioms stale_receipts_have_no_freshness_witness
#print axioms stale_receipts_have_no_profile_certificate
#print axioms naked_nat_cannot_forge_runtime_grade
#print axioms all_zero_policy_is_rejected
#print axioms relaxed_certificate_meets_only_its_pre_state_policy
#print axioms relaxed_certificate_cannot_transport_to_full_context
#print axioms aliases_share_one_breaking_domain
#print axioms aliases_cannot_forge_cut_dimension_witness
#print axioms aliases_cannot_forge_profile_certificate
#print axioms inflated_cost_topology_is_not_authoritatively_bound
#print axioms inflated_cost_cannot_forge_cut_grade

end Residua.RCC.EvidenceProfile.Tests


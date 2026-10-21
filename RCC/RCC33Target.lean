import RCC.CommonCauseIndependence

/-!
# RCC-33 target package

This target is a concrete, finite common-cause instance.  It uses one sealed
mandatory failure, one admitted mandatory-grade evidence item, and one rooted
fault domain.  The positive certificate is an exact minimum-cut certificate;
the negative witnesses refuse an empty support bundle, optional/wrong evidence,
and a threshold above the declared cut cost.

The target is deliberately self-contained.  It does not alter the global RCC
registry, source window, Nanoda root, or official closure count.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC33Target

open Residua.RCC.FailureCoverage
open Residua.RCC.CommonCause

inductive DemoContext where
  | current
  deriving DecidableEq, Repr

inductive DemoFailure where
  | commonCause
  deriving DecidableEq, Repr

inductive DemoEvidence where
  | sourceEvidence
  | optionalEvidence
  deriving DecidableEq, Repr

inductive DemoDomain where
  | host
  deriving DecidableEq, Repr

def demoModel : FailureUniverse DemoFailure where
  inScope := fun _ => True
  mandatory := fun _ => True
  mandatoryInScope := by
    intro failure _
    trivial
  declared := [.commonCause]

def demoSystem : FailureEvidenceSystem DemoContext DemoFailure DemoEvidence where
  modelAt := fun _ => demoModel
  AdmittedAt := fun _ evidence => evidence = .sourceEvidence
  CoversAt := fun _ evidence failure grade =>
    evidence = .sourceEvidence ∧
      failure = .commonCause ∧
      grade = .mandatory

def demoUniverseSeal : FailureUniverseSeal (demoSystem.modelAt .current) where
  declaredSound := by
    intro failure member
    trivial
  declaredComplete := by
    intro failure inScope
    cases failure
    change DemoFailure.commonCause ∈ [.commonCause]
    simp

def demoTopology :
    SealedFiniteTopology DemoContext DemoEvidence DemoFailure DemoDomain where
  evidenceSystem := demoSystem
  context := .current
  failureUniverseSeal := demoUniverseSeal
  evidenceUniverse := [.sourceEvidence]
  faultDomainUniverse := [.host]
  evidenceNoDup := by simp
  faultDomainNoDup := by simp
  evidenceSound := by
    intro evidence member
    cases evidence with
    | sourceEvidence => rfl
    | optionalEvidence => simp at member
  evidenceComplete := by
    intro evidence admitted
    cases evidence with
    | sourceEvidence => simp
    | optionalEvidence => simp [demoSystem] at admitted
  faultDomainComplete := by
    intro domain
    cases domain <;> simp
  dependsFor := fun evidence failure domain =>
    evidence = .sourceEvidence ∧
      failure = .commonCause ∧
      domain = .host
  dependencyRooted := by
    intro evidence failure evidenceMember evidenceCovers
    cases evidence with
    | sourceEvidence =>
        cases failure with
        | commonCause => exact ⟨.host, by simp, by simp⟩
    | optionalEvidence =>
        simp [demoSystem, CoversMandatoryAt] at evidenceCovers
  domainCost := fun _ => 1
  domainCostPositive := by
    intro domain
    cases domain
    decide

def demoBundle :
    AdmittedSupportBundle demoTopology .commonCause [.sourceEvidence] where
  failureMandatory := by trivial
  nonempty := by simp
  everyItemSupports := by
    intro evidence member
    cases evidence with
    | sourceEvidence => simp [demoTopology, demoSystem, CoversMandatoryAt]
    | optionalEvidence => simp at member

def demoMinimumCut :
    MinimumCutCertificate demoTopology .commonCause [.sourceEvidence] where
  supportBundle := demoBundle
  cut := [.host]
  cutValid := by simp [ValidCut, demoTopology]
  breaks := by
    intro evidence member
    cases evidence with
    | sourceEvidence =>
        refine ⟨.host, ?_, ?_⟩
        · simp
        · exact ⟨rfl, rfl, rfl⟩
    | optionalEvidence => simp at member
  minimal := by
    intro candidate candidateValid candidateBreaks
    cases candidate with
    | nil =>
        simp [BreaksBundle, demoTopology] at candidateBreaks
    | cons domain rest =>
        cases domain
        simp [CutCost, demoTopology]

def demoIndependent :
    IndependentAtLeast demoTopology .commonCause [.sourceEvidence] 1 :=
  minimum_cut_meets_requirement demoMinimumCut (by
    change 1 ≤ 1
    exact Nat.le_refl 1)

structure Certificate : Prop where
  positiveIndependent :
    IndependentAtLeast demoTopology .commonCause [.sourceEvidence] 1
  mandatoryFailureBound :
    (demoTopology.evidenceSystem.modelAt demoTopology.context).mandatory
      .commonCause
  admittedSupportEvidence :
    demoTopology.evidenceSystem.AdmittedAt demoTopology.context
      .sourceEvidence
  breakingCutExists :
    ∃ cut,
      ValidCut demoTopology cut ∧
        BreaksBundle demoTopology .commonCause [.sourceEvidence] cut
  emptyBundleRefused :
    ¬ AdmittedSupportBundle demoTopology .commonCause []
  optionalEvidenceRefused :
    ¬ AdmittedSupportBundle demoTopology .commonCause [.optionalEvidence]
  aboveMinimumRefused :
    ¬ IndependentAtLeast demoTopology .commonCause [.sourceEvidence] 2
  unsealedCoverageRefused :
    ¬ CoverageAdmissible demoSystem .current .unsealed [.sourceEvidence]

def certificate : Certificate where
  positiveIndependent := demoIndependent
  mandatoryFailureBound := demoIndependent.1.failureMandatory
  admittedSupportEvidence :=
    independent_bundle_item_is_admitted demoIndependent
      .sourceEvidence (by simp)
  breakingCutExists := independent_has_breaking_cut demoIndependent
  emptyBundleRefused := by
    intro impossible
    exact impossible.nonempty rfl
  optionalEvidenceRefused := by
    intro impossible
    have support := impossible.everyItemSupports .optionalEvidence (by simp)
    have impossibleMember : DemoEvidence.optionalEvidence ∈
        demoTopology.evidenceUniverse := support.1
    simp [demoTopology] at impossibleMember
  aboveMinimumRefused := by
    apply minimum_cut_below_requirement_refutes demoMinimumCut
    change 1 < 2
    decide
  unsealedCoverageRefused := by
    simp [CoverageAdmissible]

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC33Target

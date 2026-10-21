import RCC.ConservativeGrowth

/-!
# RCC-24 Conservative Growth Witnesses

The tests pin the distinction between conservative `TheoryGrowth` and a
revision that changes old semantics.  They also keep address transport,
projection restriction, judgment transport, and obstruction closure
load-bearing.
-/

namespace Residua.RCC.ConservativeGrowth.Tests

open Residua.RCC.ConservativeGrowth

inductive OldObj
  | existing
  deriving DecidableEq

inductive NewObj
  | embedded
  | added
  deriving DecidableEq

inductive Observation
  | oldMeaning
  | changedMeaning
  deriving DecidableEq

inductive Judgment
  | stable
  | rootDependent
  deriving DecidableEq

inductive Address
  | oldAddress
  | migratedAddress
  deriving DecidableEq

inductive Projection
  | oldView
  | changedOldView
  deriving DecidableEq

inductive Obstruction
  | trigger
  deriving DecidableEq

def baseSystem : GrowthSystem where
  OldObject := OldObj
  NewObject := NewObj
  Observation := Observation
  OldJudgment := Judgment
  NewJudgment := Judgment
  Address := Address
  OldProjection := Projection
  NewProjection := Projection
  Obstruction := Obstruction
  embed
    | .existing => .embedded
  embedInjective := by
    intro left right equal
    cases left
    cases right
    rfl
  oldObserve
    | .existing => .oldMeaning
  newObserve
    | .embedded => .oldMeaning
    | .added => .changedMeaning
  transportJudgment := id
  oldValid := fun _ => True
  newValid := fun _ => True
  dependsOnChangedRoot
    | .stable => False
    | .rootDependent => True
  oldAddress := fun _ => .oldAddress
  newAddress
    | .embedded => .oldAddress
    | .added => .migratedAddress
  addressMigrationValid := fun _ oldAddr newAddr =>
    oldAddr = newAddr
  oldProjection := .oldView
  newProjection := .oldView
  restrictProjection := id
  transportObstruction := id
  unresolvedOld := fun _ => True
  unresolvedNew := fun _ => False

def baseCert : TheoryGrowthCert baseSystem .trigger where
  semanticConservative := by intro x; cases x <;> rfl
  judgmentTransport := by
    intro j _ _
    trivial
  addressTransport := by
    intro x
    exact .unchanged (by cases x <;> rfl)
  projectionRestriction := rfl
  obstructionWasUnresolved := trivial
  obstructionClosed := by simp [baseSystem]

example : GrowthKind baseCert = .theoryGrowth := rfl

example :
    ∀ x,
      baseSystem.newObserve (baseSystem.embed x) =
        baseSystem.oldObserve x :=
  baseCert.semanticConservative

example :
    baseSystem.restrictProjection baseSystem.newProjection =
      baseSystem.oldProjection :=
  baseCert.projectionRestriction

example : baseSystem.unresolvedOld .trigger :=
  baseCert.obstructionWasUnresolved

example :
    ¬ baseSystem.unresolvedNew
      (baseSystem.transportObstruction .trigger) :=
  baseCert.obstructionClosed

/-! Same-input mutants: each removes one field required by production. -/

def changedSemanticsSystem : GrowthSystem :=
  { baseSystem with
    newObserve := fun
      | .embedded => .changedMeaning
      | .added => .changedMeaning }

theorem changed_old_semantics_refused :
    ¬ TheoryGrowthCert changedSemanticsSystem .trigger := by
  intro cert
  have h := cert.semanticConservative OldObj.existing
  cases h

def changedProjectionSystem : GrowthSystem :=
  { baseSystem with newProjection := .changedOldView }

theorem failed_projection_restriction_refused :
    ¬ TheoryGrowthCert changedProjectionSystem .trigger := by
  intro cert
  cases cert.projectionRestriction

def untransportedAddressSystem : GrowthSystem :=
  { baseSystem with
    newAddress := fun
      | .embedded => .migratedAddress
      | .added => .migratedAddress }

theorem untransported_address_refused_without_witness :
    ¬ TheoryGrowthCert untransportedAddressSystem .trigger := by
  intro cert
  cases h : cert.addressTransport OldObj.existing with
  | unchanged same =>
      simp [untransportedAddressSystem, baseSystem] at same
  | migrated migration =>
      have collision :
          Address.oldAddress = Address.migratedAddress :=
        migration.oldAddressPinned.symm.trans
          (migration.valid.trans migration.newAddressPinned)
      cases collision

def untouchedObstructionSystem : GrowthSystem :=
  { baseSystem with unresolvedNew := fun _ => True }

theorem untouched_obstruction_refused :
    ¬ TheoryGrowthCert untouchedObstructionSystem .trigger := by
  intro cert
  exact cert.obstructionClosed trivial

def changedRootJudgmentSystem : GrowthSystem :=
  { baseSystem with
    newValid := fun
      | .stable => False
      | .rootDependent => True }

theorem stable_judgment_must_transport :
    ¬ TheoryGrowthCert changedRootJudgmentSystem .trigger := by
  intro cert
  have transported :=
    cert.judgmentTransport Judgment.stable (by simp [changedRootJudgmentSystem, baseSystem])
      trivial
  exact transported

def mislabeledRevision : GrowthProposal changedSemanticsSystem .trigger where
  kind := .theoryRevision

example : ¬ HasTheoryGrowthLabel mislabeledRevision := by
  simp [HasTheoryGrowthLabel, mislabeledRevision]

def falselyLabeledGrowth : GrowthProposal changedSemanticsSystem .trigger where
  kind := .theoryGrowth

example : HasTheoryGrowthLabel falselyLabeledGrowth := rfl

theorem changed_semantics_cannot_cross_growth_admission :
    AdmittedTheoryGrowth changedSemanticsSystem .trigger → False :=
  old_semantic_change_is_not_admitted_growth OldObj.existing (by
    simp [changedSemanticsSystem, baseSystem])

#print axioms TheoryGrowthCert
#print axioms theory_growth_preserves_old_semantics
#print axioms theory_growth_preserves_projection
#print axioms theory_growth_closes_obstruction
#print axioms old_semantic_change_is_not_admitted_growth
#print axioms changed_old_semantics_refused
#print axioms failed_projection_restriction_refused
#print axioms untransported_address_refused_without_witness
#print axioms untouched_obstruction_refused
#print axioms stable_judgment_must_transport
#print axioms changed_semantics_cannot_cross_growth_admission

end Residua.RCC.ConservativeGrowth.Tests


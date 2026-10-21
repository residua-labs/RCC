import RCC.ConservativeGrowth
import RCCTests.ConservativeGrowth

/-!
# RCC-24 target package

This module packages conservative theory growth as an independently buildable
candidate.  The witness keeps old semantics and projections, transports
unaffected valid judgments and addresses, and closes the declared obstruction.
The mutants demonstrate that changed old meaning, changed projection,
untransported addresses, unresolved obstruction, and root-dependent judgment
loss cannot cross the conservative-growth boundary.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC24Target

open Residua.RCC
open Residua.RCC.ConservativeGrowth
open Residua.RCC.ConservativeGrowth.Tests

universe u v w x y z p q r

def baseProposal : GrowthProposal baseSystem .trigger where
  kind := .theoryGrowth

def baseAdmitted : AdmittedTheoryGrowth baseSystem .trigger where
  proposal := baseProposal
  kindExact := rfl
  certificate := baseCert

theorem generic_growth_sound
    {S : GrowthSystem.{u, v, w, x, y, z, p, q, r}}
    {trigger : S.Obstruction}
    (admitted : AdmittedTheoryGrowth S trigger) :
    admitted.proposal.kind = .theoryGrowth ∧
      (∀ old, S.newObserve (S.embed old) = S.oldObserve old) ∧
      (∀ judgment,
        ¬ S.dependsOnChangedRoot judgment →
        S.oldValid judgment →
        S.newValid (S.transportJudgment judgment)) ∧
      (∀ old, AddressTransport S old) ∧
      S.restrictProjection S.newProjection = S.oldProjection ∧
      S.unresolvedOld trigger ∧
      ¬ S.unresolvedNew (S.transportObstruction trigger) :=
  AdmittedTheoryGrowth.sound admitted

structure ConcreteWitness : Prop where
  growthSound :
    baseAdmitted.proposal.kind = .theoryGrowth ∧
      (∀ old, baseSystem.newObserve (baseSystem.embed old) =
        baseSystem.oldObserve old) ∧
      (∀ judgment,
        ¬ baseSystem.dependsOnChangedRoot judgment →
        baseSystem.oldValid judgment →
        baseSystem.newValid (baseSystem.transportJudgment judgment)) ∧
      (∀ old, AddressTransport baseSystem old) ∧
      baseSystem.restrictProjection baseSystem.newProjection =
        baseSystem.oldProjection ∧
      baseSystem.unresolvedOld .trigger ∧
      ¬ baseSystem.unresolvedNew
        (baseSystem.transportObstruction .trigger)
  semanticConservative :
    ∀ old, baseSystem.newObserve (baseSystem.embed old) =
      baseSystem.oldObserve old
  projectionPreserved :
    baseSystem.restrictProjection baseSystem.newProjection =
      baseSystem.oldProjection
  obstructionClosed :
    baseSystem.unresolvedOld .trigger ∧
      ¬ baseSystem.unresolvedNew
        (baseSystem.transportObstruction .trigger)

structure MutantRefusal : Prop where
  changedSemanticsRefused :
    ¬ TheoryGrowthCert changedSemanticsSystem .trigger
  changedProjectionRefused :
    ¬ TheoryGrowthCert changedProjectionSystem .trigger
  untransportedAddressRefused :
    ¬ TheoryGrowthCert untransportedAddressSystem .trigger
  untouchedObstructionRefused :
    ¬ TheoryGrowthCert untouchedObstructionSystem .trigger
  changedRootJudgmentRefused :
    ¬ TheoryGrowthCert changedRootJudgmentSystem .trigger
  mislabeledRevisionRefused :
    ¬ HasTheoryGrowthLabel
      (mislabeledRevision : GrowthProposal changedSemanticsSystem .trigger)

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { growthSound := AdmittedTheoryGrowth.sound baseAdmitted
      semanticConservative := baseCert.semanticConservative
      projectionPreserved := baseCert.projectionRestriction
      obstructionClosed :=
        ⟨baseCert.obstructionWasUnresolved, baseCert.obstructionClosed⟩ }
  mutants :=
    { changedSemanticsRefused := changed_old_semantics_refused
      changedProjectionRefused := failed_projection_restriction_refused
      untransportedAddressRefused :=
        untransported_address_refused_without_witness
      untouchedObstructionRefused := untouched_obstruction_refused
      changedRootJudgmentRefused := stable_judgment_must_transport
      mislabeledRevisionRefused := by
        simp [HasTheoryGrowthLabel, mislabeledRevision] }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC24Target


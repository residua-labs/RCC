import RCCTests.GoalRefinementReepoch
import RCCTests.FormalCoreGoalRefinement

/-!
# RCC-20 target package

This module does not alter the detector registry.  It packages the already
proved generic split/merge laws, the Goal/Work preservation laws, the concrete
semantic split/merge witnesses, and the reepoch bridge into one explicit
candidate certificate.  The package is useful for the exact-head receipt gate:
the target cannot be promoted merely because one isolated theorem happens to
typecheck.

The package deliberately keeps the reverse implication, dependency extraction,
and mandatory-goal waiver outside its scope.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RCC20Target

open Residua.RCC
open Residua.RCC.GoalRefinementTests
open Residua.RCC.GoalRefinementReepochTests

universe u v w

theorem generic_split_sound
    {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics.{u, v, w} S}
    {parent : S.Goal}
    {children : List S.Goal}
    (cert : SplitRefinementCert G parent children)
    (history : G.History)
    (hchildren : GoalsSatisfied G history children) :
    G.satisfied history parent :=
  split_refinement_sound cert history hchildren

theorem generic_merge_sound
    {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics.{u, v, w} S}
    {originals : List S.Goal}
    {replacement : S.Goal}
    (cert : MergeRefinementCert G originals replacement)
    (history : G.History)
    (hreplacement : G.satisfied history replacement) :
    GoalsSatisfied G history originals :=
  merge_refinement_sound cert history hreplacement

theorem generic_split_preserves_parent
    {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics.{u, v, w} S}
    {before after : GoalWorkSnapshot S}
    {parent : S.Goal}
    {children : List S.Goal}
    (registration : SplitRegistration G before after parent children)
    (present : before.goalPresent parent = true)
    (hopen : before.goalStatus parent = .open) :
    after.goalPresent parent = true ∧ after.goalStatus parent = .open :=
  split_parent_not_dropped registration present hopen

theorem generic_merge_preserves_parents
    {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics.{u, v, w} S}
    {before after : GoalWorkSnapshot S}
    {originals : List S.Goal}
    {replacement : S.Goal}
    (registration : MergeRegistration G before after originals replacement)
    (parent : S.Goal)
    (member : parent ∈ originals)
    (present : before.goalPresent parent = true)
    (hopen : before.goalStatus parent = .open) :
    after.goalPresent parent = true ∧ after.goalStatus parent = .open :=
  merge_parent_not_dropped registration parent member present hopen

structure ConcreteWitness : Prop where
  lawfulSplit :
    SplitRefinementCert demoSemantics .hardParent legalChildren
  lawfulMerge :
    MergeRefinementCert demoSemantics oldGoals .hardParent
  splitRegistration :
    SplitRegistration
      demoSemantics openSnapshot openSnapshot .hardParent legalChildren
  mergeRegistration :
    MergeRegistration
      demoSemantics openSnapshot openSnapshot oldGoals .hardParent
  splitParentKept :
    openSnapshot.goalPresent .hardParent = true ∧
      openSnapshot.goalStatus .hardParent = .open
  mergeParentKept :
    openSnapshot.goalPresent .runtimeBound = true ∧
      openSnapshot.goalStatus .runtimeBound = .open
  reepochRefinement :
    SemanticallyRefines Residua.RCC.ReepochTests.demoSystem
      Residua.RCC.ReepochTests.DemoEpoch.base
      Residua.RCC.ReepochTests.DemoEpoch.child
      Residua.RCC.ReepochTests.DemoGoal.debt
      Residua.RCC.ReepochTests.DemoGoal.replacement

structure MutantRefusal : Prop where
  irrelevantSplitRefused :
    ¬ SplitRefinementCert demoSemantics .hardParent irrelevantChildren
  weakMergeRefused :
    ¬ MergeRefinementCert demoSemantics oldGoals .proofSound
  droppedSplitRefused :
    ¬ SplitRegistration
      demoSemantics openSnapshot droppedSplitParentSnapshot
        .hardParent legalChildren
  prematureSplitRefused :
    ¬ SplitRegistration
      demoSemantics openSnapshot prematurelySatisfiedSplitSnapshot
        .hardParent legalChildren
  droppedMergeRefused :
    ¬ MergeRegistration
      demoSemantics openSnapshot droppedMergeParentSnapshot
        oldGoals .hardParent
  prematureMergeRefused :
    ¬ MergeRegistration
      demoSemantics openSnapshot prematurelySatisfiedMergeSnapshot
        oldGoals .hardParent
  edgeOnlyNotUniform :
    ¬ SplitRefinementCert
      counterUniformSemantics
      (.old, .old) [(.new, .replacement)]

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { lawfulSplit := legalSplitCertificate
      lawfulMerge := hardParentMergeCertificate
      splitRegistration := legalSplitRegistration
      mergeRegistration := legalMergeRegistration
      splitParentKept := legal_split_registration_keeps_parent
      mergeParentKept := legal_merge_registration_keeps_runtime_parent
      reepochRefinement := bridge_specializes_uniform_refinement }
  mutants :=
    { irrelevantSplitRefused := irrelevant_children_have_no_split_certificate
      weakMergeRefused := weak_replacement_has_no_merge_certificate
      droppedSplitRefused := dropped_parent_has_no_split_registration
      prematureSplitRefused := prematurely_satisfied_parent_has_no_split_registration
      droppedMergeRefused := dropped_parent_has_no_merge_registration
      prematureMergeRefused := prematurely_satisfied_parent_has_no_merge_registration
      edgeOnlyNotUniform := edge_only_does_not_imply_uniform_refinement }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC20Target


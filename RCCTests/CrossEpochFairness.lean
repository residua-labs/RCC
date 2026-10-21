import RCC.CrossEpochFairness

/-!
# RCC-38 Cross-Epoch Goal Fairness Countermodels

RED-first witnesses for ADR §22.9 and §22.10.  Lawful conservation is a safety
property, not a liveness theorem: a stable mandatory lineage can be carried
forever, remain ready forever, and lose every scheduler decision forever.
-/

open Residua.RCC.CrossEpochFairness

namespace Residua.RCC.CrossEpochFairness.Tests

inductive LineageQ
  | target
  | overtaker
  deriving DecidableEq, Repr

/-! ## CM-FAIR-01: lawful carry starvation -/

def starvationRun (epoch : Nat) : EpochFrame LineageQ where
  goal :=
    { lineageQ := .target
      mandatory := true
      ready := true
      carryAge := epoch }
  selectedLineage := some .overtaker

/-- The mandatory Goal is conserved and its carry age advances at every migration. -/
theorem starvation_run_is_lawfully_carried :
    LawfulLineageRun starvationRun := by
  intro epoch
  constructor
  · constructor <;> rfl
  · intro mandatory ready notSelected
    rfl

/-- The target lineage is continuously mandatory and ready. -/
theorem starvation_run_continuously_ready :
    ContinuouslyReadyMandatory starvationRun .target 0 := by
  intro epoch startBeforeEpoch
  exact ⟨rfl, rfl, rfl⟩

/-- Yet every epoch selects the overtaking lineage, never the target. -/
theorem starvation_run_never_selects_target :
    NeverSelected starvationRun .target 0 := by
  intro epoch startBeforeEpoch
  intro selected
  cases selected

/-- A lawful-carry starvation certificate names the liveness failure explicitly. -/
def lawfulCarryStarvation :
    GoalStarvationWitness starvationRun .target 0 where
  lawfulCarry := starvation_run_is_lawfully_carried
  continuouslyReady := starvation_run_continuously_ready
  neverSelected := starvation_run_never_selects_target

/--
Conservation alone cannot manufacture weak fairness: this run is lawful at
every migration but has no eventual target selection.
-/
theorem lawful_carry_does_not_imply_liveness :
    ¬ WeakFairness starvationRun := by
  intro fair
  exact weak_fairness_excludes_starvation fair lawfulCarryStarvation

/-! ## CM-FAIR-02: migration resets carry age -/

def ageResetRun (_epoch : Nat) : EpochFrame LineageQ where
  goal :=
    { lineageQ := .target
      mandatory := true
      ready := true
      carryAge := 0 }
  selectedLineage := some .overtaker

/-- Resetting age still conserves lineage identity and mandatory membership. -/
theorem age_reset_preserves_only_conservation :
    ∀ epoch,
      CarryConservesGoal (ageResetRun epoch) (ageResetRun (epoch + 1)) := by
  intro epoch
  constructor <;> rfl

/-- It is nevertheless not a lawful carry because an unselected ready Goal aged zero. -/
theorem migration_age_reset_is_rejected :
    ¬ LawfulLineageRun ageResetRun := by
  intro lawful
  have ageStep :=
    (lawful 0).2 rfl rfl (by
      intro selected
      cases selected)
  change (0 : Nat) = 1 at ageStep
  exact (by decide : (0 : Nat) ≠ 1) ageStep

/-! ## CM-FAIR-03: unbounded overtaking -/

/-- Every epoch lawfully selects some work, but it is always the overtaker. -/
theorem unbounded_overtaking_selects_other_work :
    ∀ epoch, (starvationRun epoch).selectedLineage = some .overtaker := by
  intro epoch
  rfl

/-- Busy scheduling is not fair scheduling for the continuously-ready target. -/
theorem unbounded_overtaking_is_not_weak_fair :
    ¬ WeakFairness starvationRun :=
  lawful_carry_does_not_imply_liveness

/-! ## Positive control: an explicit weak-fairness premise yields a witness -/

def fairRun (epoch : Nat) : EpochFrame LineageQ where
  goal :=
    { lineageQ := .target
      mandatory := true
      ready := true
      carryAge := epoch }
  selectedLineage := some .target

theorem fair_run_continuously_ready :
    ContinuouslyReadyMandatory fairRun .target 0 := by
  intro epoch startBeforeEpoch
  exact ⟨rfl, rfl, rfl⟩

theorem fair_run_is_weak_fair :
    WeakFairness fairRun := by
  intro lineage start continuouslyReady
  have lineageIsTarget := (continuouslyReady start (Nat.le_refl start)).1
  refine ⟨start, Nat.le_refl start, lineageIsTarget, ?_⟩
  cases lineageIsTarget
  rfl

/-- The liveness conclusion is an explicit finite epoch witness, not NF termination. -/
theorem weak_fairness_produces_eventual_selection :
    EventuallySelected fairRun .target 0 := by
  exact weak_fairness_eventually_selects
    fair_run_is_weak_fair fair_run_continuously_ready

#print axioms lawful_carry_does_not_imply_liveness
#print axioms migration_age_reset_is_rejected
#print axioms unbounded_overtaking_is_not_weak_fair
#print axioms weak_fairness_produces_eventual_selection

end Residua.RCC.CrossEpochFairness.Tests

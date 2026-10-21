import Init

/-!
# RCC-38 Cross-Epoch Goal Fairness

Lawful migration is a safety property.  It can conserve a mandatory Goal,
preserve its stable lineage identity, and advance its carry age forever without
ever selecting it.  Liveness therefore requires an explicit fairness premise.

An institution run is represented extensionally as `Nat → EpochFrame`; this is
the open-lineage boundary, not a finite normalizer execution.  Weak fairness
supplies a finite existential selection witness for every continuously-ready
mandatory lineage.  The theorem does not manufacture that premise from
conservation.

Prelude-only Lean 4.14; no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.CrossEpochFairness

universe u

/-- The tracked mandatory Goal at one epoch. -/
structure GoalEpochState (LineageQ : Type u) where
  lineageQ : LineageQ
  mandatory : Bool
  ready : Bool
  carryAge : Nat

/--
One epoch frame records the tracked Goal and the lineage selected by the
scheduler.  Selecting unrelated work does not select the tracked Goal.
-/
structure EpochFrame (LineageQ : Type u) where
  goal : GoalEpochState LineageQ
  selectedLineage : Option LineageQ

/-- The scheduler selected the tracked Goal's stable lineage in this frame. -/
def GoalSelected {LineageQ : Type u} (frame : EpochFrame LineageQ) : Prop :=
  frame.selectedLineage = some frame.goal.lineageQ

/-- Migration conserves the Goal's stable lineage and mandatory membership. -/
def CarryConservesGoal {LineageQ : Type u}
    (current next : EpochFrame LineageQ) : Prop :=
  next.goal.lineageQ = current.goal.lineageQ ∧
    next.goal.mandatory = current.goal.mandatory

/--
A lawful carry also advances age exactly once whenever the mandatory Goal is
ready and was not selected.  Hence a reepoch cannot reset the age of a
continuously-ready starved Goal.
-/
def LawfulCarry {LineageQ : Type u}
    (current next : EpochFrame LineageQ) : Prop :=
  CarryConservesGoal current next ∧
    (current.goal.mandatory = true →
      current.goal.ready = true →
      ¬ GoalSelected current →
      next.goal.carryAge = current.goal.carryAge + 1)

/-- Every successor pair in the open lineage is a lawful carry. -/
def LawfulLineageRun {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Prop :=
  ∀ epoch, LawfulCarry (run epoch) (run (epoch + 1))

/--
The same mandatory lineage remains ready at every epoch from `start` onward.
-/
def ContinuouslyReadyMandatory {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∀ epoch, start ≤ epoch →
    (run epoch).goal.lineageQ = lineage ∧
      (run epoch).goal.mandatory = true ∧
      (run epoch).goal.ready = true

/-- The target lineage is never selected from `start` onward. -/
def NeverSelected {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∀ epoch, start ≤ epoch →
    ¬ (run epoch).selectedLineage = some lineage

/--
An explicit finite witness exists for eventual selection.  This is the
liveness conclusion; it is not a claim that an epoch normalizer ran forever.
-/
def EventuallySelected {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∃ epoch,
    start ≤ epoch ∧
      (run epoch).goal.lineageQ = lineage ∧
      (run epoch).selectedLineage = some lineage

/--
Weak fairness is an explicit temporal premise: every continuously-ready
mandatory lineage has a finite selection witness.
-/
def WeakFairness {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Prop :=
  ∀ lineage start,
    ContinuouslyReadyMandatory run lineage start →
    EventuallySelected run lineage start

/--
A named certificate for the safety/liveness gap: every carry is lawful and the
mandatory Goal stays ready, but it is never selected.
-/
structure GoalStarvationWitness {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop where
  lawfulCarry : LawfulLineageRun run
  continuouslyReady : ContinuouslyReadyMandatory run lineage start
  neverSelected : NeverSelected run lineage start

/-- Weak fairness produces the promised finite eventual-selection witness. -/
theorem weak_fairness_eventually_selects
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    {lineage : LineageQ} {start : Nat}
    (fair : WeakFairness run)
    (ready : ContinuouslyReadyMandatory run lineage start) :
    EventuallySelected run lineage start :=
  fair lineage start ready

/-- A weak-fair run cannot also carry a starvation witness for that lineage. -/
theorem weak_fairness_excludes_starvation
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    {lineage : LineageQ} {start : Nat}
    (fair : WeakFairness run)
    (starved : GoalStarvationWitness run lineage start) :
    False := by
  have selected :=
    weak_fairness_eventually_selects fair starved.continuouslyReady
  obtain ⟨epoch, afterStart, lineageStable, selectedTarget⟩ := selected
  exact starved.neverSelected epoch afterStart selectedTarget

/--
The safety half of RCC-38: a lawful ready/unselected carry strictly advances
age, so migration cannot reset the carried Goal's waiting history.
-/
theorem lawful_ready_carry_strictly_increases_age
    {LineageQ : Type u}
    {current next : EpochFrame LineageQ}
    (lawful : LawfulCarry current next)
    (mandatory : current.goal.mandatory = true)
    (ready : current.goal.ready = true)
    (notSelected : ¬ GoalSelected current) :
    current.goal.carryAge < next.goal.carryAge := by
  rw [lawful.2 mandatory ready notSelected]
  exact Nat.lt_succ_self current.goal.carryAge

end Residua.RCC.CrossEpochFairness

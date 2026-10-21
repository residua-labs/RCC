import Init

/-!
# RCC-38 Cross-Epoch Goal Fairness

Lawful migration is a safety property.  It can conserve every mandatory Goal,
preserve stable lineage identity, and monotonically advance carry age forever
without selecting one continuously-ready Goal.  Liveness therefore requires an
explicit scheduling premise.

The model exposes the whole active Goal universe at each epoch.  A selected
lineage must be present, mandatory, and ready; an unrelated tag is not a lawful
preemption witness.  Every carried mandatory Goal preserves age, including
blocked and selected Goals.  A ready unselected Goal advances strictly.

Weak fairness remains a conditional temporal theorem over an open `Nat`-indexed
lineage.  It is not derived from finite epoch normalization or conservation.

Prelude-only Lean 4.14; no Mathlib, no custom axioms.
-/

namespace Residua.RCC.CrossEpochFairness94

universe u

/-- Workflow facts for one active Goal lineage in one epoch. -/
structure GoalLocalState where
  mandatory : Bool
  ready : Bool
  carryAge : Nat
  deriving DecidableEq, Repr

/--
One epoch frame exposes every active Goal and the scheduler's optional choice.
The function representation is intentionally extensional: concrete instances
must separately seal the finite Goal universe they claim to have extracted.
-/
structure EpochFrame (LineageQ : Type u) where
  goals : LineageQ → Option GoalLocalState
  selectedLineage : Option LineageQ

/-- The frame contains the given active Goal state. -/
def GoalAt {LineageQ : Type u}
    (frame : EpochFrame LineageQ)
    (lineage : LineageQ) (state : GoalLocalState) : Prop :=
  frame.goals lineage = some state

/-- The lineage is present, mandatory, and ready in this frame. -/
def MandatoryReady {LineageQ : Type u}
    (frame : EpochFrame LineageQ) (lineage : LineageQ) : Prop :=
  ∃ state,
    GoalAt frame lineage state ∧
      state.mandatory = true ∧
      state.ready = true

/-- The scheduler selected this exact stable lineage. -/
def GoalSelected {LineageQ : Type u}
    (frame : EpochFrame LineageQ) (lineage : LineageQ) : Prop :=
  frame.selectedLineage = some lineage

/-- A scheduler may select only a present mandatory ready Goal. -/
def SelectionLegal {LineageQ : Type u}
    (frame : EpochFrame LineageQ) : Prop :=
  ∀ lineage, GoalSelected frame lineage → MandatoryReady frame lineage

/--
Proof-carrying migration witness for one mandatory Goal.  Stable lineage
identity is represented by lookup under the same `lineage` key.  Age is
monotone for every carried mandatory Goal, not only for currently-ready ones.
If the Goal is ready and unselected, age advances strictly.
-/
def MandatoryCarryWitness {LineageQ : Type u}
    (current next : EpochFrame LineageQ)
    (lineage : LineageQ) (oldState : GoalLocalState) : Prop :=
  ∃ newState,
    GoalAt next lineage newState ∧
      newState.mandatory = true ∧
      oldState.carryAge ≤ newState.carryAge ∧
      (oldState.ready = true →
        ¬ GoalSelected current lineage →
        oldState.carryAge < newState.carryAge)

/--
A lawful epoch edge has a lawful selection and carries every old mandatory Goal
under the same lineage key with monotone age.
-/
def LawfulCarry {LineageQ : Type u}
    (current next : EpochFrame LineageQ) : Prop :=
  SelectionLegal current ∧
    ∀ lineage oldState,
      GoalAt current lineage oldState →
      oldState.mandatory = true →
      MandatoryCarryWitness current next lineage oldState

/-- Every adjacent pair in the open lineage is a lawful carry. -/
def LawfulLineageRun {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Prop :=
  ∀ epoch, LawfulCarry (run epoch) (run (epoch + 1))

/-- The same mandatory lineage remains ready from `start` onward. -/
def ContinuouslyReadyMandatory {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∀ epoch, start ≤ epoch → MandatoryReady (run epoch) lineage

/-- The target lineage is never selected from `start` onward. -/
def NeverSelected {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∀ epoch, start ≤ epoch → ¬ GoalSelected (run epoch) lineage

/-- A finite witness exists for eventual selection. -/
def EventuallySelected {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop :=
  ∃ epoch, start ≤ epoch ∧ GoalSelected (run epoch) lineage

/--
Weak fairness is an explicit temporal premise: every continuously-ready
mandatory lineage has a finite selection witness.
-/
def WeakFairness {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Prop :=
  ∀ lineage start,
    ContinuouslyReadyMandatory run lineage start →
    EventuallySelected run lineage start

/-- A named safety/liveness-gap certificate. -/
structure GoalStarvationWitness {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start : Nat) : Prop where
  lawfulCarry : LawfulLineageRun run
  continuouslyReady : ContinuouslyReadyMandatory run lineage start
  neverSelected : NeverSelected run lineage start

/-- A lawful selection is always a real, mandatory, ready Goal. -/
theorem lawful_selection_is_present_ready_mandatory
    {LineageQ : Type u}
    {current next : EpochFrame LineageQ}
    (lawful : LawfulCarry current next)
    {lineage : LineageQ}
    (selected : GoalSelected current lineage) :
    MandatoryReady current lineage :=
  lawful.1 lineage selected

/-- Every carried mandatory Goal keeps a monotone age across migration. -/
theorem lawful_carry_age_monotone
    {LineageQ : Type u}
    {current next : EpochFrame LineageQ}
    (lawful : LawfulCarry current next)
    {lineage : LineageQ} {oldState : GoalLocalState}
    (present : GoalAt current lineage oldState)
    (mandatory : oldState.mandatory = true) :
    ∃ newState,
      GoalAt next lineage newState ∧
        oldState.carryAge ≤ newState.carryAge := by
  obtain ⟨newState, nextPresent, mandatoryPreserved, ageMonotone, waiting⟩ :=
    lawful.2 lineage oldState present mandatory
  exact ⟨newState, nextPresent, ageMonotone⟩

/-- No lawful migration may reset the age of a carried mandatory Goal. -/
theorem migration_cannot_reset_age
    {LineageQ : Type u}
    {current next : EpochFrame LineageQ}
    (lawful : LawfulCarry current next)
    {lineage : LineageQ} {oldState newState : GoalLocalState}
    (oldPresent : GoalAt current lineage oldState)
    (mandatory : oldState.mandatory = true)
    (newPresent : GoalAt next lineage newState) :
    ¬ newState.carryAge < oldState.carryAge := by
  obtain ⟨carried, carriedPresent, ageMonotone⟩ :=
    lawful_carry_age_monotone lawful oldPresent mandatory
  have sameState : carried = newState :=
    Option.some.inj (carriedPresent.symm.trans newPresent)
  subst newState
  exact Nat.not_lt_of_ge ageMonotone

/-- A ready unselected mandatory Goal strictly advances age. -/
theorem lawful_ready_carry_strictly_increases_age
    {LineageQ : Type u}
    {current next : EpochFrame LineageQ}
    (lawful : LawfulCarry current next)
    {lineage : LineageQ} {oldState : GoalLocalState}
    (present : GoalAt current lineage oldState)
    (mandatory : oldState.mandatory = true)
    (ready : oldState.ready = true)
    (notSelected : ¬ GoalSelected current lineage) :
    ∃ newState,
      GoalAt next lineage newState ∧
        oldState.carryAge < newState.carryAge := by
  obtain ⟨newState, nextPresent, mandatoryPreserved, ageMonotone, waiting⟩ :=
    lawful.2 lineage oldState present mandatory
  exact ⟨newState, nextPresent, waiting ready notSelected⟩

/-- Weak fairness produces the promised finite selection witness. -/
theorem weak_fairness_eventually_selects
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    {lineage : LineageQ} {start : Nat}
    (fair : WeakFairness run)
    (ready : ContinuouslyReadyMandatory run lineage start) :
    EventuallySelected run lineage start :=
  fair lineage start ready

/-- A weak-fair run cannot carry a starvation witness for that lineage. -/
theorem weak_fairness_excludes_starvation
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    {lineage : LineageQ} {start : Nat}
    (fair : WeakFairness run)
    (starved : GoalStarvationWitness run lineage start) :
    False := by
  obtain ⟨epoch, afterStart, selected⟩ :=
    weak_fairness_eventually_selects fair starved.continuouslyReady
  exact starved.neverSelected epoch afterStart selected

/-! ## Proof-carrying preemption disciplines -/

/-- Selection occurs within `bound` epochs of the ready interval's start. -/
def SelectedWithin {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ)
    (lineage : LineageQ) (start bound : Nat) : Prop :=
  ∃ epoch,
    start ≤ epoch ∧
      epoch ≤ start + bound ∧
      GoalSelected (run epoch) lineage

/-- No continuously-ready mandatory Goal can be overtaken beyond a finite bound. -/
def BoundedOvertaking {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) (bound : Nat) : Prop :=
  ∀ lineage start,
    ContinuouslyReadyMandatory run lineage start →
    SelectedWithin run lineage start bound

/-- Every quota window contains a selection of the continuously-ready Goal. -/
def QuotaDiscipline {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) (window : Nat) : Prop :=
  0 < window ∧
    ∀ lineage start,
      ContinuouslyReadyMandatory run lineage start →
      ∃ offset,
        offset < window ∧
          GoalSelected (run (start + offset)) lineage

/--
A sealed campaign names the exact finite lineage set that may become mandatory
and supplies a service witness for every continuously-ready member.  The
service field is load-bearing: merely blocking new external work does not
prevent one incumbent from starving another.
-/
structure CampaignIsolation {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) where
  sealedLineages : List LineageQ
  lawfulCarry : LawfulLineageRun run
  universeSealed :
    ∀ lineage epoch,
      MandatoryReady (run epoch) lineage →
      List.Mem lineage sealedLineages
  service :
    ∀ lineage,
      List.Mem lineage sealedLineages →
      ∀ start,
        ContinuouslyReadyMandatory run lineage start →
        EventuallySelected run lineage start

/--
An aging policy must select a mandatory ready Goal after its monotone carry age
reaches the admitted threshold.
-/
def AgingDiscipline {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) (threshold : Nat) : Prop :=
  ∀ lineage epoch state,
    GoalAt (run epoch) lineage state →
    state.mandatory = true →
    state.ready = true →
    threshold ≤ state.carryAge →
    GoalSelected (run epoch) lineage

/-- A bounded-overtaking certificate directly entails weak fairness. -/
theorem bounded_overtaking_implies_weak_fairness
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ} {bound : Nat}
    (bounded : BoundedOvertaking run bound) :
    WeakFairness run := by
  intro lineage start ready
  obtain ⟨epoch, afterStart, beforeBound, selected⟩ :=
    bounded lineage start ready
  exact ⟨epoch, afterStart, selected⟩

/-- A positive quota gives a finite witness and therefore weak fairness. -/
theorem quota_implies_weak_fairness
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ} {window : Nat}
    (quota : QuotaDiscipline run window) :
    WeakFairness run := by
  intro lineage start ready
  obtain ⟨offset, insideWindow, selected⟩ := quota.2 lineage start ready
  exact ⟨start + offset, Nat.le_add_right start offset, selected⟩

/-- Exact sealed membership plus internal service entails weak fairness. -/
theorem campaign_isolation_implies_weak_fairness
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    (isolated : CampaignIsolation run) :
    WeakFairness run := by
  intro lineage start ready
  have member :=
    isolated.universeSealed lineage start
      (ready start (Nat.le_refl start))
  exact isolated.service lineage member start ready

/--
After `steps` lawful unselected carries, either the Goal was selected within the
finite prefix or its age is at least `steps`.
-/
theorem selected_within_or_age_at_least
    {LineageQ : Type u} [DecidableEq LineageQ]
    {run : Nat → EpochFrame LineageQ}
    {lineage : LineageQ} {start : Nat}
    (lawful : LawfulLineageRun run)
    (ready : ContinuouslyReadyMandatory run lineage start) :
    ∀ steps,
      SelectedWithin run lineage start steps ∨
        ∃ state,
          GoalAt (run (start + steps)) lineage state ∧
            steps ≤ state.carryAge := by
  intro steps
  induction steps with
  | zero =>
      right
      obtain ⟨state, present, mandatory, isReady⟩ :=
        ready start (Nat.le_refl start)
      exact ⟨state, by simpa using present, Nat.zero_le state.carryAge⟩
  | succ steps ih =>
      cases ih with
      | inl selected =>
          left
          obtain ⟨epoch, afterStart, beforeBound, chosen⟩ := selected
          exact
            ⟨epoch, afterStart,
              Nat.le_trans beforeBound
                (Nat.add_le_add_left (Nat.le_succ steps) start),
              chosen⟩
      | inr aged =>
          obtain ⟨state, present, ageLower⟩ := aged
          by_cases selectedNow :
              GoalSelected (run (start + steps)) lineage
          · left
            exact
              ⟨start + steps, Nat.le_add_right start steps,
                Nat.add_le_add_left (Nat.le_succ steps) start,
                selectedNow⟩
          · right
            obtain ⟨readyState, readyPresent, mandatory, isReady⟩ :=
              ready (start + steps) (Nat.le_add_right start steps)
            have sameState : state = readyState :=
              Option.some.inj (present.symm.trans readyPresent)
            subst readyState
            obtain ⟨nextState, nextPresent, ageStrict⟩ :=
              lawful_ready_carry_strictly_increases_age
                (lawful (start + steps)) present mandatory isReady selectedNow
            refine ⟨nextState, ?_, ?_⟩
            · simpa [Nat.add_assoc] using nextPresent
            · exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt ageLower ageStrict)

/-- A lawful monotone-aging run with a threshold policy is weak-fair. -/
theorem aging_implies_weak_fairness
    {LineageQ : Type u} [DecidableEq LineageQ]
    {run : Nat → EpochFrame LineageQ} {threshold : Nat}
    (lawful : LawfulLineageRun run)
    (aging : AgingDiscipline run threshold) :
    WeakFairness run := by
  intro lineage start ready
  cases selected_within_or_age_at_least lawful ready threshold with
  | inl selected =>
      obtain ⟨epoch, afterStart, beforeBound, chosen⟩ := selected
      exact ⟨epoch, afterStart, chosen⟩
  | inr aged =>
      obtain ⟨state, present, ageReached⟩ := aged
      obtain ⟨readyState, readyPresent, mandatory, isReady⟩ :=
        ready (start + threshold) (Nat.le_add_right start threshold)
      have sameState : state = readyState :=
        Option.some.inj (present.symm.trans readyPresent)
      subst readyState
      exact
        ⟨start + threshold, Nat.le_add_right start threshold,
          aging lineage (start + threshold) state
            present mandatory isReady ageReached⟩

/--
The four admitted ways of controlling priority preemption.  Constructors carry
the actual law; a bare policy tag cannot establish fairness.
-/
inductive PreemptionDiscipline {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Type u where
  | bounded
      (bound : Nat)
      (certificate : BoundedOvertaking run bound)
  | aging
      (decidableEq : DecidableEq LineageQ)
      (threshold : Nat)
      (lawful : LawfulLineageRun run)
      (certificate : AgingDiscipline run threshold)
  | quota
      (window : Nat)
      (certificate : QuotaDiscipline run window)
  | campaignIsolation
      (certificate : CampaignIsolation run)

/-- Every admitted preemption discipline entails the same weak-fairness law. -/
theorem preemption_discipline_implies_weak_fairness
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    (discipline : PreemptionDiscipline run) :
    WeakFairness run := by
  cases discipline with
  | bounded bound certificate =>
      exact bounded_overtaking_implies_weak_fairness certificate
  | aging decidableEq threshold lawful certificate =>
      exact @aging_implies_weak_fairness _ decidableEq _ _ lawful certificate
  | quota window certificate =>
      exact quota_implies_weak_fairness certificate
  | campaignIsolation certificate =>
      exact campaign_isolation_implies_weak_fairness certificate

/--
Relational bridge from the scheduler projection to receipts admitted at the
canonical history head.  The production RCC instance supplies the concrete
receipt type and its history/admission predicate; a naked selected-lineage field
is insufficient for a closure-facing scheduling contract.
-/
structure SelectionBinding {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) where
  Receipt : Type u
  receiptEpoch : Receipt → Nat
  receiptLineage : Receipt → LineageQ
  admittedAtCanonicalHead : Receipt → Prop
  grounded :
    ∀ epoch lineage,
      GoalSelected (run epoch) lineage →
      ∃ receipt,
        receiptEpoch receipt = epoch ∧
          receiptLineage receipt = lineage ∧
          admittedAtCanonicalHead receipt

/--
Priority policy is proof carrying.  The enabled branch cannot be constructed
from a self-reported Boolean; it contains one admitted fairness discipline.
-/
inductive PreemptionPolicy {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Type u where
  | forbidden (fair : WeakFairness run)
  | enabled (discipline : PreemptionDiscipline run)

/--
Epoch scheduling must be a lawful lineage run, ground every nominal selection
in an admitted canonical-head receipt, and either forbid priority preemption
with a fairness proof or enable it with a proof-carrying discipline.
-/
structure SchedulingContract {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) where
  lawfulCarry : LawfulLineageRun run
  selectionBinding : SelectionBinding run
  preemptionPolicy : PreemptionPolicy run

/-- Every well-formed scheduling contract supplies weak fairness. -/
theorem scheduling_contract_implies_weak_fairness
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    (contract : SchedulingContract run) :
    WeakFairness run := by
  cases contract.preemptionPolicy with
  | forbidden fair => exact fair
  | enabled discipline =>
      exact preemption_discipline_implies_weak_fairness discipline

/-- Every scheduler selection in a contract has an admitted receipt witness. -/
theorem scheduling_selection_is_grounded
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    (contract : SchedulingContract run)
    {epoch : Nat} {lineage : LineageQ}
    (selected : GoalSelected (run epoch) lineage) :
    ∃ receipt,
      contract.selectionBinding.receiptEpoch receipt = epoch ∧
        contract.selectionBinding.receiptLineage receipt = lineage ∧
        contract.selectionBinding.admittedAtCanonicalHead receipt :=
  contract.selectionBinding.grounded epoch lineage selected

/-! ## Named liveness residues; no total decision over infinite runs is claimed. -/

/-- A concrete age-reset counterexample on one migration edge. -/
structure MigrationAgeResetWitness {LineageQ : Type u}
    (current next : EpochFrame LineageQ) where
  lineage : LineageQ
  oldState : GoalLocalState
  newState : GoalLocalState
  oldPresent : GoalAt current lineage oldState
  newPresent : GoalAt next lineage newState
  mandatory : oldState.mandatory = true
  reset : newState.carryAge < oldState.carryAge

/-- Typed explanations for a lineage-liveness failure or missing proof. -/
inductive LineageLivenessResidue {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) where
  | goalStarved
      {lineage : LineageQ} {start : Nat}
      (witness : GoalStarvationWitness run lineage start)
  | migrationResetsGoalAge
      {epoch : Nat}
      (witness : MigrationAgeResetWitness (run epoch) (run (epoch + 1)))
  | priorityOvertakingUnbounded
      (witness : ∀ bound, ¬ BoundedOvertaking run bound)
  | lineageFairnessEvidenceGap
      {lineage : LineageQ} {start : Nat}
      (ready : ContinuouslyReadyMandatory run lineage start)

/-- Supplied audit result; no total decision over an infinite run is inferred. -/
inductive LineageFairnessEvidence {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) : Type u where
  | certified (fair : WeakFairness run)
  | namedFailure (residue : LineageLivenessResidue run)

/--
Coverage is an explicit instance/finite-campaign obligation over a lawful,
receipt-grounded lineage run.  It cannot be constructed from "no counterexample
found".  Adequacy of the upstream source/Intent projection remains the RCC
source-window and Intent-coverage obligation; an extensionally empty run is
fair only for an actually empty admitted Goal scope.
-/
structure LineageFairnessCoverage {LineageQ : Type u}
    (run : Nat → EpochFrame LineageQ) where
  lawfulCarry : LawfulLineageRun run
  selectionBinding : SelectionBinding run
  evidence : LineageFairnessEvidence run

/-- Covered lineage audits yield either a fairness theorem or a named residue. -/
theorem coverage_yields_fairness_or_named_residue
    {LineageQ : Type u}
    {run : Nat → EpochFrame LineageQ}
    (coverage : LineageFairnessCoverage run) :
    WeakFairness run ∨ Nonempty (LineageLivenessResidue run) := by
  cases coverage.evidence with
  | certified fair =>
      exact Or.inl fair
  | namedFailure residue =>
      exact Or.inr ⟨residue⟩

end Residua.RCC.CrossEpochFairness94


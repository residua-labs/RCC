/-!
# RCC-19 Intent / Goal Non-Vacuity Kernel

Every goal-adequacy constructor carries the semantic evidence named by ADR §20.1.
Countermodels contain a lawful negative history rejected by the real verifier;
mutant divergence contains a tautological claim plus a forged certificate accepted
only by the mutant; explicit triviality contains a proof that the lawful claim is
indeed tautological.

Intent adequacy requires a mandatory load-bearing goal unless policy explicitly
admits the entire intent is trivial. Critical closure always requires a load-bearing
critical goal, so `explicitlyTrivial` never contributes critical closure strength.

This module does not discover mandatory goals, judge policy, bind a runtime verifier,
or close RCC globally. Prelude-only Lean 4.14; no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC

universe u v w

/-- The exact three evidence classes admitted by ADR §20.1. -/
inductive LoadBearingEvidence where
  | countermodel
  | mutantDivergence
  | explicitlyTrivial
  deriving DecidableEq, Repr

namespace LoadBearingEvidence

/--
Only semantic countermodels and real/mutant verifier divergence contribute closure
strength. A declared structural tautology is evidence, but is not load-bearing.
-/
def IsLoadBearing (evidence : LoadBearingEvidence) : Prop :=
  evidence ≠ .explicitlyTrivial

end LoadBearingEvidence

/-- Semantic claim and real/mutant verifier surface for one goal. -/
structure GoalContract where
  History : Type u
  Certificate : Type v
  lawful : History → Prop
  claim : History → Prop
  verify : History → Certificate → Bool
  mutantVerify : History → Certificate → Bool

/--
Proof-carrying goal adequacy. Constructor payloads prevent a mere evidence label from
turning a vacuous claim or an always-accepting verifier into load-bearing evidence.
-/
inductive GoalAdequacy (goal : GoalContract.{u, v}) where
  | countermodel
      (history : goal.History)
      (forgedCertificate : goal.Certificate)
      (lawfulHistory : goal.lawful history)
      (claimRefuted : ¬ goal.claim history)
      (realRejects : goal.verify history forgedCertificate = false)
  | mutantDivergence
      (history : goal.History)
      (forgedCertificate : goal.Certificate)
      (lawfulHistory : goal.lawful history)
      (claimTautological :
        ∀ candidate, goal.lawful candidate → goal.claim candidate)
      (mutantAccepts : goal.mutantVerify history forgedCertificate = true)
      (realRejects : goal.verify history forgedCertificate = false)
  | explicitlyTrivial
      (claimTautological :
        ∀ history, goal.lawful history → goal.claim history)

namespace GoalAdequacy

/-- Erase a dependent witness to its exact ADR evidence class. -/
def evidence {goal : GoalContract.{u, v}} :
    GoalAdequacy goal → LoadBearingEvidence
  | .countermodel .. => .countermodel
  | .mutantDivergence .. => .mutantDivergence
  | .explicitlyTrivial .. => .explicitlyTrivial

end GoalAdequacy

/-- Policy has one explicit exception; silence never means that an intent is trivial. -/
inductive IntentTrivialityPolicy where
  | requireLoadBearing
  | explicitlyAdmitEntireIntentTrivial
  deriving DecidableEq, Repr

/--
Intent decomposition with a proof-carrying adequacy witness for every declared goal.
Mandatory and critical lists are separate because not every mandatory structural goal
contributes critical closure strength.
-/
structure IntentProfile where
  Goal : Type u
  contract : Goal → GoalContract.{v, w}
  mandatoryGoals : List Goal
  criticalGoals : List Goal
  adequacy : (goal : Goal) → GoalAdequacy (contract goal)
  policy : IntentTrivialityPolicy

/-- At least one selected goal carries evidence that is not explicit triviality. -/
def HasLoadBearingGoal (intent : IntentProfile.{u, v, w})
    (goals : List intent.Goal) : Prop :=
  ∃ goal, goal ∈ goals ∧
    (intent.adequacy goal).evidence.IsLoadBearing

/--
Nontrivial policy requires a load-bearing mandatory goal. The only exception is the
named policy constructor that explicitly admits the whole intent is trivial.
-/
def IntentAdequate (intent : IntentProfile.{u, v, w}) : Prop :=
  intent.policy = .explicitlyAdmitEntireIntentTrivial ∨
    HasLoadBearingGoal intent intent.mandatoryGoals

/--
Critical closure is never inferred from policy triviality: a critical list must contain
an actually load-bearing witness.
-/
def CriticalClosureAdequate (intent : IntentProfile.{u, v, w}) : Prop :=
  HasLoadBearingGoal intent intent.criticalGoals

/-- Both intent decomposition and the claimed critical closure must be non-vacuous. -/
def ClosureAdequate (intent : IntentProfile.{u, v, w}) : Prop :=
  IntentAdequate intent ∧ CriticalClosureAdequate intent

/-- Under nontrivial policy, intent adequacy exposes a mandatory load-bearing witness. -/
theorem intent_adequate_requires_load_bearing_mandatory
    (intent : IntentProfile.{u, v, w})
    (hpolicy : intent.policy = .requireLoadBearing)
    (hadequate : IntentAdequate intent) :
    HasLoadBearingGoal intent intent.mandatoryGoals := by
  rcases hadequate with htrivial | hload
  · rw [hpolicy] at htrivial
    cases htrivial
  · exact hload

/-- A mandatory load-bearing witness makes the mandatory-goal list nonempty. -/
theorem intent_adequate_requires_nonempty_mandatory
    (intent : IntentProfile.{u, v, w})
    (hpolicy : intent.policy = .requireLoadBearing)
    (hadequate : IntentAdequate intent) :
    intent.mandatoryGoals ≠ [] := by
  intro hempty
  have hload :=
    intent_adequate_requires_load_bearing_mandatory intent hpolicy hadequate
  rcases hload with ⟨goal, hmem, _⟩
  rw [hempty] at hmem
  cases hmem

/--
RCC-19 headline: lawful critical closure under nontrivial policy returns a nonempty
mandatory set plus distinct mandatory and critical load-bearing witnesses.
-/
theorem rcc19_intent_goal_nonvacuity
    (intent : IntentProfile.{u, v, w})
    (hpolicy : intent.policy = .requireLoadBearing)
    (hclosure : ClosureAdequate intent) :
    intent.mandatoryGoals ≠ [] ∧
      HasLoadBearingGoal intent intent.mandatoryGoals ∧
      HasLoadBearingGoal intent intent.criticalGoals := by
  constructor
  · exact intent_adequate_requires_nonempty_mandatory intent hpolicy hclosure.1
  · constructor
    · exact intent_adequate_requires_load_bearing_mandatory
        intent hpolicy hclosure.1
    · exact hclosure.2

end Residua.RCC

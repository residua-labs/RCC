import RCC.GoalAdequacy

/-!
# RCC-19 Intent / Goal Non-Vacuity Witnesses

RED-first tests for load-bearing goal evidence. The breakages caught here are:

* accepting an empty mandatory-goal set because universal satisfaction is vacuous;
* accepting `Claim := True` plus a forged verifier success as a critical goal;
* counting an all-`explicitlyTrivial` critical intent as nontrivial closure;
* weakening the RCC-19 theorem so it no longer returns both mandatory and critical
  load-bearing witnesses.

The test module exercises the real dependent evidence constructors and closure predicates.
It does not inspect source text or mock a verifier.
-/

open Residua.RCC

namespace Residua.RCC.GoalAdequacyTests

/-! ## Exact evidence surface and positive controls -/

/--
The evidence carrier is pinned to exactly the three ADR §20.1 cases. Adding an
unreviewed fourth escape hatch leaves a case open.
-/
theorem load_bearing_evidence_exactly_three (evidence : LoadBearingEvidence) :
    evidence = .countermodel ∨
      evidence = .mutantDivergence ∨
      evidence = .explicitlyTrivial := by
  cases evidence <;> simp

/-- A safety claim with a lawful negative history and a rejecting real verifier. -/
def safetyGoal : GoalContract where
  History := Bool
  Certificate := Unit
  lawful := fun _ => True
  claim := fun history => history = true
  verify := fun history _ => history
  mutantVerify := fun _ _ => true

/-- Semantic countermodel evidence: the false history refutes the claim and is rejected. -/
def safetyCountermodel : GoalAdequacy safetyGoal :=
  .countermodel false () trivial (by simp [safetyGoal]) rfl

/--
A mathematical tautology whose real verifier still has teeth against a forged
certificate, while the deliberately weakened verifier accepts it.
-/
def tautologyWithTeeth : GoalContract where
  History := Unit
  Certificate := Bool
  lawful := fun _ => True
  claim := fun _ => True
  verify := fun _ certificate => certificate
  mutantVerify := fun _ _ => true

/-- Mutant divergence is load-bearing even though the mathematical claim is a tautology. -/
def tautologyMutantDivergence : GoalAdequacy tautologyWithTeeth :=
  .mutantDivergence () false trivial (fun _ _ => trivial) rfl rfl

/-- A declared structural tautology with no negative or mutant-divergence witness. -/
def structuralGoal : GoalContract where
  History := Unit
  Certificate := Unit
  lawful := fun _ => True
  claim := fun _ => True
  verify := fun _ _ => true
  mutantVerify := fun _ _ => true

def structuralTriviality : GoalAdequacy structuralGoal :=
  .explicitlyTrivial (fun _ _ => trivial)

inductive DemoGoal
  | safety
  | tautologyWithTeeth
  | structural
  deriving DecidableEq

def demoContract : DemoGoal → GoalContract
  | .safety => safetyGoal
  | .tautologyWithTeeth => tautologyWithTeeth
  | .structural => structuralGoal

def demoAdequacy : (goal : DemoGoal) → GoalAdequacy (demoContract goal)
  | .safety => safetyCountermodel
  | .tautologyWithTeeth => tautologyMutantDivergence
  | .structural => structuralTriviality

/-- A nontrivial intent may mix structural goals with a real mandatory safety goal. -/
def safetyIntent : IntentProfile where
  Goal := DemoGoal
  contract := demoContract
  mandatoryGoals := [.structural, .safety]
  criticalGoals := [.safety]
  adequacy := demoAdequacy
  policy := .requireLoadBearing

theorem semantic_countermodel_supports_real_intent :
    ClosureAdequate safetyIntent := by
  constructor
  · right
    exact ⟨.safety,
      by exact List.Mem.tail _ (List.Mem.head _),
      by simp [safetyIntent, demoAdequacy, safetyCountermodel, GoalAdequacy.evidence,
        LoadBearingEvidence.IsLoadBearing]⟩
  · exact ⟨.safety,
      by exact List.Mem.head _,
      by simp [safetyIntent, demoAdequacy, safetyCountermodel, GoalAdequacy.evidence,
        LoadBearingEvidence.IsLoadBearing]⟩

/-- A tautological claim is admissible only because the real/mutant verifier diverges. -/
def mutantBackedIntent : IntentProfile where
  Goal := DemoGoal
  contract := demoContract
  mandatoryGoals := [.tautologyWithTeeth]
  criticalGoals := [.tautologyWithTeeth]
  adequacy := demoAdequacy
  policy := .requireLoadBearing

theorem mutant_divergence_supports_real_intent :
    ClosureAdequate mutantBackedIntent := by
  constructor
  · right
    exact ⟨.tautologyWithTeeth,
      by exact List.Mem.head _,
      by simp [mutantBackedIntent, demoAdequacy, tautologyMutantDivergence,
        GoalAdequacy.evidence,
        LoadBearingEvidence.IsLoadBearing]⟩
  · exact ⟨.tautologyWithTeeth,
      by exact List.Mem.head _,
      by simp [mutantBackedIntent, demoAdequacy, tautologyMutantDivergence,
        GoalAdequacy.evidence,
        LoadBearingEvidence.IsLoadBearing]⟩

/-! ## CM-GOAL-01a: empty mandatory goals vacuously close in the naive model -/

/-- The naive conjunction used to expose empty-list vacuity independently of the kernel. -/
def NaiveMandatorySatisfied {Goal : Type} (mandatory : List Goal)
    (satisfied : Goal → Prop) : Prop :=
  ∀ goal, goal ∈ mandatory → satisfied goal

/--
Even an always-false satisfaction relation "satisfies" every goal in an empty
mandatory list. This is the exact vacuous-close footgun.
-/
theorem empty_mandatory_naively_closes :
    NaiveMandatorySatisfied ([] : List DemoGoal) (fun _ => False) := by
  intro goal hmem
  cases hmem

/-- The critical safety goal exists, isolating the failure to the empty mandatory set. -/
def emptyMandatoryIntent : IntentProfile where
  Goal := DemoGoal
  contract := demoContract
  mandatoryGoals := []
  criticalGoals := [.safety]
  adequacy := demoAdequacy
  policy := .requireLoadBearing

/-- The real kernel refuses the same empty mandatory set under nontrivial policy. -/
theorem empty_mandatory_real_kernel_refuses :
    ¬ IntentAdequate emptyMandatoryIntent := by
  intro hadequate
  have hnonempty := intent_adequate_requires_nonempty_mandatory
    emptyMandatoryIntent rfl hadequate
  exact hnonempty rfl

/-! ## CM-GOAL-01b: `Claim := True` makes ordinary verifier soundness vacuous -/

/--
The forged verifier accepts every certificate and the claim is definitionally
`True`, so the ordinary `verify = true → Claim` condition passes vacuously.
-/
def claimTrueForgedGoal : GoalContract where
  History := Unit
  Certificate := Unit
  lawful := fun _ => True
  claim := fun _ => True
  verify := fun _ _ => true
  mutantVerify := fun _ _ => true

theorem claim_true_forged_certificate_is_accepted :
    claimTrueForgedGoal.verify () () = true := by
  rfl

theorem claim_true_passes_naive_verifier_soundness :
    ∀ history certificate,
      claimTrueForgedGoal.verify history certificate = true →
        claimTrueForgedGoal.claim history := by
  intro _ _ _
  trivial

/--
The dependent evidence kernel admits no load-bearing witness for the forged
`Claim := True` verifier: a countermodel contradicts `True`, and mutant divergence
contradicts the always-accepting real verifier.
-/
theorem claim_true_forged_goal_has_only_trivial_evidence
    (adequacy : GoalAdequacy claimTrueForgedGoal) :
    adequacy.evidence = .explicitlyTrivial := by
  cases adequacy with
  | countermodel _ _ _ claimRefuted _ =>
      exact False.elim (claimRefuted trivial)
  | mutantDivergence _ _ _ _ _ realRejects =>
      simp [claimTrueForgedGoal] at realRejects
  | explicitlyTrivial _ =>
      rfl

inductive ForgedGoal
  | only
  deriving DecidableEq

def forgedContract (_ : ForgedGoal) : GoalContract :=
  claimTrueForgedGoal

def forgedAdequacy (_ : ForgedGoal) : GoalAdequacy claimTrueForgedGoal :=
  .explicitlyTrivial (fun _ _ => trivial)

def forgedCriticalIntent : IntentProfile where
  Goal := ForgedGoal
  contract := forgedContract
  mandatoryGoals := [.only]
  criticalGoals := [.only]
  adequacy := forgedAdequacy
  policy := .requireLoadBearing

/-- The real kernel refuses to upgrade naive Claim-True soundness into critical closure. -/
theorem claim_true_forged_close_real_kernel_refuses :
    ¬ ClosureAdequate forgedCriticalIntent := by
  intro hclosure
  obtain ⟨goal, _, hload⟩ := hclosure.2
  have htrivial :
      (forgedCriticalIntent.adequacy goal).evidence = .explicitlyTrivial :=
    claim_true_forged_goal_has_only_trivial_evidence
      (forgedCriticalIntent.adequacy goal)
  exact hload htrivial

/-! ## CM-GOAL-01c: an all-trivial critical intent carries zero closure strength -/

inductive TrivialGoal
  | bookkeeping
  | schemaReflexivity
  deriving DecidableEq

def trivialContract (_ : TrivialGoal) : GoalContract :=
  structuralGoal

def trivialAdequacy (_ : TrivialGoal) : GoalAdequacy structuralGoal :=
  structuralTriviality

def allTrivialCriticalIntent : IntentProfile where
  Goal := TrivialGoal
  contract := trivialContract
  mandatoryGoals := [.bookkeeping, .schemaReflexivity]
  criticalGoals := [.bookkeeping, .schemaReflexivity]
  adequacy := trivialAdequacy
  policy := .requireLoadBearing

/-- The naive conjunction closes because both structural claims are `True`. -/
theorem all_trivial_critical_intent_naively_closes :
    NaiveMandatorySatisfied allTrivialCriticalIntent.mandatoryGoals
      (fun _ => True) := by
  intro _ _
  trivial

/-- Explicit triviality cannot alone make a nontrivial intent adequate. -/
theorem all_trivial_intent_real_kernel_refuses :
    ¬ IntentAdequate allTrivialCriticalIntent := by
  intro hadequate
  obtain ⟨goal, _, hload⟩ :=
    intent_adequate_requires_load_bearing_mandatory
      allTrivialCriticalIntent rfl hadequate
  exact hload (by cases goal <;> rfl)

/-- Explicit triviality contributes no critical closure strength either. -/
theorem all_trivial_critical_closure_real_kernel_refuses :
    ¬ CriticalClosureAdequate allTrivialCriticalIntent := by
  intro hcritical
  obtain ⟨goal, _, hload⟩ := hcritical
  exact hload (by cases goal <;> rfl)

/-! ## Explicit whole-intent triviality policy exception -/

def explicitlyTrivialIntent : IntentProfile where
  Goal := TrivialGoal
  contract := trivialContract
  mandatoryGoals := []
  criticalGoals := []
  adequacy := trivialAdequacy
  policy := .explicitlyAdmitEntireIntentTrivial

/--
The policy exception is explicit and narrow: it makes the intent adequate, but
does not forge critical closure strength.
-/
theorem explicit_whole_intent_triviality_is_adequate :
    IntentAdequate explicitlyTrivialIntent := by
  left
  rfl

theorem explicit_whole_intent_triviality_is_not_critical_closure :
    ¬ CriticalClosureAdequate explicitlyTrivialIntent := by
  intro hcritical
  obtain ⟨_, hmem, _⟩ := hcritical
  cases hmem

/-! ## Exact statement pins -/

/--
The nontrivial-policy theorem must expose an actual mandatory load-bearing
witness, not merely return `True` or a policy tag.
-/
example :
    ∀ (intent : IntentProfile),
      intent.policy = .requireLoadBearing →
      IntentAdequate intent →
      HasLoadBearingGoal intent intent.mandatoryGoals :=
  intent_adequate_requires_load_bearing_mandatory

/--
RCC-19 is pinned to all three conclusions: nonempty mandatory goals, a mandatory
load-bearing witness, and a critical load-bearing witness.
-/
example :
    ∀ (intent : IntentProfile),
      intent.policy = .requireLoadBearing →
      ClosureAdequate intent →
      intent.mandatoryGoals ≠ [] ∧
        HasLoadBearingGoal intent intent.mandatoryGoals ∧
        HasLoadBearingGoal intent intent.criticalGoals :=
  rcc19_intent_goal_nonvacuity

/-- info: 'Residua.RCC.rcc19_intent_goal_nonvacuity' does not depend on any axioms -/
#guard_msgs in
#print axioms rcc19_intent_goal_nonvacuity

end Residua.RCC.GoalAdequacyTests


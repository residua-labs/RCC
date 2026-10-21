import RCC.VerifierSoundness

/-! RCC-2 candidate: accepted certificates project only through a sound verifier. -/

namespace Residua.RCC.RCC2Target

open Residua.RCC

universe u v

abbrev concreteGoal : GoalContract where
  History := Nat
  Certificate := Bool
  lawful := fun _ => True
  claim := fun history => history = 7
  verify := fun history certificate => decide (history = 7 ∧ certificate = true)
  mutantVerify := fun _ _ => true

/-- The complete family of candidates which are bad for the concrete goal.
    Keeping the side condition explicit prevents a single `rfl` fixture from
    standing in for verifier discrimination. -/
def badCandidate (history : Nat) (certificate : Bool) : Prop :=
  history ≠ 7 ∨ certificate = false

/-- Two distinct bad inputs used as a small non-degenerate witness family. -/
def badCandidateFamily : List (Nat × Bool) :=
  [(8, true), (7, false)]

theorem badCandidateFamily_has_two_distinct_members :
    badCandidateFamily = [(8, true), (7, false)] ∧
      (8, true) ≠ (7, false) := by
  constructor
  · rfl
  · decide

theorem badCandidateFamily_members_are_bad :
    ∀ candidate ∈ badCandidateFamily,
      badCandidate candidate.1 candidate.2 := by
  intro candidate h
  simp [badCandidateFamily] at h
  rcases h with rfl | rfl
  · left
    decide
  · right
    rfl

theorem concreteVerifierSound : SoundGoalVerifier concreteGoal := by
  constructor
  intro history certificate accepted
  simp at accepted ⊢
  exact accepted.1

def concreteVerifier : SoundGoalVerifier concreteGoal := concreteVerifierSound

def acceptedSeven : AcceptedGoalCertificate concreteGoal concreteVerifier 7 where
  certificate := true
  accepted := by rfl

structure Certificate where
  genericAcceptedProjection :
    ∀ {goal : GoalContract.{u, v}}
      {verifier : SoundGoalVerifier goal}
      {history : goal.History},
      AcceptedGoalCertificate goal verifier history → goal.claim history
  verifierSound : SoundGoalVerifier concreteGoal
  acceptedCertificate : AcceptedGoalCertificate concreteGoal concreteVerifier 7
  acceptedClaim : concreteGoal.claim 7
  badCandidateFamilyHasTwoDistinctMembers :
    badCandidateFamily = [(8, true), (7, false)] ∧
      (8, true) ≠ (7, false)
  mutantAcceptsBadCandidate :
    ∀ history certificate, concreteGoal.mutantVerify history certificate = true
  realRejectsBadCandidate :
    ∀ history certificate, badCandidate history certificate →
      concreteGoal.verify history certificate = false

def certificate : Certificate where
  genericAcceptedProjection := fun accepted => accepted.sound
  verifierSound := concreteVerifier
  acceptedCertificate := acceptedSeven
  acceptedClaim := acceptedSeven.sound
  badCandidateFamilyHasTwoDistinctMembers :=
    badCandidateFamily_has_two_distinct_members
  mutantAcceptsBadCandidate := by
    intro history certificate
    rfl
  realRejectsBadCandidate := by
    intro history certificate bad
    simp [badCandidate] at bad ⊢
    rcases bad with historyBad | certificateBad
    · simp [historyBad]
    · simp [certificateBad]

def concreteCertificate : Certificate.{0, 0} := certificate

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC2Target

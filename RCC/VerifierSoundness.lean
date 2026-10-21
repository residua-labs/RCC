import RCC.GoalAdequacy

/-!
# R2 Certificate Verifier Soundness

A goal contract supplies executable certificate verification but does not gain
semantic authority from that function alone.  `SoundGoalVerifier` is the
load-bearing bridge from every accepted certificate to the indexed claim.
`AcceptedGoalCertificate` binds one exact history and certificate to that
verifier; its soundness theorem is the only projection to the claim.

This kernel does not discover certificates, decide claims, or bind a formal
verifier to a production executable.
-/

namespace Residua.RCC

universe u v

/-- Semantic soundness law for the executable verifier of one exact goal. -/
structure SoundGoalVerifier (goal : GoalContract.{u, v}) : Prop where
  acceptedSound :
    ∀ history certificate,
      goal.verify history certificate = true →
        goal.claim history

/--
One accepted certificate indexed by the exact goal contract and history.
Callers provide acceptance evidence, not a claim proof.
-/
structure AcceptedGoalCertificate
    (goal : GoalContract.{u, v})
    (verifier : SoundGoalVerifier goal)
    (history : goal.History) where
  certificate : goal.Certificate
  accepted : goal.verify history certificate = true

/-- R2 headline: accepted verification under a sound verifier proves the claim. -/
theorem AcceptedGoalCertificate.sound
    {goal : GoalContract.{u, v}}
    {verifier : SoundGoalVerifier goal}
    {history : goal.History}
    (accepted : AcceptedGoalCertificate goal verifier history) :
    goal.claim history :=
  verifier.acceptedSound history accepted.certificate accepted.accepted

end Residua.RCC

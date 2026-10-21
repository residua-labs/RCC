import RCC.TemporalValidity

/-!
# RCC-29 Temporal Closure Receipt

`CascadePlan.sound` proves several temporal facts at once, but an admitted
history needs a durable proof object carrying all of them together.  This
module packages that result without collapsing historical validity, current
usability, or successor transportability into one predicate.

Prelude-only Lean 4.14; all proof obligations are kernel-checked.
-/

namespace Residua.RCC.TemporalValidity

universe u

structure CascadeClosureReceipt
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch) where
  historicalPreserved :
    ∀ judgment window receipt,
      ValidAt (applyRevoke S snapshot event successorEpoch plan)
          judgment window receipt ↔
        ValidAt snapshot judgment window receipt
  dependentsResolved :
    ∀ judgment, S.dependsOn judgment event.target →
      (¬ UsableAt
          (applyRevoke S snapshot event successorEpoch plan) judgment) ∧
        TransportStateSound S snapshot successorEpoch judgment
          ((applyRevoke S snapshot event successorEpoch plan).currentState
            judgment) ∧
        match
          (applyRevoke S snapshot event successorEpoch plan).currentState judgment
        with
        | .transported replacementJudgment =>
            ∃ replacementTarget,
              event.replacement = some replacementTarget ∧
              S.replacementJudgmentFor replacementTarget replacementJudgment
        | _ => True
  independentPreserved :
    ∀ judgment, ¬ S.dependsOn judgment event.target →
      (applyRevoke S snapshot event successorEpoch plan).currentState judgment =
        snapshot.currentState judgment

theorem CascadePlan.toClosureReceipt
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch) :
    CascadeClosureReceipt S snapshot event successorEpoch plan := by
  have sound := CascadePlan.sound S snapshot event successorEpoch plan
  exact {
    historicalPreserved := sound.1
    dependentsResolved := sound.2.1
    independentPreserved := sound.2.2
  }

theorem CascadeClosureReceipt.dependent_not_usable
    {S : TemporalValiditySystem}
    {snapshot : TemporalSnapshot S}
    {event : Revoke S snapshot}
    {successorEpoch : S.Epoch}
    {plan : CascadePlan S snapshot event successorEpoch}
    (receipt : CascadeClosureReceipt S snapshot event successorEpoch plan)
    {judgment : S.Judgment}
    (hdependent : S.dependsOn judgment event.target) :
    ¬ UsableAt (applyRevoke S snapshot event successorEpoch plan) judgment :=
  (receipt.dependentsResolved judgment hdependent).1

theorem CascadeClosureReceipt.history_immutable
    {S : TemporalValiditySystem}
    {snapshot : TemporalSnapshot S}
    {event : Revoke S snapshot}
    {successorEpoch : S.Epoch}
    {plan : CascadePlan S snapshot event successorEpoch}
    (receipt : CascadeClosureReceipt S snapshot event successorEpoch plan)
    (judgment : S.Judgment) (window : S.Window) (proof : S.Receipt) :
    ValidAt (applyRevoke S snapshot event successorEpoch plan)
        judgment window proof ↔ ValidAt snapshot judgment window proof :=
  receipt.historicalPreserved judgment window proof

end Residua.RCC.TemporalValidity


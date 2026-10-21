import RCC.WakeContract

/-! RCC-22 candidate: Await wake adequacy and expired-wake reclassification. -/

namespace Residua.RCC.RCC22Target

open Residua.RCC

universe u v w x y z

structure Certificate where
  awaitSound :
    ∀ {S : WakeSystem.{u, v, w, x, y, z}} {state : S.State}
      {contract : WakeContract S state},
      AwaitCertificate S state contract →
      NoSameEpochAdvance S state ∧
        (¬ ∃ observation,
          S.observed state observation ∧ contract.wakePredicate observation) ∧
        S.currentGoal state = some contract.affectedGoal ∧
        S.goalOpen state contract.affectedGoal ∧
        S.goalObstructed state contract.affectedGoal ∧
        (¬ S.expired state contract.expiryOrRecheckPolicy) ∧
        ∃ observation,
          contract.wakePredicate observation ∧
          S.sourceOf observation = contract.observationSource ∧
          S.goalDependsOn state contract.affectedGoal observation ∧
          S.ruleApplies contract.invalidationRule observation
            contract.affectedGoal ∧
          EvidencePacketEffect S state observation contract.affectedGoal
  awaitPollInert :
    ∀ {S : WakeSystem.{u, v, w, x, y, z}} {state : S.State}
      {contract : WakeContract S state},
      (certificate : AwaitCertificate S state contract) →
      AwaitInert S state contract (awaitWithoutObservation certificate)
  expiredReclassifies :
    ∀ {S : WakeSystem.{u, v, w, x, y, z}} {origin checked : S.State}
      {contract : WakeContract S origin},
      S.expired checked contract.expiryOrRecheckPolicy →
      ∀ disposition : WakeDisposition S checked contract,
        ∃ classification : WakeReclassification,
          disposition.reclassification? = some classification
  expiredCannotAwait :
    ∀ {S : WakeSystem.{u, v, w, x, y, z}} {origin checked : S.State}
      {contract : WakeContract S origin},
      S.expired checked contract.expiryOrRecheckPolicy →
      ∀ disposition : WakeDisposition S checked contract,
        disposition.awaitsAgain = false

def certificate : Certificate where
  awaitSound := fun certificate => AwaitCertificate.sound certificate
  awaitPollInert := fun certificate =>
    await_without_observation_is_inert certificate
  expiredReclassifies := fun hexpired disposition =>
    expired_wake_must_reclassify _ hexpired disposition
  expiredCannotAwait := fun hexpired disposition =>
    expired_wake_cannot_await_again _ hexpired disposition

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC22Target

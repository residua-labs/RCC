import RCCTests.AdmissionLinearizer

/-!
# RCC-43 target package

This candidate packages settled admission as the conjunction of finality,
settled effect evidence, and durable history inclusion.  Authorized-only,
applied-unrecorded, and unrecorded-history mutants are refused.
-/

namespace Residua.RCC.RCC43Target

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AdmissionLinearizer.RealizationTests
open Residua.RCC.AdmissionLinearizer.SettlementBridgeTests
open Residua.RCC.AuthorizationFinality

structure Certificate : Prop where
  completeAdmission : Nonempty
    (SettledAdmission admissionEnvironment activateProposal)
  sameSlotUnique :
    ∀ {first second : Proposal Slot Head Judgment},
      (firstAdmission : SettledAdmission admissionEnvironment first) →
      (secondAdmission : SettledAdmission admissionEnvironment second) →
      first.slot = second.slot →
      admissionEnvironment.equivalence.Equivalent
        first.judgment second.judgment
  authorizedOnlyRefused :
    ¬ Nonempty (SettledAdmission authorizedOnlyEnvironment activateProposal)
  unsettledEffectRefused :
    ¬ Nonempty (SettledAdmission unsettledEnvironment activateProposal)
  unrecordedHistoryRefused :
    ¬ Nonempty (SettledAdmission unrecordedEnvironment activateProposal)

def certificate : Certificate where
  completeAdmission := ⟨completeAdmission⟩
  sameSlotUnique := by
    intro first second firstAdmission secondAdmission sameSlot
    exact settled_admissions_same_slot_equivalent
      firstAdmission secondAdmission sameSlot
  authorizedOnlyRefused := authorized_only_cannot_admit
  unsettledEffectRefused := finalized_unsettled_cannot_admit
  unrecordedHistoryRefused := settled_unrecorded_cannot_admit

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC43Target

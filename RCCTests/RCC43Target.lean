import RCC.RCC43Target

/-! Independent checks for the RCC-43 settled-admission target. -/

namespace Residua.RCC.RCC43Target.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AdmissionLinearizer.RealizationTests
open Residua.RCC.AdmissionLinearizer.SettlementBridgeTests
open Residua.RCC.RCC43Target

theorem target_has_complete_settled_admission :
    Nonempty (SettledAdmission admissionEnvironment activateProposal) :=
  certificate.completeAdmission

theorem target_preserves_same_slot_uniqueness :
    admissionEnvironment.equivalence.Equivalent
      activateProposal.judgment activateProposal.judgment :=
  certificate.sameSlotUnique
    (first := activateProposal)
    (second := activateProposal)
    completeAdmission completeAdmission rfl

theorem target_refuses_incomplete_effect_and_history :
    (¬ Nonempty (SettledAdmission authorizedOnlyEnvironment activateProposal)) ∧
      (¬ Nonempty (SettledAdmission unsettledEnvironment activateProposal)) ∧
      (¬ Nonempty (SettledAdmission unrecordedEnvironment activateProposal)) :=
  ⟨certificate.authorizedOnlyRefused,
    certificate.unsettledEffectRefused,
    certificate.unrecordedHistoryRefused⟩

theorem target_certificate_is_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

#print axioms target_has_complete_settled_admission
#print axioms target_preserves_same_slot_uniqueness
#print axioms target_refuses_incomplete_effect_and_history
#print axioms target_certificate_is_nonempty

end Residua.RCC.RCC43Target.Tests

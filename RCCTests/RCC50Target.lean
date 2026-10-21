import RCC.RCC50Target

/-! Thin admission checks for RCC-50 exact commutative joins. -/

namespace Residua.RCC.RCC50Target.Tests

open Residua.RCC.CommutativeJoin
open Residua.RCC.CommutativeJoin.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_checker_admits_actual_join :
    verifyExactJoin concreteCandidate = .admit concreteCertificate :=
  certificate.checkerAdmits

theorem target_one_sided_refused :
    verifyExactJoin oneSidedCandidate =
      .refuse .rightOperationOrderMismatch :=
  certificate.oneSidedRefused

theorem target_reused_occurrence_refused :
    verifyExactJoin reusedOccurrenceCandidate =
      .refuse .occurrenceNotRebased :=
  certificate.reusedOccurrenceRefused

theorem target_noncommuting_refused :
    verifyExactJoin noncommutingCandidate =
      .refuse .finalStateMismatch :=
  certificate.noncommutingRefused

#print axioms target_certificate_nonempty
#print axioms target_checker_admits_actual_join
#print axioms target_one_sided_refused
#print axioms target_reused_occurrence_refused
#print axioms target_noncommuting_refused

end Residua.RCC.RCC50Target.Tests

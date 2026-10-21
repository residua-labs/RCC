import RCC.RCC2Target

namespace Residua.RCC.RCC2Target.Tests

open Residua.RCC
open Residua.RCC.RCC2Target

theorem accepted_certificate_projects_claim :
    concreteGoal.claim 7 :=
  acceptedSeven.sound

theorem bad_candidate_family_is_non_degenerate :
    badCandidateFamily = [(8, true), (7, false)] ∧
      (8, true) ≠ (7, false) :=
  concreteCertificate.badCandidateFamilyHasTwoDistinctMembers

theorem every_bad_candidate_is_rejected_by_real_verifier :
    ∀ history certificate, badCandidate history certificate →
      concreteGoal.verify history certificate = false :=
  concreteCertificate.realRejectsBadCandidate

theorem every_candidate_is_accepted_by_mutant :
    ∀ history certificate, concreteGoal.mutantVerify history certificate = true :=
  concreteCertificate.mutantAcceptsBadCandidate

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms accepted_certificate_projects_claim
#print axioms bad_candidate_family_is_non_degenerate
#print axioms every_bad_candidate_is_rejected_by_real_verifier
#print axioms every_candidate_is_accepted_by_mutant
#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC2Target.Tests

import RCC.RCC94Target

/-! Independent seat for the RCC-94 cross-epoch fairness certificate. -/

namespace Residua.RCC.RCC94Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC94Target.Tests

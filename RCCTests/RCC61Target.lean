import RCC.RCC61Target

/-! Thin admission checks for RCC-61 executable defeq-address boundary. -/

namespace Residua.RCC.RCC61Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC61Target.Tests

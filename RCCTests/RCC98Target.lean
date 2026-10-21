import RCC.RCC98Target

/-! Independent seat for the RCC-98 addressed-resolution certificate. -/

namespace Residua.RCC.RCC98Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC98Target.Tests

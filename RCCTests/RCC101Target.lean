import RCC.RCC101Target

/-! Independent seat for the RCC-101 address-use registry certificate. -/

namespace Residua.RCC.RCC101Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC101Target.Tests

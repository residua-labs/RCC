import RCC.RCC97Target

/-! Independent seat for the RCC-97 address-kernel certificate. -/

namespace Residua.RCC.RCC97Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC97Target.Tests

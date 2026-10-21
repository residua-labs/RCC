import RCC.RCC100Target

/-! Independent seat for the RCC-100 canonical-codec certificate. -/

namespace Residua.RCC.RCC100Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC100Target.Tests

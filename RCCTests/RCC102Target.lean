import RCC.RCC102Target

/-! Independent seat for the RCC-102 component/seam gluing certificate. -/

namespace Residua.RCC.RCC102Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC102Target.Tests

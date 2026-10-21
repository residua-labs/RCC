import RCC.RCC105Target

/-! Independent seat for the RCC-105 defeq exactness certificate. -/

namespace Residua.RCC.RCC105Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC105Target.Tests

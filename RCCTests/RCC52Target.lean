import RCC.RCC52Target

/-! Thin admission checks for RCC-52 key-epoch vote binding. -/

namespace Residua.RCC.RCC52Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC52Target.Tests

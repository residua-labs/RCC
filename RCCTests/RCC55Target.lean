import RCC.RCC55Target

/-! Thin admission checks for RCC-55 mobile-adversary refresh safety. -/

namespace Residua.RCC.RCC55Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC55Target.Tests

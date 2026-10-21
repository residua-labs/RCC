import RCC.RCC18Target

namespace Residua.RCC.RCC18Target.Tests

open Residua.RCC.RCC18Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  rcc18_certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC18Target.Tests

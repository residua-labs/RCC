import RCC.RCC21Target

namespace Residua.RCC.RCC21Target.Tests

open Residua.RCC.RCC21Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC21Target.Tests

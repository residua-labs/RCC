import RCC.RCC26Target

namespace Residua.RCC.RCC26Target.Tests

open Residua.RCC.RCC26Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC26Target.Tests

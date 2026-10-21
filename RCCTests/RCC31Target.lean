import RCC.RCC31Target

namespace Residua.RCC.RCC31Target.Tests

open Residua.RCC.RCC31Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC31Target.Tests

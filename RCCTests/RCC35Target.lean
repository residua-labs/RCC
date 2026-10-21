import RCC.RCC35Target

namespace Residua.RCC.RCC35Target.Tests

open Residua.RCC.RCC35Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC35Target.Tests

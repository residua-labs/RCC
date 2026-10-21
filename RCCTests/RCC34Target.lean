import RCC.RCC34Target

namespace Residua.RCC.RCC34Target.Tests

open Residua.RCC.RCC34Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC34Target.Tests

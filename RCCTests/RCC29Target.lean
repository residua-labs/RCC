import RCC.RCC29Target

namespace Residua.RCC.RCC29Target.Tests

open Residua.RCC.RCC29Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC29Target.Tests

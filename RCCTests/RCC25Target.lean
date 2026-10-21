import RCC.RCC25Target

namespace Residua.RCC.RCC25Target.Tests

open Residua.RCC.RCC25Target

theorem target_certificate_nonempty : Nonempty (Certificate.{0, 0, 0, 0, 0, 0}) :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate.{0, 0, 0, 0, 0, 0} :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC25Target.Tests

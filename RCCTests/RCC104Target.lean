import RCC.RCC104Target

namespace Residua.RCC.RCC104Target.Tests

open Residua.RCC.RCC104Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC104Target.Tests

import RCC.RCC99Target

namespace Residua.RCC.RCC99Target.Tests

open Residua.RCC.RCC99Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC99Target.Tests

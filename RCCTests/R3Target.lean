import RCC.R3Target

namespace Residua.RCC.R3Target.Tests

open Residua.RCC.R3Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.R3Target.Tests

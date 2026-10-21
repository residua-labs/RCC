import RCC.R1Target

namespace Residua.RCC.R1Target.Tests

open Residua.RCC.R1Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.R1Target.Tests

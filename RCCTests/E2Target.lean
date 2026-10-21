import RCC.E2Target

namespace Residua.RCC.E2Target.Tests

open Residua.RCC.E2Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.E2Target.Tests

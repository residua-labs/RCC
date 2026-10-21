import RCC.R2Target

namespace Residua.RCC.R2Target.Tests

open Residua.RCC.R2Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.R2Target.Tests

import RCC.C2Target

namespace Residua.RCC.C2Target.Tests

open Residua.RCC.C2Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.C2Target.Tests

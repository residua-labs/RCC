import RCC.C4Target

namespace Residua.RCC.C4Target.Tests

open Residua.RCC.C4Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.C4Target.Tests

import RCC.E4Target

namespace Residua.RCC.E4Target.Tests

open Residua.RCC.E4Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.E4Target.Tests

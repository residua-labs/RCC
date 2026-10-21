import RCC.E5Target

namespace Residua.RCC.E5Target.Tests

open Residua.RCC.E5Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.E5Target.Tests

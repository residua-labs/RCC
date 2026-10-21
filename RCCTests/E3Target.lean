import RCC.E3Target

namespace Residua.RCC.E3Target.Tests

open Residua.RCC.E3Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.E3Target.Tests

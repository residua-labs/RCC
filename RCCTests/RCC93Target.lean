import RCC.RCC93Target

/-! Independent seat for RCC-93 reepoch debt-conservation certificate. -/

namespace Residua.RCC.RCC93Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC93Target.Tests

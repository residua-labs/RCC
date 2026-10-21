import RCC.RCC95Target

/-! Independent seat for the RCC-95 relative-closure capstone certificate. -/

namespace Residua.RCC.RCC95Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC95Target.Tests

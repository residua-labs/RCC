import RCC.RCC107Target

/-! Independent seat for the RCC-107 collision-aware defeq-address certificate. -/

namespace Residua.RCC.RCC107Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC107Target.Tests

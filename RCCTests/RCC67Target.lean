import RCC.RCC67Target

/-! Thin admission checks for RCC-67 trust-topology successor invalidation. -/

namespace Residua.RCC.RCC67Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC67Target.Tests

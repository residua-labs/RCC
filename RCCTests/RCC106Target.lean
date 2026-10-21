import RCC.RCC106Target

/-! Independent seat for the RCC-106 typed defeq-address certificate. -/

namespace Residua.RCC.RCC106Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC106Target.Tests

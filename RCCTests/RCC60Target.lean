import RCC.RCC60Target

/-! Thin admission checks for RCC-60 addressed-store and resolution receipts. -/

namespace Residua.RCC.RCC60Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC60Target.Tests

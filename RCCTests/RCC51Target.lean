import RCC.RCC51Target

/-! Thin admission checks for RCC-51 global invariant intent binding. -/

namespace Residua.RCC.RCC51Target.Tests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC51Target.Tests

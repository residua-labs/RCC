import RCC.RCC20Target

namespace Residua.RCC.RCC20Target.Tests

open Residua.RCC.RCC20Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  certificate_is_nonempty

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty

end Residua.RCC.RCC20Target.Tests

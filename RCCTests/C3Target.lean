import RCC.C3Target

namespace Residua.RCC.C3Target.Tests

open Residua.RCC.C3Target

theorem target_certificate_nonempty : Nonempty Certificate :=
  candidate_is_nonempty

theorem target_certificate_reexports : Certificate :=
  certificate

end Residua.RCC.C3Target.Tests

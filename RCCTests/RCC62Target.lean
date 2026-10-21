import RCC.RCC62Target

/-! Thin admission checks for RCC-62 sealed actual-influence coverage. -/

namespace Residua.RCC.RCC62Target.Tests

open Residua.RCC
open Residua.RCC.InvalidationClosureTests

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  candidate_is_nonempty

theorem target_certificate_binds_transitive_mutants :
    (¬ DirectInvalidated .sourceEdit .staleGreen) ∧
      directOnlyMutant.currentState .staleGreen = .usable ∧
      invalidatedSnapshot.currentState .staleGreen ≠
        directOnlyMutant.currentState .staleGreen := by
  exact ⟨certificate.directOnlyMissesTransitiveSource,
    certificate.directOnlyLeavesStaleGreenUsable,
    certificate.fullClosureRefusesDirectOnlyMutant⟩

def target_certificate_reexports : Certificate :=
  certificate

#print axioms target_certificate_nonempty
#print axioms target_certificate_reexports

end Residua.RCC.RCC62Target.Tests

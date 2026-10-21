import RCCTests.AssumptionRelativeSoundness

/-! RCC-R2 candidate: verifier soundness is distinct from assumption-relative
    authority; stale roots and inactive dependencies cannot bind a judgment. -/

namespace Residua.RCC.R2Target

open Residua.RCC.AssumptionRelativeSoundness.Tests
open Residua.RCC.AssumptionRelativeSoundness

structure Certificate where
  acceptedCurrentClaim :
    goal.claim (kernel.historyAt carrier.value)
  currentBindingClaim :
    kernel.ClaimUnder snapshot.coordinates.assumptionRoot
      (kernel.historyAt carrier.value)
  staleRootRejected :
    ¬ AssumptionRelativeCertificateBindingAt
      kernel snapshot carrier staleAccepted
  inactiveRootRejected :
    ¬ AssumptionRelativeCertificateBindingAt
      inactiveKernel snapshot carrier inactiveAccepted
  inactiveDependencyRejected :
    ¬ AssumptionRelativeCertificateBindingAt
      inactiveDependencyKernel snapshot carrier inactiveDependencyAccepted

def certificate : Certificate where
  acceptedCurrentClaim := currentAccepted.sound
  currentBindingClaim := current_active_root_proves_relative_claim
  staleRootRejected := stale_root_cannot_bind
  inactiveRootRejected := inactive_root_cannot_bind
  inactiveDependencyRejected := inactive_listed_dependency_cannot_bind

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.R2Target

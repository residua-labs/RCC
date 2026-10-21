import RCCTests.AssumptionRelativeSoundness

/-! RCC-68 candidate: assumption-relative soundness and stale-root refusal. -/

namespace Residua.RCC.RCC68Target

open Residua.RCC.AssumptionRelativeSoundness.Tests
open Residua.RCC.AssumptionRelativeSoundness

def currentRootClaim := current_active_root_proves_relative_claim
def rawStaleRootClaim := r2_alone_accepts_stale_root
def staleRootRefused := stale_root_cannot_bind
def inactiveRootRefused := inactive_root_cannot_bind
def inactiveDependencyRefused := inactive_listed_dependency_cannot_bind

structure Certificate where
  currentRootClaim :
    kernel.ClaimUnder snapshot.coordinates.assumptionRoot
      (kernel.historyAt carrier.value)
  rawStaleRootClaim :
    goal.claim (kernel.historyAt carrier.value)
  staleRootRefused :
    ¬ AssumptionRelativeCertificateBindingAt kernel snapshot carrier staleAccepted
  inactiveRootRefused :
    ¬ AssumptionRelativeCertificateBindingAt inactiveKernel snapshot carrier
        inactiveAccepted
  inactiveDependencyRefused :
    ¬ AssumptionRelativeCertificateBindingAt inactiveDependencyKernel snapshot carrier
        inactiveDependencyAccepted

def certificate : Certificate where
  currentRootClaim := current_active_root_proves_relative_claim
  rawStaleRootClaim := r2_alone_accepts_stale_root
  staleRootRefused := stale_root_cannot_bind
  inactiveRootRefused := inactive_root_cannot_bind
  inactiveDependencyRefused := inactive_listed_dependency_cannot_bind

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC68Target

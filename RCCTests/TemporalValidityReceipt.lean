import RCC.TemporalValidityReceipt
import RCCTests.FormalCoreTemporalValidity

/-!
# RCC-29 Temporal Closure Receipt Witnesses

The lawful clock and hash revocations produce durable receipts.  Mutants that
rewrite history or manufacture an unproved transport marker remain rejected.
-/

namespace Residua.RCC.TemporalValidity.ReceiptTests

open Residua.RCC.TemporalValidity
open Residua.RCC.TemporalValidity.Tests

def clockReceipt :
    CascadeClosureReceipt demoSystem initialSnapshot clockRevoke
      .kernelV2 clockPlan :=
  CascadePlan.toClosureReceipt demoSystem initialSnapshot clockRevoke
    .kernelV2 clockPlan

def hashReceipt :
    CascadeClosureReceipt demoSystem initialSnapshot hashRevoke
      .kernelV2 hashPlan :=
  CascadePlan.toClosureReceipt demoSystem initialSnapshot hashRevoke
    .kernelV2 hashPlan

theorem clock_receipt_preserves_history :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt := by
  exact (clockReceipt.history_immutable
    .expiry .admitted .expiryReceipt).mpr rfl

theorem clock_receipt_removes_stale_authority :
    ¬ UsableAt clockRevoked .expiry := by
  exact clockReceipt.dependent_not_usable (by
    simp [demoSystem, demoDependsOn, clockRevoke, clockTarget])

theorem hash_receipt_binds_transport_target :
    ∃ replacementTarget,
      hashRevoke.replacement = some replacementTarget ∧
      demoSystem.replacementJudgmentFor replacementTarget .hashSoundV2 := by
  have h := hashReceipt.dependentsResolved .hashSound (by
    simp [demoSystem, demoDependsOn, hashRevoke, hashTarget])
  have hstate :
      (applyRevoke demoSystem initialSnapshot hashRevoke .kernelV2 hashPlan).currentState
        .hashSound = .transported .hashSoundV2 :=
    by simpa [hashRevoked] using certified_transport_is_recorded
  rw [hstate] at h
  exact h.2.2

theorem history_rewrite_cannot_be_a_temporal_receipt :
    ¬ (ValidAt historyRewriteMutant .expiry .admitted .expiryReceipt) := by
  simp [ValidAt, historyRewriteMutant]

theorem unproved_transport_cannot_be_a_temporal_receipt :
    ¬ TransportStateSound demoSystem transportWithoutProofMutant
      .kernelV2 .expiry
      (transportWithoutProofMutant.currentState .expiry) := by
  simp [TransportStateSound, Transportable, transportWithoutProofMutant,
    demoSystem, demoTransportable, initialSnapshot]

end Residua.RCC.TemporalValidity.ReceiptTests


import RCC.TemporalValidity
import RCC.TemporalValidityReceipt
import RCCTests.FormalCoreTemporalValidity
import RCCTests.TemporalValidityReceipt

/-!
# RCC-29 target package

This candidate packages temporal judgment validity as three separate
predicates: historical `ValidAt`, current `UsableAt`, and successor-epoch
`Transportable`.  A lawful revoke preserves immutable history while forcing
declared dependents to revalidate, transport with a replacement-specific
certificate, or reopen.

The official detector registry is intentionally unchanged.

Prelude-only Lean 4.14; no proof placeholders or custom axioms.
-/

namespace Residua.RCC.RCC29Target

open Residua.RCC.TemporalValidity
open Residua.RCC.TemporalValidity.Tests
open Residua.RCC.TemporalValidity.ReceiptTests

universe u

theorem generic_revoke_preserves_valid_at
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment) (window : S.Window) (receipt : S.Receipt) :
    ValidAt (applyRevoke S snapshot event successorEpoch plan)
        judgment window receipt ↔
      ValidAt snapshot judgment window receipt :=
  revoke_preserves_valid_at S snapshot event successorEpoch plan
    judgment window receipt

theorem generic_dependent_judgment_cannot_remain_usable
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hdependent : S.dependsOn judgment event.target) :
    ¬ UsableAt (applyRevoke S snapshot event successorEpoch plan) judgment :=
  dependent_judgment_not_usable_after_revoke
    S snapshot event successorEpoch plan judgment hdependent

structure ConcreteWitness : Prop where
  clockHistoryPreserved :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt
  clockDependentNotUsable :
    ¬ UsableAt clockRevoked .expiry
  hashTransportRecorded :
    hashRevoked.currentState .hashSound = .transported .hashSoundV2
  hashTransportBoundToReplacement :
    ∃ replacementTarget,
      hashRevoke.replacement = some replacementTarget ∧
      demoSystem.replacementJudgmentFor replacementTarget .hashSoundV2
  clockReceiptHistory :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt
  lawfulTransportSound :
    TransportStateSound demoSystem hashRevoked .kernelV2 .hashSound
      (hashRevoked.currentState .hashSound)

structure MutantRefusal : Prop where
  staleGreenRefused :
    clockRevoked.currentState .expiry ≠
      staleGreenMutant.currentState .expiry
  transportWithoutProofRefused :
    ¬ TransportStateSound demoSystem transportWithoutProofMutant
      .kernelV2 .expiry
      (transportWithoutProofMutant.currentState .expiry)
  historyRewriteRefused :
    ¬ ValidAt historyRewriteMutant .expiry .admitted .expiryReceipt
  wrongReplacementRefused :
    ¬ demoSystem.replacementJudgmentFor evidenceTarget .hashSoundV2
  unrelatedReopenRefused :
    clockRevoked.currentState .unrelated ≠
      unrelatedReopenMutant.currentState .unrelated

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { clockHistoryPreserved := historical_receipt_is_immutable
      clockDependentNotUsable := clock_receipt_removes_stale_authority
      hashTransportRecorded := certified_transport_is_recorded
      hashTransportBoundToReplacement :=
        hash_receipt_binds_transport_target
      clockReceiptHistory := clock_receipt_preserves_history
      lawfulTransportSound := lawful_transport_carries_changed_kernel_proof }
  mutants :=
    { staleGreenRefused := stale_green_mutant_detected
      transportWithoutProofRefused :=
        transport_without_proof_mutant_detected.2.2
      historyRewriteRefused := history_rewrite_cannot_be_a_temporal_receipt
      wrongReplacementRefused := wrong_replacement_target_mutant_detected
      unrelatedReopenRefused := unrelated_reopen_mutant_detected }

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC29Target


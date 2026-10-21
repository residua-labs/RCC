import RCCTests.FormalCoreTemporalValidity

/-! RCC-66 candidate: temporal validity, usability, and transport boundaries. -/

namespace Residua.RCC.RCC66Target

open Residua.RCC.TemporalValidity
open Residua.RCC.TemporalValidity.Tests

def historicalValidityImmutable := historical_receipt_is_immutable
def dependentJudgmentReopened := dependent_judgment_is_reopened
def dependentJudgmentRevalidated := dependent_judgment_is_revalidated
def certifiedTransportRecorded := certified_transport_is_recorded
def validAtNotUsability := valid_at_does_not_imply_current_usability
def usabilityNotTransportability := usability_does_not_imply_transportability
def staleGreenRefused := stale_green_mutant_detected
def transportWithoutProofRefused := transport_without_proof_mutant_detected
def lawfulTransportCarriesProof := lawful_transport_carries_changed_kernel_proof
def replacementSpecificTransport := lawful_transport_is_bound_to_event_replacement
def wrongReplacementRefused := wrong_replacement_target_mutant_detected
def historyRewriteRefused := history_rewrite_mutant_detected
def unrelatedRevocationPreserved := unrelated_revocation_does_not_reopen_independent_judgment
def unrelatedReopenRefused := unrelated_reopen_mutant_detected

structure Certificate where
  historicalValidityImmutable :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt
  dependentJudgmentReopened :
    clockRevoked.currentState .expiry = .reopened
  dependentJudgmentRevalidated :
    evidenceRevoked.currentState .evidenceBacked = .revalidate
  certifiedTransportRecorded :
    hashRevoked.currentState .hashSound = .transported .hashSoundV2
  validAtNotUsability :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt ∧
      ¬ UsableAt clockRevoked .expiry
  usabilityNotTransportability :
    UsableAt initialSnapshot .expiry ∧
      ¬ Transportable demoSystem .expiry .expiry .kernelV1 .kernelV2
  staleGreenRefused :
    clockRevoked.currentState .expiry ≠
      staleGreenMutant.currentState .expiry
  transportWithoutProofRefused :
    ValidAt transportWithoutProofMutant .expiry .admitted .expiryReceipt ∧
      transportWithoutProofMutant.currentState .expiry =
        .transported .hashSoundV2 ∧
      ¬ TransportStateSound demoSystem transportWithoutProofMutant
        .kernelV2 .expiry
        (transportWithoutProofMutant.currentState .expiry)
  lawfulTransportCarriesProof :
    TransportStateSound demoSystem hashRevoked .kernelV2 .hashSound
      (hashRevoked.currentState .hashSound)
  replacementSpecificTransport :
    ∃ replacementTarget,
      hashRevoke.replacement = some replacementTarget ∧
      demoSystem.replacementJudgmentFor replacementTarget .hashSoundV2
  wrongReplacementRefused :
    ¬ demoSystem.replacementJudgmentFor evidenceTarget .hashSoundV2
  historyRewriteRefused :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt ∧
      ¬ ValidAt historyRewriteMutant .expiry .admitted .expiryReceipt
  unrelatedRevocationPreserved :
    clockRevoked.currentState .unrelated = .usable
  unrelatedReopenRefused :
    clockRevoked.currentState .unrelated ≠
      unrelatedReopenMutant.currentState .unrelated

def certificate : Certificate where
  historicalValidityImmutable := historicalValidityImmutable
  dependentJudgmentReopened := dependentJudgmentReopened
  dependentJudgmentRevalidated := dependentJudgmentRevalidated
  certifiedTransportRecorded := certifiedTransportRecorded
  validAtNotUsability := validAtNotUsability
  usabilityNotTransportability := usabilityNotTransportability
  staleGreenRefused := staleGreenRefused
  transportWithoutProofRefused := transportWithoutProofRefused
  lawfulTransportCarriesProof := lawfulTransportCarriesProof
  replacementSpecificTransport := replacementSpecificTransport
  wrongReplacementRefused := wrongReplacementRefused
  historyRewriteRefused := historyRewriteRefused
  unrelatedRevocationPreserved := unrelatedRevocationPreserved
  unrelatedReopenRefused := unrelatedReopenRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC66Target

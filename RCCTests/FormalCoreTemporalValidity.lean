import RCC.TemporalValidity

/-!
# RCC-29 Temporal Judgment Validity Witnesses

These witnesses keep immutable historical validity, current usability, and
successor-epoch transportability separate.  The supplied dependency relation is
already dependency-closed; this file does not claim completeness for a
repository dependency extractor.
-/

namespace Residua.RCC.TemporalValidity.Tests

open Residua.RCC.TemporalValidity

inductive TargetQ
  | clockAssumption
  | hashBinding
  | hashBindingV2
  | externalEvidence
  deriving DecidableEq

inductive Judgment
  | expiry
  | hashSound
  | hashSoundV2
  | evidenceBacked
  | unrelated
  deriving DecidableEq

inductive Window
  | admitted
  | current
  deriving DecidableEq

inductive Epoch
  | kernelV1
  | kernelV2
  deriving DecidableEq

inductive Authority
  | governanceRoot
  deriving DecidableEq

inductive Receipt
  | expiryReceipt
  | hashReceipt
  | evidenceReceipt
  | unrelatedReceipt
  deriving DecidableEq

inductive ReasonQ
  | sourceRetracted
  deriving DecidableEq

def clockTarget : TargetRef TargetQ :=
  ⟨.clockAssumption, .assumption⟩

def hashTarget : TargetRef TargetQ :=
  ⟨.hashBinding, .implementationBinding⟩

def hashTargetV2 : TargetRef TargetQ :=
  ⟨.hashBindingV2, .implementationBinding⟩

def evidenceTarget : TargetRef TargetQ :=
  ⟨.externalEvidence, .evidence⟩

def demoDependsOn : Judgment → TargetRef TargetQ → Prop
  | .expiry, target => target = clockTarget
  | .hashSound, target => target = hashTarget
  | .evidenceBacked, target => target = evidenceTarget
  | _, _ => False

def demoTransportable : Judgment → Judgment → Epoch → Epoch → Prop
  | .hashSound, .hashSoundV2, .kernelV1, .kernelV2 => True
  | _, _, _, _ => False

def demoReplacementJudgmentFor :
    TargetRef TargetQ → Judgment → Prop
  | target, .hashSoundV2 => target = hashTargetV2
  | _, _ => False

def demoSystem : TemporalValiditySystem where
  TargetQ := TargetQ
  Judgment := Judgment
  Window := Window
  Epoch := Epoch
  Authority := Authority
  Receipt := Receipt
  ReasonQ := ReasonQ
  dependsOn := demoDependsOn
  dependsOnDecidable := fun judgment target => by
    cases judgment <;> cases target <;> simp [demoDependsOn, clockTarget,
      hashTarget, evidenceTarget] <;> infer_instance
  authorized := fun authority _ _ => authority = .governanceRoot
  effectiveAt := fun effective currentWindow =>
    effective = .current ∧ currentWindow = .current
  transportable := demoTransportable
  replacementJudgmentFor := demoReplacementJudgmentFor

def initialSnapshot : TemporalSnapshot demoSystem where
  epoch := .kernelV1
  window := .current
  historicalReceipt := fun judgment window =>
    match judgment, window with
    | .expiry, .admitted => some .expiryReceipt
    | .hashSound, .admitted => some .hashReceipt
    | .evidenceBacked, .admitted => some .evidenceReceipt
    | .unrelated, .admitted => some .unrelatedReceipt
    | _, _ => none
  currentState := fun _ => .usable

def clockRevoke : Revoke demoSystem initialSnapshot where
  target := clockTarget
  effectiveWindow := .current
  reasonQ := .sourceRetracted
  authority := .governanceRoot
  replacement := none
  authorityProof := rfl
  effectiveProof := ⟨rfl, rfl⟩

def clockPlan :
    CascadePlan demoSystem initialSnapshot clockRevoke .kernelV2 where
  resolve := fun judgment depends => by
    cases judgment with
    | expiry => exact .reopen
    | hashSound =>
        simp [demoSystem, demoDependsOn, clockRevoke, clockTarget, hashTarget] at depends
    | hashSoundV2 => simp [demoSystem, demoDependsOn] at depends
    | evidenceBacked =>
        simp [demoSystem, demoDependsOn, clockRevoke, clockTarget,
          evidenceTarget] at depends
    | unrelated => simp [demoSystem, demoDependsOn] at depends

def clockRevoked : TemporalSnapshot demoSystem :=
  applyRevoke demoSystem initialSnapshot clockRevoke .kernelV2 clockPlan

def evidenceRevoke : Revoke demoSystem initialSnapshot where
  target := evidenceTarget
  effectiveWindow := .current
  reasonQ := .sourceRetracted
  authority := .governanceRoot
  replacement := none
  authorityProof := rfl
  effectiveProof := ⟨rfl, rfl⟩

def evidencePlan :
    CascadePlan demoSystem initialSnapshot evidenceRevoke .kernelV2 where
  resolve := fun judgment depends => by
    cases judgment with
    | evidenceBacked => exact .revalidate
    | expiry =>
        simp [demoSystem, demoDependsOn, evidenceRevoke, clockTarget,
          evidenceTarget] at depends
    | hashSound =>
        simp [demoSystem, demoDependsOn, evidenceRevoke, hashTarget,
          evidenceTarget] at depends
    | hashSoundV2 => simp [demoSystem, demoDependsOn] at depends
    | unrelated => simp [demoSystem, demoDependsOn] at depends

def evidenceRevoked : TemporalSnapshot demoSystem :=
  applyRevoke demoSystem initialSnapshot evidenceRevoke .kernelV2 evidencePlan

def hashRevoke : Revoke demoSystem initialSnapshot where
  target := hashTarget
  effectiveWindow := .current
  reasonQ := .sourceRetracted
  authority := .governanceRoot
  replacement := some hashTargetV2
  authorityProof := rfl
  effectiveProof := ⟨rfl, rfl⟩

def hashPlan :
    CascadePlan demoSystem initialSnapshot hashRevoke .kernelV2 where
  resolve := fun judgment depends => by
    cases judgment with
    | hashSound =>
        exact .transport hashTargetV2 rfl .hashSoundV2
          (by simp [demoSystem, demoReplacementJudgmentFor])
          (by simp [demoSystem, demoTransportable, initialSnapshot])
    | expiry =>
        simp [demoSystem, demoDependsOn, hashRevoke, clockTarget, hashTarget] at depends
    | hashSoundV2 => simp [demoSystem, demoDependsOn] at depends
    | evidenceBacked =>
        simp [demoSystem, demoDependsOn, hashRevoke, hashTarget,
          evidenceTarget] at depends
    | unrelated => simp [demoSystem, demoDependsOn] at depends

def hashRevoked : TemporalSnapshot demoSystem :=
  applyRevoke demoSystem initialSnapshot hashRevoke .kernelV2 hashPlan

theorem historical_receipt_is_immutable :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt := by
  exact (revoke_preserves_valid_at
    demoSystem initialSnapshot clockRevoke .kernelV2 clockPlan
    .expiry .admitted .expiryReceipt).mpr rfl

theorem dependent_judgment_is_reopened :
    clockRevoked.currentState .expiry = .reopened := by
  simp [clockRevoked, applyRevoke, clockPlan, clockRevoke, demoSystem,
    demoDependsOn, clockTarget]

theorem dependent_judgment_is_revalidated :
    evidenceRevoked.currentState .evidenceBacked = .revalidate := by
  simp [evidenceRevoked, applyRevoke, evidencePlan, evidenceRevoke, demoSystem,
    demoDependsOn, evidenceTarget]

theorem certified_transport_is_recorded :
    hashRevoked.currentState .hashSound = .transported .hashSoundV2 := by
  simp [hashRevoked, applyRevoke, hashPlan, hashRevoke, demoSystem,
    demoDependsOn, hashTarget]

theorem valid_at_does_not_imply_current_usability :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt ∧
      ¬ UsableAt clockRevoked .expiry := by
  exact
    ⟨historical_receipt_is_immutable,
      dependent_judgment_not_usable_after_revoke
        demoSystem initialSnapshot clockRevoke .kernelV2 clockPlan .expiry (by
          simp [demoSystem, demoDependsOn, clockRevoke, clockTarget])⟩

theorem usability_does_not_imply_transportability :
    UsableAt initialSnapshot .expiry ∧
      ¬ Transportable demoSystem .expiry .expiry .kernelV1 .kernelV2 := by
  constructor
  · rfl
  · simp [Transportable, demoSystem, demoTransportable]

/-- Mutant: the revoked dependency leaves a stale GREEN judgment usable. -/
def staleGreenMutant : TemporalSnapshot demoSystem where
  epoch := initialSnapshot.epoch
  window := initialSnapshot.window
  historicalReceipt := initialSnapshot.historicalReceipt
  currentState := initialSnapshot.currentState

/-- Mutant: a valid old receipt is transported across a new kernel without proof. -/
def transportWithoutProofMutant : TemporalSnapshot demoSystem where
  epoch := initialSnapshot.epoch
  window := initialSnapshot.window
  historicalReceipt := initialSnapshot.historicalReceipt
  currentState := fun
    | .expiry => .transported .hashSoundV2
    | judgment => initialSnapshot.currentState judgment

/-- Mutant: current revocation rewrites an immutable historical receipt. -/
def historyRewriteMutant : TemporalSnapshot demoSystem where
  epoch := initialSnapshot.epoch
  window := initialSnapshot.window
  historicalReceipt := fun judgment window =>
    match judgment, window with
    | .expiry, .admitted => none
    | _, _ => initialSnapshot.historicalReceipt judgment window
  currentState := clockRevoked.currentState

/-- Mutant: an unrelated revocation reopens an independent judgment. -/
def unrelatedReopenMutant : TemporalSnapshot demoSystem where
  epoch := initialSnapshot.epoch
  window := initialSnapshot.window
  historicalReceipt := initialSnapshot.historicalReceipt
  currentState := fun
    | .unrelated => .reopened
    | judgment => clockRevoked.currentState judgment

theorem stale_green_mutant_detected :
    clockRevoked.currentState .expiry ≠
      staleGreenMutant.currentState .expiry := by
  rw [dependent_judgment_is_reopened]
  simp [staleGreenMutant, initialSnapshot]

theorem transport_without_proof_mutant_detected :
    ValidAt transportWithoutProofMutant .expiry .admitted .expiryReceipt ∧
      transportWithoutProofMutant.currentState .expiry =
        .transported .hashSoundV2 ∧
      ¬ TransportStateSound demoSystem transportWithoutProofMutant
        .kernelV2 .expiry
        (transportWithoutProofMutant.currentState .expiry) := by
  constructor
  · rfl
  · constructor
    · rfl
    · simp [TransportStateSound, Transportable, transportWithoutProofMutant,
        demoSystem, demoTransportable, initialSnapshot]

theorem lawful_transport_carries_changed_kernel_proof :
    TransportStateSound demoSystem hashRevoked .kernelV2 .hashSound
      (hashRevoked.currentState .hashSound) := by
  exact dependent_judgment_transport_sound
    demoSystem initialSnapshot hashRevoke .kernelV2 hashPlan .hashSound (by
      simp [demoSystem, demoDependsOn, hashRevoke, hashTarget])

theorem transport_certificate_is_replacement_specific :
    Transportable demoSystem .hashSound .hashSoundV2 .kernelV1 .kernelV2 ∧
      ¬ Transportable demoSystem .hashSound .expiry .kernelV1 .kernelV2 := by
  simp [Transportable, demoSystem, demoTransportable]

theorem lawful_transport_is_bound_to_event_replacement :
    ∃ replacementTarget,
      hashRevoke.replacement = some replacementTarget ∧
      demoSystem.replacementJudgmentFor replacementTarget .hashSoundV2 := by
  have h := dependent_judgment_transport_target_sound
    demoSystem initialSnapshot hashRevoke .kernelV2 hashPlan .hashSound (by
      simp [demoSystem, demoDependsOn, hashRevoke, hashTarget])
  have hstate :
      (applyRevoke demoSystem initialSnapshot hashRevoke .kernelV2 hashPlan).currentState
          .hashSound =
        .transported .hashSoundV2 := by
    exact certified_transport_is_recorded
  rw [hstate] at h
  exact h

theorem wrong_replacement_target_mutant_detected :
    ¬ demoSystem.replacementJudgmentFor evidenceTarget .hashSoundV2 := by
  simp [demoSystem, demoReplacementJudgmentFor, evidenceTarget, hashTargetV2]

theorem history_rewrite_mutant_detected :
    ValidAt clockRevoked .expiry .admitted .expiryReceipt ∧
      ¬ ValidAt historyRewriteMutant .expiry .admitted .expiryReceipt := by
  constructor
  · exact historical_receipt_is_immutable
  · simp [ValidAt, historyRewriteMutant]

theorem unrelated_revocation_does_not_reopen_independent_judgment :
    clockRevoked.currentState .unrelated = .usable := by
  exact unrelated_judgment_state_preserved
    demoSystem initialSnapshot clockRevoke .kernelV2 clockPlan .unrelated (by
      simp [demoSystem, demoDependsOn])

theorem unrelated_reopen_mutant_detected :
    clockRevoked.currentState .unrelated ≠
      unrelatedReopenMutant.currentState .unrelated := by
  rw [unrelated_revocation_does_not_reopen_independent_judgment]
  simp [unrelatedReopenMutant]

#print axioms revoke_preserves_valid_at
#print axioms dependent_judgment_not_usable_after_revoke
#print axioms dependent_judgment_transport_sound
#print axioms unrelated_judgment_state_preserved
#print axioms historical_receipt_is_immutable
#print axioms valid_at_does_not_imply_current_usability
#print axioms usability_does_not_imply_transportability
#print axioms stale_green_mutant_detected
#print axioms transport_without_proof_mutant_detected
#print axioms lawful_transport_carries_changed_kernel_proof
#print axioms transport_certificate_is_replacement_specific
#print axioms lawful_transport_is_bound_to_event_replacement
#print axioms wrong_replacement_target_mutant_detected
#print axioms history_rewrite_mutant_detected
#print axioms unrelated_reopen_mutant_detected

end Residua.RCC.TemporalValidity.Tests

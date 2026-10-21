import RCC.ProofCarryingOutcome

/-! RCC-25 target package: proof-carrying branch derivation and CoreObject bridge. -/

namespace Residua.RCC.RCC25Target

open Residua.RCC.ProofCarryingOutcome

universe u a c w m h

structure Certificate : Prop where
  advancedCarries :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (state next : K.State)
      (certificate : K.AdvancePacket state next)
      (decreases : K.measure next < K.measure state),
      deriveOpen K state = .advanced next certificate decreases →
        Nonempty (K.AdvancePacket state next)
  reepochCarries :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (state : K.State)
      (certificate : K.MigrationPacket state),
      deriveOpen K state = .reepoch certificate →
        Nonempty (K.MigrationPacket state)
  haltCarries :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (state : K.State)
      (certificate : K.HaltPacket state),
      deriveOpen K state = .halt certificate →
        Nonempty (K.HaltPacket state)
  awaitExcludesAdvance :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (readers : BranchReadersComplete K)
      (state : K.State) (wake : K.WakePacket state),
      deriveOpen K state = .await wake →
        ¬ Nonempty
          (CertifiedAdvance K.State K.measure K.AdvancePacket state)
  reepochExcludesHigherPriority :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (readers : BranchReadersComplete K)
      (state : K.State) (migration : K.MigrationPacket state),
      deriveOpen K state = .reepoch migration →
        (¬ Nonempty
            (CertifiedAdvance K.State K.measure K.AdvancePacket state)) ∧
          ¬ Nonempty (K.WakePacket state)
  haltExcludesContinuation :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (readers : BranchReadersComplete K)
      (state : K.State) (failure : K.HaltPacket state),
      deriveOpen K state = .halt failure →
        (¬ Nonempty
            (CertifiedAdvance K.State K.measure K.AdvancePacket state)) ∧
          (¬ Nonempty (K.WakePacket state)) ∧
          ¬ Nonempty (K.MigrationPacket state)
  closedStops :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (reader : ClosedReaderComplete K)
      (state : K.State) (closed : Nonempty (K.ClosedPacket state)),
      ∃ certificate,
        Residua.RCC.ProofCarryingOutcome.normalize K state =
          .closed state certificate
  coreExact :
    ∀ (K : BranchSystem.{u, a, c, w, m, h}) (reader : ClosedReaderComplete K),
      (Residua.RCC.ProofCarryingOutcome.coreObject K).Exact

def certificate : Certificate.{0, 0, 0, 0, 0, 0} where
  advancedCarries := deriveOpen_advanced_certificate
  reepochCarries := deriveOpen_reepoch_certificate
  haltCarries := deriveOpen_halt_certificate
  awaitExcludesAdvance := by
    intro K readers state wake selected
    exact await_excludes_hidden_advance K readers state wake selected
  reepochExcludesHigherPriority := by
    intro K readers state migration selected
    exact reepoch_excludes_hidden_higher_priority
      K readers state migration selected
  haltExcludesContinuation := by
    intro K readers state failure selected
    exact halt_excludes_hidden_continuation K readers state failure selected
  closedStops := by
    intro K reader state closed
    exact normalize_of_closed K reader state closed
  coreExact := by
    intro K reader
    exact Residua.RCC.ProofCarryingOutcome.core_exact K reader

theorem certificate_is_nonempty : Nonempty (Certificate.{0, 0, 0, 0, 0, 0}) :=
  ⟨certificate⟩

end Residua.RCC.RCC25Target

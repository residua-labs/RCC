import RCC.FormalCore

/-!
# ResiduaRCCFormalCoreTests

RED-first executable theorem specification for the first RCC formal slice.
The file was committed before its production module and now remains the load-bearing
non-trivial witness for the implementation.
-/

open Residua.RCC

namespace Residua.RCC.Tests

/-- A non-trivial finite system: every open state `n > 0` advances to `n - 1`. -/
def countdownExec : Exec where
  State := Nat
  measure := id
  closed := fun n => n = 0
  closedDecidable := fun _ => inferInstance
  stepOpen := fun n h =>
    .advanced (Nat.pred n) (Nat.pred_lt h)

/-- One certified open-state step of the normalizer. -/
theorem countdown_normalize_succ (n : Nat) :
    normalize countdownExec (Nat.succ n) = normalize countdownExec n := by
  rw [normalize]
  simp [countdownExec]

/-- A closed state is a fixed point of the closed-result projection. -/
theorem countdown_closed_is_idempotent :
    (normalize countdownExec (0 : Nat)).state? = some (0 : Nat) := by
  exact normalize_state_of_closed countdownExec (0 : Nat) rfl

/-- The normalizer actually performs three certified advances before closing. -/
theorem countdown_normalizes_to_zero :
    (normalize countdownExec (3 : Nat)).state? = some (0 : Nat) := by
  rw [show (3 : Nat) = Nat.succ 2 by rfl, countdown_normalize_succ 2]
  rw [show (2 : Nat) = Nat.succ 1 by rfl, countdown_normalize_succ 1]
  rw [show (1 : Nat) = Nat.succ 0 by rfl, countdown_normalize_succ 0]
  exact countdown_closed_is_idempotent

/-- The executable system refines its induced relation on a concrete step. -/
theorem countdown_exec_refines_rel :
    (relOfExec countdownExec).step (3 : Nat) (2 : Nat) := by
  have hopen : ¬ countdownExec.closed (3 : Nat) := by
    change (3 : Nat) ≠ 0
    exact Nat.succ_ne_zero 2
  refine ⟨hopen, ?_⟩
  rfl

/-- The CoreObject bridge identifies normalizer fixed points with closed states. -/
theorem countdown_core_exact_at_zero :
    (coreObject countdownExec).D (0 : Nat) (0 : Nat) ↔
      (coreObject countdownExec).Adm (0 : Nat) := by
  exact core_exact_iff countdownExec (0 : Nat)

/-- A non-closed state is not a CoreObject fixed point. -/
theorem countdown_three_not_fixed :
    ¬ (coreObject countdownExec).D (3 : Nat) (3 : Nat) := by
  intro hfixed
  change (normalize countdownExec (3 : Nat)).state? = some (3 : Nat) at hfixed
  rw [countdown_normalizes_to_zero] at hfixed
  have hzero : (0 : Nat) = 3 := Option.some.inj hfixed
  exact Nat.noConfusion hzero

end Residua.RCC.Tests

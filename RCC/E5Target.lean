import RCCTests.FormalCore

/-! E5 candidate: certified Advanced steps strictly decrease a well-founded
    measure, refine the relation layer, terminate normalization, and connect
    its fixed points to executable closure. -/

namespace Residua.RCC.E5Target

open Residua.RCC
open Residua.RCC.Tests

structure Certificate where
  successorNormalizesSame :
    ∀ n : Nat,
      normalize countdownExec (Nat.succ n) = normalize countdownExec n
  finiteTraceCloses :
    (normalize countdownExec (3 : Nat)).state? = some (0 : Nat)
  advancedRefinesRelation :
    (relOfExec countdownExec).step (3 : Nat) (2 : Nat)
  closedFixedPoint :
    (coreObject countdownExec).D (0 : Nat) (0 : Nat) ↔
      (coreObject countdownExec).Adm (0 : Nat)
  nonclosedNotFixed :
    ¬ (coreObject countdownExec).D (3 : Nat) (3 : Nat)

def certificate : Certificate where
  successorNormalizesSame := countdown_normalize_succ
  finiteTraceCloses := countdown_normalizes_to_zero
  advancedRefinesRelation := countdown_exec_refines_rel
  closedFixedPoint := countdown_core_exact_at_zero
  nonclosedNotFixed := countdown_three_not_fixed

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.E5Target

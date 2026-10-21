import RCC.ComponentClosurePreservation

namespace Residua.RCC.ComponentClosurePreservation.Tests

open Residua.RCC

inductive State
  | zero
  | one
  deriving DecidableEq, Repr

def source : Rel where
  State := State
  step := fun start finish => start = .zero ∧ finish = .one
  closed := fun state => state = .one

def identitySeam : Seam source source where
  map := id
  closedPreserved := fun closed => closed
  stepPreserved := fun step => step

def sourceClosedTrace : source.ClosedTrace .zero .one where
  reaches := .tail ⟨rfl, rfl⟩ (.refl (R := source) State.one)
  terminal := rfl

theorem identity_seam_preserves_nonempty_closed_trace :
    source.ClosedTrace
      (identitySeam.map .zero) (identitySeam.map .one) :=
  identitySeam.closedTracePreserved sourceClosedTrace

def targetWithoutClosure : Rel where
  State := State
  step := source.step
  closed := fun _ => False

/-- The mutant still preserves every component step under the identity map. -/
theorem step_only_mapping_exists :
    ∀ {start finish},
      source.step start finish →
        targetWithoutClosure.step start finish :=
  fun step => step

/--
Step preservation alone cannot construct a seam: the source terminal would
have to become closed in a target where no state is closed.
-/
theorem step_only_mapping_cannot_preserve_component_closure :
    ¬ Nonempty (Seam source targetWithoutClosure) := by
  rintro ⟨seam⟩
  exact seam.closedPreserved (s := .one) rfl

end Residua.RCC.ComponentClosurePreservation.Tests

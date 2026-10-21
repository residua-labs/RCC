import RCC.StepExecModel
import RCC.RC1StepMSTBinding

/-!
# RC-1 adapter for the generic Step ExecModel

The existing `StepSurface` fixes the RC-1 class and settled-representative
coordinates.  This adapter adds the missing raw-attempt, outcome, quotient,
and typed-residue coordinates without pretending to synthesize them.  Its
four laws are instance obligations and are re-exported as the generic
`StepExecModel.Profile`.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RC1StepExecAdapter

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.StepExecModel

universe u v w x y

structure Adapter
    {State : Type u}
    (C : ClosureContext State)
    (surface : StepSurface C) : Type (max (max (max (max (u + 1) (v + 1)) (w + 1)) (x + 1)) (y + 1)) where
  Raw : Type v
  Outcome : Type w
  Residue : Type x
  q : Raw → surface.StepClass
  evalRaw : Raw → Outcome
  evalClass : surface.StepClass → Outcome
  rho : surface.StepClass → Option Residue
  quotient_factorization :
    ∀ raw, evalRaw raw = evalClass (q raw)
  representative_implies_admissible :
    ∀ cls rep, surface.sigma cls = some rep → surface.admitted cls = true
  residue_totality :
    ∀ cls,
      surface.active cls = true →
      surface.admitted cls = false →
      ∃ residue, rho cls = some residue
  representative_precision :
    ∀ cls,
      surface.active cls = true →
      surface.admitted cls = true →
      ∃ rep, surface.sigma cls = some rep

def model
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (adapter : Adapter C surface) : StepExecModel.Model where
  Raw := adapter.Raw
  Class := surface.StepClass
  Rep := surface.SettledEvent
  Residue := adapter.Residue
  Outcome := adapter.Outcome
  q := adapter.q
  evalRaw := adapter.evalRaw
  evalClass := adapter.evalClass
  active := surface.active
  admissible := surface.admitted
  rho := adapter.rho
  sigma := surface.sigma

def profile
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (adapter : Adapter C surface) :
    StepExecModel.Profile (model adapter) where
  quotient_factorization := adapter.quotient_factorization
  representative_implies_admissible := adapter.representative_implies_admissible
  residue_totality := adapter.residue_totality
  representative_precision := adapter.representative_precision

theorem adapter_has_profile
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (adapter : Adapter C surface) :
    StepExecModel.Profile (model adapter) :=
  profile adapter

end Residua.RCC.RC1StepExecAdapter

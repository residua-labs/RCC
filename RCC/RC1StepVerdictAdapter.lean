import RCC.StepVerdictModel
import RCC.RC1StepMSTBinding

/-!
# RC-1 typed verdict adapter

The ordinary RC-1 Step Exec adapter leaves `Outcome` abstract.  This adapter
specializes the same surface to the closed verdict vocabulary and requires
the verdict/readers to agree, so a residue cannot be present merely as an
unrelated side channel.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RC1StepVerdictAdapter

open Residua.RCC
open Residua.RCC.RelativeCompleteClosure
open Residua.RCC.RC1StepMSTBinding
open Residua.RCC.StepVerdictModel

universe u

structure Adapter
    {State : Type u}
    (C : ClosureContext State)
    (surface : StepSurface C) : Type (u + 1) where
  Raw : Type
  Residue : Type
  q : Raw → surface.StepClass
  evalRaw : Raw → Outcome surface.SettledEvent Residue
  evalClass : surface.StepClass → Outcome surface.SettledEvent Residue
  rho : surface.StepClass → Option Residue
  quotient_factorization :
    ∀ raw, evalRaw raw = evalClass (q raw)
  admitted_iff_accepted :
    ∀ cls,
      surface.admitted cls = true ↔
        ∃ rep, evalClass cls = .accepted rep
  representative_iff_accepted :
    ∀ cls rep,
      surface.sigma cls = some rep ↔
        evalClass cls = .accepted rep
  residue_totality :
    ∀ cls,
      surface.active cls = true →
      surface.admitted cls = false →
      ∃ residue,
        rho cls = some residue ∧
          (evalClass cls = .reject residue ∨
           evalClass cls = .await residue ∨
           evalClass cls = .reepoch residue ∨
           evalClass cls = .fatal residue)

def model
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (adapter : Adapter C surface) : StepVerdictModel.Model where
  Raw := adapter.Raw
  Class := surface.StepClass
  Rep := surface.SettledEvent
  Residue := adapter.Residue
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
    StepVerdictModel.Profile (model adapter) where
  quotient_factorization := adapter.quotient_factorization
  admitted_iff_admit := adapter.admitted_iff_accepted
  representative_iff_admit := adapter.representative_iff_accepted
  active_nonadmitted_has_typed_residue := adapter.residue_totality

theorem adapter_has_profile
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    (adapter : Adapter C surface) :
    StepVerdictModel.Profile (model adapter) :=
  profile adapter

theorem bound_advance_has_accepted_verdict
    {State : Type u}
    {C : ClosureContext State}
    {surface : StepSurface C}
    {adapter : Adapter C surface}
    {before after : State}
    {packet : AdvancePacket C before after}
    (binding : BoundAdvance surface packet) :
    (model adapter).evalClass (surface.classOf packet) =
      .accepted binding.event := by
  exact
    (adapter.representative_iff_accepted
      (surface.classOf packet) binding.event).1 binding.representative

end Residua.RCC.RC1StepVerdictAdapter

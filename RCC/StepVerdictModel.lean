import RCC.StepExecModel

/-!
# RCC Step verdict model

The generic Step-MST profile deliberately leaves `Outcome` abstract.  This
small refinement gives the outcome a closed operational vocabulary and binds
the admissibility, representative, and residue projections to that verdict.
It is still an instance contract: the model supplies the readers and the
profile supplies their coherence laws.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.StepVerdictModel

universe u v w x

inductive Outcome (Rep : Type w) (Residue : Type x) : Type (max w x)
  | accepted (representative : Rep)
  | reject (residue : Residue)
  | await (residue : Residue)
  | reepoch (residue : Residue)
  | fatal (residue : Residue)

structure Model where
  Raw : Type u
  Class : Type v
  Rep : Type w
  Residue : Type x
  q : Raw → Class
  evalRaw : Raw → Outcome Rep Residue
  evalClass : Class → Outcome Rep Residue
  active : Class → Bool
  admissible : Class → Bool
  rho : Class → Option Residue
  sigma : Class → Option Rep

structure Profile (M : Model) : Prop where
  quotient_factorization :
    ∀ raw, M.evalRaw raw = M.evalClass (M.q raw)
  admitted_iff_admit :
    ∀ cls,
      M.admissible cls = true ↔
        ∃ rep, M.evalClass cls = .accepted rep
  representative_iff_admit :
    ∀ cls rep,
      M.sigma cls = some rep ↔
        M.evalClass cls = .accepted rep
  active_nonadmitted_has_typed_residue :
    ∀ cls,
      M.active cls = true →
      M.admissible cls = false →
      ∃ residue,
        M.rho cls = some residue ∧
          (M.evalClass cls = .reject residue ∨
           M.evalClass cls = .await residue ∨
           M.evalClass cls = .reepoch residue ∨
           M.evalClass cls = .fatal residue)

theorem evalRaw_eq_evalClass
    {M : Model} (profile : Profile M) (raw : M.Raw) :
    M.evalRaw raw = M.evalClass (M.q raw) :=
  profile.quotient_factorization raw

theorem admitted_iff_admit
    {M : Model} (profile : Profile M) (cls : M.Class) :
    M.admissible cls = true ↔
      ∃ rep, M.evalClass cls = .accepted rep :=
  profile.admitted_iff_admit cls

theorem active_nonadmitted_has_typed_residue
    {M : Model} (profile : Profile M)
    {cls : M.Class}
    (active : M.active cls = true)
    (notAdmitted : M.admissible cls = false) :
    ∃ residue,
      M.rho cls = some residue ∧
        (M.evalClass cls = .reject residue ∨
         M.evalClass cls = .await residue ∨
         M.evalClass cls = .reepoch residue ∨
         M.evalClass cls = .fatal residue) :=
  profile.active_nonadmitted_has_typed_residue cls active notAdmitted

/-! ## Refinement to the original abstract Step-MST profile -/

def toStepExecModel (M : Model) : StepExecModel.Model where
  Raw := M.Raw
  Class := M.Class
  Rep := M.Rep
  Residue := M.Residue
  Outcome := Outcome M.Rep M.Residue
  q := M.q
  evalRaw := M.evalRaw
  evalClass := M.evalClass
  active := M.active
  admissible := M.admissible
  rho := M.rho
  sigma := M.sigma

theorem profile_to_step_exec_profile
    {M : Model} (profile : Profile M) :
    StepExecModel.Profile (toStepExecModel M) where
  quotient_factorization := profile.quotient_factorization
  representative_implies_admissible := by
    intro cls rep representative
    exact
      (profile.admitted_iff_admit cls).2
        ⟨rep, (profile.representative_iff_admit cls rep).1 representative⟩
  residue_totality := by
    intro cls active notAdmitted
    obtain ⟨residue, rhoProof, _⟩ :=
      profile.active_nonadmitted_has_typed_residue cls active notAdmitted
    exact ⟨residue, rhoProof⟩
  representative_precision := by
    intro cls active admitted
    obtain ⟨rep, accepted⟩ := (profile.admitted_iff_admit cls).1 admitted
    exact ⟨rep, (profile.representative_iff_admit cls rep).2 accepted⟩

end Residua.RCC.StepVerdictModel

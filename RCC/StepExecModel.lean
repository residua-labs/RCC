/-!
# RCC Step ExecModel / Tier-1 profile

This is the generic quotient/profile surface that the RC-1 StepSurface can
later instantiate.  It deliberately does not claim that a concrete RC-1
surface already supplies raw attempts, quotient classes, or typed residues.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.StepExecModel

universe u v w x y

/-- The five carriers and the four semantic projections of one step model. -/
structure Model where
  Raw : Type u
  Class : Type v
  Rep : Type w
  Residue : Type x
  Outcome : Type y
  q : Raw → Class
  evalRaw : Raw → Outcome
  evalClass : Class → Outcome
  active : Class → Bool
  admissible : Class → Bool
  rho : Class → Option Residue
  sigma : Class → Option Rep

/-- Tier-1 profile: the four laws are supplied independently by an instance. -/
structure Profile (M : Model) : Prop where
  quotient_factorization :
    ∀ raw, M.evalRaw raw = M.evalClass (M.q raw)
  representative_implies_admissible :
    ∀ cls rep, M.sigma cls = some rep → M.admissible cls = true
  residue_totality :
    ∀ cls,
      M.active cls = true →
      M.admissible cls = false →
      ∃ residue, M.rho cls = some residue
  representative_precision :
    ∀ cls,
      M.active cls = true →
      M.admissible cls = true →
      ∃ rep, M.sigma cls = some rep

theorem evalRaw_eq_evalClass
    {M : Model} (profile : Profile M) (raw : M.Raw) :
    M.evalRaw raw = M.evalClass (M.q raw) :=
  profile.quotient_factorization raw

theorem sigma_some_implies_admissible
    {M : Model} (profile : Profile M)
    {cls : M.Class} {rep : M.Rep}
    (representative : M.sigma cls = some rep) :
    M.admissible cls = true :=
  profile.representative_implies_admissible cls rep representative

theorem active_nonadmitted_has_residue
    {M : Model} (profile : Profile M)
    {cls : M.Class}
    (active : M.active cls = true)
    (notAdmitted : M.admissible cls = false) :
    ∃ residue, M.rho cls = some residue :=
  profile.residue_totality cls active notAdmitted

theorem active_admitted_has_representative
    {M : Model} (profile : Profile M)
    {cls : M.Class}
    (active : M.active cls = true)
    (admitted : M.admissible cls = true) :
    ∃ rep, M.sigma cls = some rep :=
  profile.representative_precision cls active admitted

end Residua.RCC.StepExecModel

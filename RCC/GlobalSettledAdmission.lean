import RCC.AdmissionLinearizer

/-!
# RCC-43 — globally settled admission

`GloballySuccessfulFinalize` proves membership in the versioned canonical CAS
evolution but does not settle an external effect or record durable history.
`SettledAdmission` binds effect settlement and canonical-history membership to
one actual local finalizer run but, by itself, does not prove that the writer
snapshot belongs to the global linearizer.

This module closes that formal product without accepting two detachable
finality runs.  One `GloballySettledAdmission` extends the exact
`SettledAdmission` and adds the canonical snapshot for its own writer state.
The global finality certificate is then mechanically reconstructed from the
same `finalizeRequest` and `finalizeSuccess`.

This carrier is intentionally for external-effect admissions.  Pure
history-only transitions require a separate completion branch rather than a
fabricated external effect.  Moreover, `durableContains` and effect
observations remain abstract instance predicates; production durability and
physical-world authenticity still require runtime-refinement bindings.

Prelude-only Lean 4.14; no Mathlib, custom postulates, or proof placeholders.
-/

namespace Residua.RCC.GlobalSettledAdmission

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer

universe u

/--
One RCC-43 external-effect admission whose exact writer snapshot is also a
member of the global RCC-42 linearizer evolution.
-/
structure GloballySettledAdmission
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence)
    (version : Version)
    (proposal : Proposal Slot Head Judgment)
    extends SettledAdmission environment proposal where
  canonicalSnapshot :
    CanonicalWriterSnapshot
      linearizer version environment.writerState

/--
Global finality is derived from the same request and local success already
bound to the effect and history records; no second finality run is accepted.
-/
def GloballySettledAdmission.toGloballySuccessfulFinalize
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    (admission :
      GloballySettledAdmission linearizer version proposal) :
    GloballySuccessfulFinalize
      linearizer version environment.writerState
        admission.finalizeRequest where
  snapshot := admission.canonicalSnapshot
  localSuccess := admission.finalizeSuccess

/-- Every globally settled external-effect admission has terminal effect phase. -/
theorem GloballySettledAdmission.effect_terminal
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    (admission :
      GloballySettledAdmission linearizer version proposal) :
    Residua.RCC.EffectSettlement.EffectPhase.IsTerminal
      environment.effectSnapshot.policyTerminalFailure
      admission.effectReceipt.phase :=
  settled_admission_effect_terminal admission.toSettledAdmission

/-- Every globally settled admission has durable canonical-history membership. -/
theorem GloballySettledAdmission.history_durable
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    (admission :
      GloballySettledAdmission linearizer version proposal) :
    environment.historySnapshot.durableContains admission.history.event :=
  settled_admission_history_durable admission.toSettledAdmission

/-- Pre-state authorization remains bound to the same globally settled proposal. -/
theorem GloballySettledAdmission.authorized
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ Version : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version
          environment.writerSpec environment.equivalence}
    {version : Version}
    {proposal : Proposal Slot Head Judgment}
    (admission :
      GloballySettledAdmission linearizer version proposal) :
    AuthorizedWithReceipt Slot Head Judgment AuthorityEvidence proposal :=
  settled_admission_implies_authorized admission.toSettledAdmission

end Residua.RCC.GlobalSettledAdmission

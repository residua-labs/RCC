import RCCTests.ProofCarryingOutcome

/-! RCC-86 candidate: proof-carrying four-way outcome semantics. -/

namespace Residua.RCC.RCC86Target

open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingOutcome.Tests

def admittedStepCloses := one_admitted_step_closes
def coreExact := demo_core_exact
def decreasingJumpRefused := arbitrary_decreasing_jump_without_event_refused
def selectedAdvanceAdmitted := selected_advance_is_admitted
def awaitCarriesWake := await_carries_wake
def reepochCarriesConservation := reepoch_carries_conservation
def reepochWithoutConservationRefused := reepoch_without_conservation_refused
def haltCarriesNamedFailure := halt_carries_named_failure
def omittedAdvanceReaderIncomplete := omitted_advance_reader_is_not_complete
def genericCoreNeedsAdapter := generic_core_still_needs_semantic_packet_adapter

structure Certificate where
  admittedStepCloses :
    ProofCarryingOutcome.normalize demoSystem .pending =
      .closed .done .done
  awaitCarriesWake :
    ∃ certificate,
      ProofCarryingOutcome.normalize awaitSystem .pending =
        .await .pending certificate
  reepochCarriesConservation :
    ∃ certificate : DemoMigration .done,
      ProofCarryingOutcome.normalize reepochSystem .done =
        .reepoch .done certificate
  haltCarriesNamedFailure :
    ∃ certificate : DemoFailure .pending,
      ProofCarryingOutcome.normalize haltSystem .pending =
        .halt .pending certificate
  decreasingJumpRefused :
    ¬ Nonempty (DemoAdvance .pending .rogue)
  selectedAdvanceAdmitted :
    ∀ certificate,
      deriveOpen demoSystem .pending =
        .advanced .done certificate (by decide) →
      DemoAdmission .pending .done
  reepochWithoutConservationRefused :
    ¬ Nonempty (DemoMigration .pending)

def certificate : Certificate where
  admittedStepCloses := one_admitted_step_closes
  awaitCarriesWake := await_carries_wake
  reepochCarriesConservation := reepoch_carries_conservation
  haltCarriesNamedFailure := halt_carries_named_failure
  decreasingJumpRefused := decreasingJumpRefused.2
  selectedAdvanceAdmitted := selectedAdvanceAdmitted
  reepochWithoutConservationRefused := reepochWithoutConservationRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC86Target

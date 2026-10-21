import RCCTests.ProofCarryingOutcome

/-! E1 candidate: the executable outcome kernel derives exactly the four
    proof-carrying final branches, recurses only through admitted decreases,
    and refuses hidden continuations when reader completeness is absent. -/

namespace Residua.RCC.E1Target

open Residua.RCC.ProofCarryingOutcome
open Residua.RCC.ProofCarryingOutcome.Tests

structure Certificate where
  admittedStepCloses :
    Residua.RCC.ProofCarryingOutcome.normalize demoSystem .pending =
      .closed .done .done
  awaitCarriesWake :
    ∃ certificate,
      Residua.RCC.ProofCarryingOutcome.normalize awaitSystem .pending =
        .await .pending certificate
  reepochCarriesConservation :
    ∃ certificate : DemoMigration .done,
      Residua.RCC.ProofCarryingOutcome.normalize reepochSystem .done =
        .reepoch .done certificate
  haltCarriesFailure :
    ∃ certificate : DemoFailure .pending,
      Residua.RCC.ProofCarryingOutcome.normalize haltSystem .pending =
        .halt .pending certificate
  readerCompletenessBlocksOmittedAdvance :
    ¬ BranchReadersComplete omittedAdvanceSystem
  coreFixedPointExact :
    (Residua.RCC.ProofCarryingOutcome.coreObject demoSystem).Exact

def certificate : Certificate where
  admittedStepCloses := one_admitted_step_closes
  awaitCarriesWake := await_carries_wake
  reepochCarriesConservation := reepoch_carries_conservation
  haltCarriesFailure := halt_carries_named_failure
  readerCompletenessBlocksOmittedAdvance := omitted_advance_reader_is_not_complete
  coreFixedPointExact := demo_core_exact

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.E1Target

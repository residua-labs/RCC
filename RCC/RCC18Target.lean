import RCCTests.PrimitiveOperationalTotality

/-!
# RCC-18 target package

This package seals the parametric primitive operational boundary: all declared
primitive observations classify into `Ok`, `Await`, `Refuse`, or
`ResourceExhausted`, and an insufficient contract is explicitly resource
exhausted.  It deliberately does not claim that arbitrary host processes or
network operations terminate; runtime adapter refinement remains outside this
target.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RCC18Target

open Residua.RCC
open Residua.RCC.PrimitiveOperationalTotalityTests

structure ConcreteWitness : Prop where
  fourWay :
    ∀ primitive,
      (∃ value, execute demoFamily primitive demoContract () = .Ok value) ∨
        (∃ wake, execute demoFamily primitive demoContract () = .Await wake) ∨
        (∃ residue, execute demoFamily primitive demoContract () = .Refuse residue) ∨
        (∃ residue,
          execute demoFamily primitive demoContract () = .ResourceExhausted residue)
  exhausted :
    ∀ primitive,
      execute demoFamily primitive exhaustedContract () =
        .ResourceExhausted .fuelDepleted
  timeoutIsResource :
    execute demoFamily .BinaryMeasurement demoContract () =
      .ResourceExhausted .processTimeout
  exceptionIsRefused :
    execute demoFamily .EffectAppend demoContract () =
      .Refuse .caughtException

structure MutantRefusal : Prop where
  silentTimeoutRefused :
    ¬ ClassifierConforms
      (silentTimeoutMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue))
  exhaustionDoesNotClose :
    ¬ (OpResult.IsResourceExhausted
          (execute demoFamily .BinaryMeasurement demoContract ()) →
        DemoClosed .open)

structure Certificate : Prop where
  witness : ConcreteWitness
  mutants : MutantRefusal

def certificate : Certificate where
  witness :=
    { fourWay := every_declared_primitive_has_four_way_boundary
      exhausted := exhausted_contract_returns_resource_exhausted
      timeoutIsResource := binary_measurement_timeout_is_resource_exhausted
      exceptionIsRefused := effect_append_exception_is_refused }
  mutants :=
    { silentTimeoutRefused := silent_timeout_countermodel_rejected
      exhaustionDoesNotClose := timeout_does_not_close_open_state }

theorem rcc18_certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

theorem rcc18_boundary
    (primitive : PrimitiveKind) :
    ((∃ value, execute demoFamily primitive exhaustedContract () = .Ok value) ∨
        (∃ wake, execute demoFamily primitive exhaustedContract () = .Await wake) ∨
        (∃ residue, execute demoFamily primitive exhaustedContract () = .Refuse residue) ∨
        (∃ residue,
          execute demoFamily primitive exhaustedContract () =
            .ResourceExhausted residue)) ∧
      (demoPolicy.insufficient primitive exhaustedContract →
        ∃ residue,
          execute demoFamily primitive exhaustedContract () =
            .ResourceExhausted residue) :=
  rcc18_parametric_boundary
    demoPolicy demoFamily demoFamilyLawful primitive exhaustedContract ()

end Residua.RCC.RCC18Target


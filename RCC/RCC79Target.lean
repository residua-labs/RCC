import RCCTests.PrimitiveInvocationCoverage

/-! RCC-79 candidate: complete primitive invocation and runtime coverage. -/

namespace Residua.RCC.RCC79Target

open Residua.RCC.PrimitiveInvocationCoverage.Tests
open Residua.RCC.PrimitiveInvocationCoverage
open Residua.RCC
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.FacetCoherence

def everyInvocationCovered := positive_every_actual_is_total_refined_runtime_bound
def hiddenInvocationRefused := one_good_hides_bad_second
def runtimeStepMismatchRefused := actual_not_runtimeStep
def vacuousRuntimeRefused := vacuous_runtime_relation
def underdeclaredUniverseRefused := underdeclared_universe

structure Certificate where
  everyInvocationCovered :
    ∀ (invocation : Invocation),
      ∃ refinement : ActualInvocationRefinementAt family,
        refinement.invocation = actualInvocation ∧
        InvocationReturned refinement.invocation ∧
        allRuntimeWorld.runtimeStep (beforeAt invocation) (afterAt invocation) ∧
        Nonempty (FormalOrMeasuredAt fullSystem () invocation)
  hiddenInvocationRefused :
    ¬ Nonempty
      (ExhaustiveInvocationCoverageAt
        fullSystem () oneGoodOnlyEvidence)
  runtimeStepMismatchRefused :
    ¬ Nonempty
      (ActualInvocationPacketAt onlyGoodRuntimeSystem () .bad)
  vacuousRuntimeRefused :
    ¬ Nonempty
      (ActualInvocationPacketAt vacuousRuntimeSystem () .good)
  underdeclaredUniverseRefused :
    ¬ InvocationUniverseSeal underdeclaredSystem ()

def certificate : Certificate where
  everyInvocationCovered := positive_every_actual_is_total_refined_runtime_bound
  hiddenInvocationRefused := hiddenInvocationRefused
  runtimeStepMismatchRefused := runtimeStepMismatchRefused
  vacuousRuntimeRefused := vacuousRuntimeRefused
  underdeclaredUniverseRefused := underdeclaredUniverseRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC79Target

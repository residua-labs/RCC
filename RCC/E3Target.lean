import RCCTests.PrimitiveInvocationCoverage

/-! E3 candidate: every in-scope primitive invocation has one exact packet,
    runtime binding, and formal/measured receipt; omissions and mismatches
    remain typed residues rather than disappearing from the frontier. -/

namespace Residua.RCC.E3Target

open Residua.RCC.PrimitiveInvocationCoverage.Tests
open Residua.RCC.PrimitiveInvocationCoverage
open Residua.RCC.ClosurePrerequisites

structure Certificate where
  everyActualInvocationBound :
    ∀ invocation : Invocation,
      ∃ refinement : ActualInvocationRefinementAt family,
        refinement.invocation = actualInvocation ∧
        InvocationReturned refinement.invocation ∧
        allRuntimeWorld.runtimeStep (beforeAt invocation) (afterAt invocation) ∧
        Nonempty (FormalOrMeasuredAt fullSystem () invocation)
  omittedPacketRejected :
    ¬ Nonempty
      (ExhaustiveInvocationCoverageAt
        fullSystem () oneGoodOnlyEvidence)
  runtimeMismatchRejected :
    ¬ Nonempty
      (ActualInvocationPacketAt onlyGoodRuntimeSystem () .bad)
  vacuousRuntimeRejected :
    ¬ Nonempty
      (ActualInvocationPacketAt vacuousRuntimeSystem () .good)
  underdeclaredUniverseRejected :
    ¬ InvocationUniverseSeal underdeclaredSystem ()

def certificate : Certificate where
  everyActualInvocationBound :=
    positive_every_actual_is_total_refined_runtime_bound
  omittedPacketRejected := one_good_hides_bad_second
  runtimeMismatchRejected := actual_not_runtimeStep
  vacuousRuntimeRejected := vacuous_runtime_relation
  underdeclaredUniverseRejected := underdeclared_universe

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.E3Target

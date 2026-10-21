import RCC.SeamAssumptionAdapter
import RCCTests.SeamExactness

namespace Residua.RCC.SeamAssumptionAdapter.Tests

open Residua.RCC.SeamExactness
open Residua.RCC.SeamAssumptionAdapter

inductive Assumption
  | clock
  deriving DecidableEq, Repr

namespace Positive

def dependencies (value : Bool) : List Assumption :=
  if value then [.clock] else []

abbrev binding :
    AssumptionSeamBinding SeamExactness.Tests.Identity.world where
  Assumption := Assumption
  sourceActive := fun root assumption =>
    root =
        SeamExactness.Tests.Identity.world.sourceAssumptionRoot ∧
      assumption = Assumption.clock
  targetActive := fun root assumption =>
    root =
        SeamExactness.Tests.Identity.world.targetAssumptionRoot ∧
      assumption = Assumption.clock
  sourceDependencies := dependencies
  targetDependencies := dependencies

def assumptionSeam :
    ExactAssumptionSeamAt
      SeamExactness.Tests.Identity.world binding where
  exact := SeamExactness.Tests.Identity.exactSeam
  activeExact := by
    intro assumption
    constructor
    · intro active
      exact ⟨rfl, active.2⟩
    · intro active
      exact ⟨rfl, active.2⟩
  dependenciesExact := by
    intro source assumption
    cases source <;> cases assumption <;>
      constructor <;> intro listed <;> exact listed

end Positive

theorem active_dependency_transports_to_target :
    Assumption.clock ∈
        Positive.binding.targetDependencies
          (SeamExactness.Tests.Identity.world.encode true) ∧
      Positive.binding.targetActive
        SeamExactness.Tests.Identity.world.targetAssumptionRoot
        .clock :=
  Positive.assumptionSeam.transportActiveDependency
    (source := true)
    (assumption := Assumption.clock)
    (List.Mem.head [])
    ⟨rfl, rfl⟩

namespace InactiveTarget

abbrev binding :
    AssumptionSeamBinding SeamExactness.Tests.Identity.world where
  Assumption := Assumption
  sourceActive := fun root assumption =>
    root =
        SeamExactness.Tests.Identity.world.sourceAssumptionRoot ∧
      assumption = Assumption.clock
  targetActive := fun _ _ => False
  sourceDependencies := Positive.dependencies
  targetDependencies := Positive.dependencies

end InactiveTarget

/-- Equal root identifiers cannot hide an inactive target dependency. -/
theorem root_equality_alone_does_not_transport_activity :
    ¬ ExactAssumptionSeamAt
      SeamExactness.Tests.Identity.world
      InactiveTarget.binding := by
  intro seam
  exact (seam.activeExact Assumption.clock).mp ⟨rfl, rfl⟩

namespace OmittedDependency

abbrev binding :
    AssumptionSeamBinding SeamExactness.Tests.Identity.world where
  Assumption := Assumption
  sourceActive := fun root assumption =>
    root =
        SeamExactness.Tests.Identity.world.sourceAssumptionRoot ∧
      assumption = Assumption.clock
  targetActive := fun root assumption =>
    root =
        SeamExactness.Tests.Identity.world.targetAssumptionRoot ∧
      assumption = Assumption.clock
  sourceDependencies := Positive.dependencies
  targetDependencies := fun _ => []

end OmittedDependency

/-- An encoded target cannot silently omit a source certificate dependency. -/
theorem omitted_target_dependency_is_refused :
    ¬ ExactAssumptionSeamAt
      SeamExactness.Tests.Identity.world
      OmittedDependency.binding := by
  intro seam
  have sourceListed :
      Assumption.clock ∈
        OmittedDependency.binding.sourceDependencies true := by
    exact List.Mem.head []
  have targetListed :=
    (seam.dependenciesExact true Assumption.clock).mp sourceListed
  cases targetListed

end Residua.RCC.SeamAssumptionAdapter.Tests

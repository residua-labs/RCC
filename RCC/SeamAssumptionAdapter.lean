import RCC.SeamExactness

/-!
# C2 seam assumption adapter

Equal assumption-root coordinates do not prove that two components interpret
the root alike.  This adapter adds two exact boundary laws:

* the active assumption predicate agrees at both endpoint roots; and
* the dependency list of each transported source output agrees with the
  dependency list of its encoded target input.

The resulting theorem transports an actual active dependency, not merely a
root identifier.  Completeness of dependency extraction inside either
component remains an instance obligation outside this adapter.
-/

namespace Residua.RCC.SeamAssumptionAdapter

open Residua.RCC.SeamExactness

universe u

/-- Active assumptions and certificate dependencies at both seam endpoints. -/
structure AssumptionSeamBinding (world : SeamWorld) where
  Assumption : Type u
  sourceActive :
    world.AssumptionRoot → Assumption → Prop
  targetActive :
    world.AssumptionRoot → Assumption → Prop
  sourceDependencies :
    world.SourceOutput → List Assumption
  targetDependencies :
    world.TargetInput → List Assumption

/--
The exact active-context and dependency interpretation carried by one exact
seam.
-/
structure ExactAssumptionSeamAt
    (world : SeamWorld)
    (binding : AssumptionSeamBinding world) : Prop where
  exact : ExactSeamAt world
  activeExact :
    ∀ assumption,
      binding.sourceActive world.sourceAssumptionRoot assumption ↔
        binding.targetActive world.targetAssumptionRoot assumption
  dependenciesExact :
    ∀ source assumption,
      assumption ∈ binding.sourceDependencies source ↔
        assumption ∈
          binding.targetDependencies (world.encode source)

/--
An active source dependency crosses the seam as both a listed and active
target dependency.
-/
theorem ExactAssumptionSeamAt.transportActiveDependency
    {world : SeamWorld}
    {binding : AssumptionSeamBinding world}
    (seam : ExactAssumptionSeamAt world binding)
    {source : world.SourceOutput}
    {assumption : binding.Assumption}
    (listed :
      assumption ∈ binding.sourceDependencies source)
    (active :
      binding.sourceActive
        world.sourceAssumptionRoot assumption) :
    assumption ∈
        binding.targetDependencies (world.encode source) ∧
      binding.targetActive
        world.targetAssumptionRoot assumption :=
  ⟨(seam.dependenciesExact source assumption).mp listed,
    (seam.activeExact assumption).mp active⟩

/-- Dependency and activity transport is reversible at the exact seam. -/
theorem ExactAssumptionSeamAt.reflectActiveDependency
    {world : SeamWorld}
    {binding : AssumptionSeamBinding world}
    (seam : ExactAssumptionSeamAt world binding)
    {source : world.SourceOutput}
    {assumption : binding.Assumption}
    (listed :
      assumption ∈
        binding.targetDependencies (world.encode source))
    (active :
      binding.targetActive
        world.targetAssumptionRoot assumption) :
    assumption ∈ binding.sourceDependencies source ∧
      binding.sourceActive
        world.sourceAssumptionRoot assumption :=
  ⟨(seam.dependenciesExact source assumption).mpr listed,
    (seam.activeExact assumption).mpr active⟩

end Residua.RCC.SeamAssumptionAdapter

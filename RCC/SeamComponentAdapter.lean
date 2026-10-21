import RCC.FormalCore
import RCC.SeamExactness

/-!
# C2 seam-to-component adapter

`ExactSeamAt` certifies one semantic and realization boundary.  A component
transition system has two additional obligations: the encoding must preserve
each step, and a closed source endpoint must remain closed at the target.

This adapter keeps those obligations explicit and mechanically constructs the
existing `FormalCore.Seam`.  The local exactness kernel therefore cannot be
substituted for component closure preservation.

Active-assumption transport, concrete writer fencing, and composition-family
enumeration remain separate C2 integration obligations.
-/

namespace Residua.RCC.SeamComponentAdapter

open Residua.RCC
open Residua.RCC.SeamExactness

universe u

/-- The component transition and closure predicates at both seam endpoints. -/
structure ComponentRelationBinding (world : SeamWorld) where
  sourceStep :
    world.SourceOutput → world.SourceOutput → Prop
  targetStep :
    world.TargetInput → world.TargetInput → Prop
  sourceClosed :
    world.SourceOutput → Prop
  targetClosed :
    world.TargetInput → Prop

/-- The source relation induced by a component binding. -/
def ComponentRelationBinding.sourceRel
    {world : SeamWorld}
    (binding : ComponentRelationBinding world) :
    Rel where
  State := world.SourceOutput
  step := binding.sourceStep
  closed := binding.sourceClosed

/-- The target relation induced by a component binding. -/
def ComponentRelationBinding.targetRel
    {world : SeamWorld}
    (binding : ComponentRelationBinding world) :
    Rel where
  State := world.TargetInput
  step := binding.targetStep
  closed := binding.targetClosed

/--
One seam exactness certificate plus the two component-level preservation
laws needed by `FormalCore.Seam`.
-/
structure ExactComponentSeamAt
    (world : SeamWorld)
    (binding : ComponentRelationBinding world) : Prop where
  exact : ExactSeamAt world
  stepPreserved :
    ∀ {source target},
      binding.sourceStep source target →
      binding.targetStep (world.encode source) (world.encode target)
  closedPreserved :
    ∀ {source},
      binding.sourceClosed source →
      binding.targetClosed (world.encode source)

/--
The adapter headline: a proof-carrying exact component seam constructs the
existing formal seam object without caller-supplied status.
-/
def ExactComponentSeamAt.toFormalSeam
    {world : SeamWorld}
    {binding : ComponentRelationBinding world}
    (componentSeam : ExactComponentSeamAt world binding) :
    Seam binding.sourceRel binding.targetRel where
  map := world.encode
  closedPreserved := componentSeam.closedPreserved
  stepPreserved := componentSeam.stepPreserved

/-- The formal seam retains the exact source-to-target encoding. -/
theorem ExactComponentSeamAt.formalMapExact
    {world : SeamWorld}
    {binding : ComponentRelationBinding world}
    (componentSeam : ExactComponentSeamAt world binding)
    (source : world.SourceOutput) :
    componentSeam.toFormalSeam.map source = world.encode source :=
  rfl

end Residua.RCC.SeamComponentAdapter

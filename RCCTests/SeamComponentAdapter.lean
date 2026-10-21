import RCC.SeamComponentAdapter
import RCCTests.SeamExactness

namespace Residua.RCC.SeamComponentAdapter.Tests

open Residua.RCC
open Residua.RCC.SeamExactness
open Residua.RCC.SeamComponentAdapter

namespace Positive

def binding :
    ComponentRelationBinding SeamExactness.Tests.Identity.world where
  sourceStep := fun source target =>
    source = false ∧ target = true
  targetStep := fun source target =>
    source = false ∧ target = true
  sourceClosed := fun source =>
    source = true
  targetClosed := fun target =>
    target = true

def componentSeam :
    ExactComponentSeamAt
      SeamExactness.Tests.Identity.world binding where
  exact := SeamExactness.Tests.Identity.exactSeam
  stepPreserved := fun step => step
  closedPreserved := fun closed => closed

end Positive

theorem exact_component_seam_constructs_formal_core_seam :
    Nonempty
      (Seam
        Positive.binding.sourceRel
        Positive.binding.targetRel) :=
  ⟨Positive.componentSeam.toFormalSeam⟩

theorem exact_component_seam_preserves_concrete_step :
    Positive.binding.targetStep
      (Positive.componentSeam.toFormalSeam.map false)
      (Positive.componentSeam.toFormalSeam.map true) :=
  Positive.componentSeam.toFormalSeam.stepPreserved ⟨rfl, rfl⟩

theorem exact_component_seam_preserves_concrete_closure :
    Positive.binding.targetClosed
      (Positive.componentSeam.toFormalSeam.map true) :=
  Positive.componentSeam.toFormalSeam.closedPreserved rfl

namespace MissingClosure

def binding :
    ComponentRelationBinding SeamExactness.Tests.Identity.world where
  sourceStep := Positive.binding.sourceStep
  targetStep := Positive.binding.targetStep
  sourceClosed := Positive.binding.sourceClosed
  targetClosed := fun _ => False

end MissingClosure

/--
Even a live semantic exactness certificate cannot replace the missing
component closure-preservation law.
-/
theorem semantic_exactness_alone_cannot_construct_component_seam :
    ¬ ExactComponentSeamAt
      SeamExactness.Tests.Identity.world
      MissingClosure.binding := by
  intro componentSeam
  exact componentSeam.closedPreserved (source := true) rfl

end Residua.RCC.SeamComponentAdapter.Tests

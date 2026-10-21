import RCC.ComponentClosureFamily
import RCCTests.ComponentClosurePreservation
import RCCTests.FacetCoherence

namespace Residua.RCC.ComponentClosureFamily.Tests

open Residua.RCC
open Residua.RCC.ComponentClosureFamily
open Residua.RCC.FacetCoherence

namespace Positive

abbrev World := FacetCoherence.Tests.world

def binding : CoherenceComponentBinding World where
  sourceRel := fun _ =>
    ComponentClosurePreservation.Tests.source
  targetRel := fun _ =>
    ComponentClosurePreservation.Tests.source
  seam := fun _ =>
    ComponentClosurePreservation.Tests.identitySeam
  terminalSound := by
    intro component start finish trace
    cases component
    · exact .left
    · exact .right

def realization
    (component : World.Component) :
    ComponentClosureRealization binding component where
  start := .zero
  finish := .one
  trace := ComponentClosurePreservation.Tests.sourceClosedTrace

def family : ClosedComponentFamily binding where
  realization := by
    intro component listed
    exact realization component

end Positive

theorem c1_trace_family_closes_left_component :
    Positive.World.componentClosed
      FacetCoherence.Tests.Component.left :=
  Positive.family.componentsClosed
    .left
    (List.Mem.head _)

theorem c1_trace_family_closes_right_component :
    Positive.World.componentClosed
      FacetCoherence.Tests.Component.right :=
  Positive.family.componentsClosed
    .right
    (List.Mem.tail _ (List.Mem.head _))

theorem c1_trace_family_retains_mapped_target_trace :
    (Positive.binding.targetRel FacetCoherence.Tests.Component.left).ClosedTrace
      ((Positive.binding.seam .left).map
        (Positive.realization .left).start)
      ((Positive.binding.seam .left).map
        (Positive.realization .left).finish) :=
  (Positive.realization .left).targetTrace

/--
The existing C1 mutant shows that step preservation without target closure
cannot supply the formal seam required by a component realization.
-/
theorem step_only_mapping_cannot_form_component_realization_seam :
    ¬ Nonempty
      (Seam
        ComponentClosurePreservation.Tests.source
        ComponentClosurePreservation.Tests.targetWithoutClosure) :=
  ComponentClosurePreservation.Tests.step_only_mapping_cannot_preserve_component_closure

def falseComponentWorld : CoherenceWorld :=
  { FacetCoherence.Tests.world with
    componentClosed := fun _ => False
    globalClosed := False }

/--
A valid C1 trace family cannot manufacture an unrelated false legacy
component predicate through `terminalSound`.
-/
theorem trace_family_cannot_realize_false_component_predicate
    (binding : CoherenceComponentBinding falseComponentWorld) :
    ClosedComponentFamily binding →
      False := by
  intro family
  exact
    family.componentsClosed
      FacetCoherence.Tests.Component.left
      (List.Mem.head _)

end Residua.RCC.ComponentClosureFamily.Tests

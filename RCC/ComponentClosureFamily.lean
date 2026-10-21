import RCC.ComponentClosurePreservation
import RCC.FacetCoherence

/-!
# C1 component closure family

C1 transports one finite closed trace through one component seam.  Composition
needs that evidence for every component listed by one `CoherenceWorld`.

This module retains each trace, seam, and endpoint as projectable data, then
derives the abstract `world.componentClosed` predicate through an explicit
instance adapter.  It does not discover the production component universe or
bind the trace to a runtime snapshot.
-/

namespace Residua.RCC.ComponentClosureFamily

open Residua.RCC
open Residua.RCC.FacetCoherence

universe u

/--
The fixed relation interpretation of every declared component.

`terminalSound` is the explicit instance adapter from a complete mapped
target trace to the local predicate consumed by composition.
-/
structure CoherenceComponentBinding (world : CoherenceWorld.{u}) where
  sourceRel : world.Component → Rel.{u}
  targetRel : world.Component → Rel.{u}
  seam :
    ∀ component,
      Seam (sourceRel component) (targetRel component)
  terminalSound :
    ∀ component
      {start finish : (sourceRel component).State},
      (targetRel component).ClosedTrace
        ((seam component).map start)
        ((seam component).map finish) →
      world.componentClosed component

/-- One finite source trace at the fixed component interpretation. -/
structure ComponentClosureRealization
    {world : CoherenceWorld.{u}}
    (binding : CoherenceComponentBinding world)
    (component : world.Component) where
  start : (binding.sourceRel component).State
  finish : (binding.sourceRel component).State
  trace :
    (binding.sourceRel component).ClosedTrace start finish

/-- The exact target trace produced by C1. -/
def ComponentClosureRealization.targetTrace
    {world : CoherenceWorld}
    {binding : CoherenceComponentBinding world}
    {component : world.Component}
    (realization : ComponentClosureRealization binding component) :
    (binding.targetRel component).ClosedTrace
      ((binding.seam component).map realization.start)
      ((binding.seam component).map realization.finish) :=
  (binding.seam component).closedTracePreserved realization.trace

/-- C1 derives the listed component's local closure proposition. -/
theorem ComponentClosureRealization.closed
    {world : CoherenceWorld}
    {binding : CoherenceComponentBinding world}
    {component : world.Component}
    (realization : ComponentClosureRealization binding component) :
    world.componentClosed component :=
  binding.terminalSound component realization.targetTrace

/--
Projectable C1 evidence for every component in the declared coherence list.
-/
structure ClosedComponentFamily
    {world : CoherenceWorld.{u}}
    (binding : CoherenceComponentBinding world) where
  realization :
    ∀ component,
      component ∈ world.components →
      ComponentClosureRealization binding component

/-- Every listed component is closed by its retained C1 trace. -/
theorem ClosedComponentFamily.componentsClosed
    {world : CoherenceWorld}
    {binding : CoherenceComponentBinding world}
    (family : ClosedComponentFamily binding)
    (component : world.Component)
    (listed : component ∈ world.components) :
    world.componentClosed component :=
  (family.realization component listed).closed

end Residua.RCC.ComponentClosureFamily

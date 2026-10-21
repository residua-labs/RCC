import RCCTests.ComponentClosureFamily

/-! C1 candidate: a closed component is obtained from a mapped target trace
    through an explicit seam-preserving realization, not from a step-only
    relation or an unrelated caller-supplied predicate. -/

namespace Residua.RCC.C1Target

open Residua.RCC
open Residua.RCC.ComponentClosureFamily.Tests
open Residua.RCC.ComponentClosureFamily
open Residua.RCC.ComponentClosurePreservation
open Residua.RCC.FacetCoherence

structure Certificate where
  leftComponentClosed :
    Positive.World.componentClosed
      Residua.RCC.FacetCoherence.Tests.Component.left
  rightComponentClosed :
    Positive.World.componentClosed
      Residua.RCC.FacetCoherence.Tests.Component.right
  mappedTargetTraceRetained :
    (Positive.binding.targetRel Residua.RCC.FacetCoherence.Tests.Component.left).ClosedTrace
      ((Positive.binding.seam .left).map (Positive.realization .left).start)
      ((Positive.binding.seam .left).map (Positive.realization .left).finish)
  stepOnlyRejected :
    ¬ Nonempty
      (Seam
        ComponentClosurePreservation.Tests.source
        ComponentClosurePreservation.Tests.targetWithoutClosure)
  falsePredicateRejected :
    ∀ binding : CoherenceComponentBinding falseComponentWorld,
      ClosedComponentFamily binding → False

def certificate : Certificate where
  leftComponentClosed := c1_trace_family_closes_left_component
  rightComponentClosed := c1_trace_family_closes_right_component
  mappedTargetTraceRetained := c1_trace_family_retains_mapped_target_trace
  stepOnlyRejected := step_only_mapping_cannot_form_component_realization_seam
  falsePredicateRejected := trace_family_cannot_realize_false_component_predicate

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.C1Target

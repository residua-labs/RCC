import RCC.FormalCore

/-!
# C1 component closure preservation

A component seam transports more than an isolated terminal predicate. Every
edge of one finite relation trace is mapped into the target component, and the
terminal closure proof is transported at the same mapped endpoint.

This theorem is local to fixed relation objects. It does not prove seam
exactness, common-snapshot assembly, or global intent closure.
-/

namespace Residua.RCC

namespace Rel

/-- Finite reflexive-transitive closure of one component's step relation. -/
inductive Reaches (R : Rel) : R.State → R.State → Prop
  | refl (state : R.State) : Reaches R state state
  | tail {start next finish : R.State} :
      R.step start next →
      Reaches R next finish →
      Reaches R start finish

/-- A finite component trace whose exact endpoint is closed. -/
structure ClosedTrace
    (R : Rel) (start finish : R.State) : Prop where
  reaches : Reaches R start finish
  terminal : R.closed finish

end Rel

/-- Every finite source trace maps edge-for-edge through a component seam. -/
theorem Seam.reachesPreserved
    {A B : Rel}
    (seam : Seam A B)
    {start finish : A.State}
    (trace : A.Reaches start finish) :
    B.Reaches (seam.map start) (seam.map finish) := by
  induction trace with
  | refl state =>
      exact .refl (seam.map state)
  | tail step rest inductionHypothesis =>
      exact .tail (seam.stepPreserved step) inductionHypothesis

/--
C1 headline: a seam transports the entire finite trace and its terminal
component-closure proof.
-/
theorem Seam.closedTracePreserved
    {A B : Rel}
    (seam : Seam A B)
    {start finish : A.State}
    (trace : A.ClosedTrace start finish) :
    B.ClosedTrace (seam.map start) (seam.map finish) :=
  ⟨seam.reachesPreserved trace.reaches,
    seam.closedPreserved trace.terminal⟩

end Residua.RCC

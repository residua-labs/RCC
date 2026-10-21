import RCC.ClosurePrerequisites
import RCC.FacetCoherence

/-!
# RCC primitive invocation coverage

RCC-18 proves that one returned primitive invocation refines one projected
primitive family.  Closure needs a stronger, state-indexed statement: every
actual invocation in one sealed finite universe is refined and is represented
by the same-snapshot FC-2 runtime relation.

This module supplies that quantifier.  An instance may expose raw invocation
identities, actual returned values, runtime endpoints, and an evidence reader.
It may not report a packet-local `covered` bit.  An exhaustive certificate
must prove that the finite universe is nonempty and exact, and that the reader
returns a proof-carrying packet for every in-scope invocation.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.PrimitiveInvocationCoverage

open Residua.RCC
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.FacetCoherence

universe u

/--
The state-indexed raw surfaces used to enumerate and bind actual primitive
invocations.  `Invocation` is an occurrence identity, not the invocation's
value identity, so two equal calls remain two items in the coverage universe.
-/
structure PrimitiveInvocationSystem where
  Snapshot : Type u
  Invocation : Type u
  invocationDecidableEq : DecidableEq Invocation

  inScopeAt : Snapshot → Invocation → Prop
  invocationsAt : Snapshot → List Invocation

  policyAt : Snapshot → ResourcePolicy
  familyAt : Snapshot → PrimitiveFamily.{u, u, u, u}
  lawfulAt :
    ∀ snapshot,
      LawfulPrimitiveFamily (policyAt snapshot) (familyAt snapshot)
  actualAt :
    (snapshot : Snapshot) → Invocation →
      ActualPrimitiveInvocation (familyAt snapshot)

  worldAt : Snapshot → CoherenceWorld.{u}
  runtimeBeforeAt :
    (snapshot : Snapshot) → Invocation → (worldAt snapshot).RuntimeState
  runtimeAfterAt :
    (snapshot : Snapshot) → Invocation → (worldAt snapshot).RuntimeState

  MeasurementReceipt : Type u
  measuredReceiptAt :
    Snapshot → Invocation → Option MeasurementReceipt
  MeasurementBindsAt :
    Snapshot → Invocation → MeasurementReceipt → Prop

/--
The invocation enumeration is a sealed finite closed world.  Nonemptiness is
load-bearing: a system cannot establish primitive coverage by declaring no
actual invocations and choosing an empty runtime relation.
-/
structure InvocationUniverseSeal
    (S : PrimitiveInvocationSystem) (snapshot : S.Snapshot) : Prop where
  inScopeExists : ∃ invocation, S.inScopeAt snapshot invocation
  sound :
    ∀ invocation,
      invocation ∈ S.invocationsAt snapshot →
        S.inScopeAt snapshot invocation
  complete :
    ∀ invocation,
      S.inScopeAt snapshot invocation →
        invocation ∈ S.invocationsAt snapshot

/--
The formal/runtime bridge for one exact occurrence.  A direct bridge carries
the FC-2 formal reduction.  The measured branch exposes an explicit receipt
from the state-indexed reader and a binding proof; it is an auditable trust
boundary rather than an implicit ambient assumption.
-/
inductive FormalOrMeasuredAt
    (S : PrimitiveInvocationSystem)
    (snapshot : S.Snapshot)
    (invocation : S.Invocation) : Type u
  | formalStep
      (step :
        (S.worldAt snapshot).reduces
          ((S.worldAt snapshot).abstractState
            (S.runtimeBeforeAt snapshot invocation))
          ((S.worldAt snapshot).abstractState
            (S.runtimeAfterAt snapshot invocation)))
  | measured
      (receipt : S.MeasurementReceipt)
      (found :
        S.measuredReceiptAt snapshot invocation = some receipt)
      (bound :
        S.MeasurementBindsAt snapshot invocation receipt)

/--
One proof-carrying actual invocation packet.  Its refinement witness must name
the exact `actualAt` value selected by the invocation occurrence.  Its runtime
edge uses the exact same snapshot as the family, actual invocation, endpoints,
and formal/measured bridge.
-/
structure ActualInvocationPacketAt
    (S : PrimitiveInvocationSystem)
    (snapshot : S.Snapshot)
    (invocation : S.Invocation) where
  refinement : ActualInvocationRefinementAt (S.familyAt snapshot)
  invocationExact :
    refinement.invocation = S.actualAt snapshot invocation
  runtimeBound :
    (S.worldAt snapshot).runtimeStep
      (S.runtimeBeforeAt snapshot invocation)
      (S.runtimeAfterAt snapshot invocation)
  formalOrMeasured : FormalOrMeasuredAt S snapshot invocation

/--
An instance exposes an evidence reader.  The reader's codomain is already a
proof-carrying packet; it cannot return a detached `refined := true`.
-/
structure InvocationEvidenceWindowAt
    (S : PrimitiveInvocationSystem)
    (snapshot : S.Snapshot) where
  packetAt :
    (invocation : S.Invocation) →
      Option (ActualInvocationPacketAt S snapshot invocation)

/--
Exact invocation coverage: the universe is sealed, and every actual in-scope
occurrence has a packet returned by the evidence reader.
-/
structure ExhaustiveInvocationCoverageAt
    (S : PrimitiveInvocationSystem)
    (snapshot : S.Snapshot)
    (evidence : InvocationEvidenceWindowAt S snapshot) where
  universeSeal : InvocationUniverseSeal S snapshot
  packetComplete :
    ∀ invocation,
      S.inScopeAt snapshot invocation →
        ∃ packet, evidence.packetAt invocation = some packet

/-- A returned `OpResult` always inhabits exactly one of RCC-18's four arms. -/
def InvocationReturned
    {family : PrimitiveFamily.{u, u, u, u}}
    (invocation : ActualPrimitiveInvocation family) : Prop :=
  (∃ value, invocation.result = .Ok value) ∨
    (∃ wake, invocation.result = .Await wake) ∨
    (∃ residue, invocation.result = .Refuse residue) ∨
    (∃ residue, invocation.result = .ResourceExhausted residue)

theorem actualInvocation_returned
    {family : PrimitiveFamily.{u, u, u, u}}
    (invocation : ActualPrimitiveInvocation family) :
    InvocationReturned invocation := by
  cases resultFound : invocation.result with
  | Ok value =>
      exact Or.inl ⟨value, resultFound⟩
  | Await wake =>
      exact Or.inr (Or.inl ⟨wake, resultFound⟩)
  | Refuse residue =>
      exact Or.inr (Or.inr (Or.inl ⟨residue, resultFound⟩))
  | ResourceExhausted residue =>
      exact Or.inr (Or.inr (Or.inr ⟨residue, resultFound⟩))

/--
Headline theorem: every in-scope actual invocation is finite-returning,
RCC-18-refined, same-snapshot runtime-bound, and connected either to the
formal reduction or to an explicit measured receipt.
-/
theorem ExhaustiveInvocationCoverageAt.all_total_refined_runtime_bound
    {S : PrimitiveInvocationSystem}
    {snapshot : S.Snapshot}
    {evidence : InvocationEvidenceWindowAt S snapshot}
    (coverage : ExhaustiveInvocationCoverageAt S snapshot evidence)
    (invocation : S.Invocation)
    (inScope : S.inScopeAt snapshot invocation) :
    ∃ refinement : ActualInvocationRefinementAt (S.familyAt snapshot),
      refinement.invocation = S.actualAt snapshot invocation ∧
      InvocationReturned refinement.invocation ∧
      (S.worldAt snapshot).runtimeStep
        (S.runtimeBeforeAt snapshot invocation)
        (S.runtimeAfterAt snapshot invocation) ∧
      Nonempty (FormalOrMeasuredAt S snapshot invocation) := by
  rcases coverage.packetComplete invocation inScope with
    ⟨packet, found⟩
  exact
    ⟨packet.refinement, packet.invocationExact,
      actualInvocation_returned packet.refinement.invocation,
      packet.runtimeBound, ⟨packet.formalOrMeasured⟩⟩

/-- The projected primitive family used by every covered invocation is lawful. -/
theorem ExhaustiveInvocationCoverageAt.family_lawful
    {S : PrimitiveInvocationSystem}
    {snapshot : S.Snapshot}
    {evidence : InvocationEvidenceWindowAt S snapshot}
    (_coverage : ExhaustiveInvocationCoverageAt S snapshot evidence) :
    LawfulPrimitiveFamily (S.policyAt snapshot) (S.familyAt snapshot) :=
  S.lawfulAt snapshot

end Residua.RCC.PrimitiveInvocationCoverage

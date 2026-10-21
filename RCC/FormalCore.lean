/-!
# ResiduaRCCFormalCore

First machine-checkable slice of RCC-SPEC-v2.

This module deliberately proves a small, load-bearing kernel rather than pretending to
encode the complete 107-target RCC theorem registry in one step:

* `RCCExec` is a total open-state stepper whose `advanced` branch carries a strict
  natural-number decrease.
* `normalize` is well-founded and returns exactly `Closed | Await | Reepoch | Halt`.
* `RCCExec` induces a relation-level `RCCRel`.
* the partial closed normalizer induces a `CoreObject` whose fixed points are exactly
  the executable closed states.
* interfaces for addressing, grounded evidence, admission linearization,
  serializability, world binding, and component seams are named without claiming their
  later theorem obligations are discharged here.

Prelude-only Lean 4.14; no Mathlib, no `sorry`, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC

universe u v w

/-! ## 1. Typed terminal and internal-step results -/

/-- Internal same-epoch outcome for a state already proved open. -/
inductive OpenStepResult (State : Type u) (measure : State → Nat) (s : State) where
  | advanced (next : State) (decreases : measure next < measure s)
  | await (wake : String)
  | reepoch (reason : String)
  | halt (residue : String)

namespace OpenStepResult

/-- Projection used to define the relation induced by an executable stepper. -/
def target? {State : Type u} {measure : State → Nat} {s : State} :
    OpenStepResult State measure s → Option State
  | .advanced next _ => some next
  | .await _ => none
  | .reepoch _ => none
  | .halt _ => none

end OpenStepResult

/-- The externally visible RCC result. `Closed` carries its semantic proof. -/
inductive NormalizeResult (State : Type u) (closed : State → Prop) where
  | closed (state : State) (proof : closed state)
  | await (state : State) (wake : String)
  | reepoch (state : State) (reason : String)
  | halt (state : State) (residue : String)

namespace NormalizeResult

/-- Only a genuine `Closed` branch projects a closed successor state. -/
def state? {State : Type u} {closed : State → Prop} :
    NormalizeResult State closed → Option State
  | .closed state _ => some state
  | .await _ _ => none
  | .reepoch _ _ => none
  | .halt _ _ => none

/-- Erase proof payloads into the four named branch tags. -/
def tag {State : Type u} {closed : State → Prop} :
    NormalizeResult State closed → String
  | .closed _ _ => "Closed"
  | .await _ _ => "Await"
  | .reepoch _ _ => "Reepoch"
  | .halt _ _ => "Halt"

end NormalizeResult

/-! ## 2. Executable and relational RCC cores -/

/-- Minimal executable RCC instance for a frozen epoch. -/
structure Exec where
  State : Type u
  measure : State → Nat
  closed : State → Prop
  closedDecidable : (s : State) → Decidable (closed s)
  stepOpen : (s : State) → ¬ closed s → OpenStepResult State measure s

/-- Relation-level view generated from an executable RCC instance. -/
structure Rel where
  State : Type u
  step : State → State → Prop
  closed : State → Prop

/-- Every executable open-state advance is represented by the induced relation. -/
def relOfExec (E : Exec) : Rel where
  State := E.State
  step := fun s t =>
    ∃ h : ¬ E.closed s, (E.stepOpen s h).target? = some t
  closed := E.closed

/-- The explicit refinement witness for an executable advanced branch. -/
theorem advanced_refines_rel (E : Exec) (s t : E.State)
    (hopen : ¬ E.closed s)
    (hstep : (E.stepOpen s hopen).target? = some t) :
    (relOfExec E).step s t := by
  exact ⟨hopen, hstep⟩

/-- The executable and relation-level closed predicates are definitionally aligned. -/
theorem exec_closed_refines_rel (E : Exec) (s : E.State)
    (h : E.closed s) :
    (relOfExec E).closed s := h

/-! ## 3. Well-founded normalization -/

/--
Normalize one frozen epoch. Only `advanced` recurses, and that constructor carries the
strict decrease needed by Lean's termination checker.
-/
def normalize (E : Exec) (s : E.State) : NormalizeResult E.State E.closed :=
  letI : Decidable (E.closed s) := E.closedDecidable s
  if hclosed : E.closed s then
    .closed s hclosed
  else
    match E.stepOpen s hclosed with
    | .advanced next decreases => normalize E next
    | .await wake => .await s wake
    | .reepoch reason => .reepoch s reason
    | .halt residue => .halt s residue
termination_by E.measure s
decreasing_by exact decreases

/-- Closed states are executable fixed points of the closed projection. -/
theorem normalize_state_of_closed (E : Exec) (s : E.State)
    (h : E.closed s) :
    (normalize E s).state? = some s := by
  rw [normalize]
  simp only [h, ↓reduceDIte, NormalizeResult.state?]

/-- A closed state returns the `Closed` branch rather than a weaker branch. -/
theorem normalize_tag_of_closed (E : Exec) (s : E.State)
    (h : E.closed s) :
    (normalize E s).tag = "Closed" := by
  rw [normalize]
  simp only [h, ↓reduceDIte, NormalizeResult.tag]

/-! ## 4. CoreObject bridge -/

/-- Minimal `CoreObject` shape used by the RCC fixed-point bridge. -/
structure CoreObject where
  Ext : Type u
  Adm : Ext → Prop
  D : Ext → Ext → Prop
  singleValued : ∀ {x y z}, D x y → D x z → y = z

namespace CoreObject

/-- Exactness is fixed-point/admissible equivalence, not representative determinism. -/
def Exact (C : CoreObject) : Prop := ∀ x, C.D x x ↔ C.Adm x

end CoreObject

/-- Partial dynamics: only a completed `Closed` normalization contributes an edge. -/
def coreObject (E : Exec) : CoreObject where
  Ext := E.State
  Adm := E.closed
  D := fun s t => (normalize E s).state? = some t
  singleValued := by
    intro x y z hy hz
    have h : (some y : Option E.State) = some z := hy.symm.trans hz
    exact Option.some.inj h

/-- A normalizer fixed point is closed. -/
theorem core_sound (E : Exec) (s : E.State) :
    (coreObject E).D s s → (coreObject E).Adm s := by
  intro hfixed
  change (normalize E s).state? = some s at hfixed
  change E.closed s
  cases hnorm : normalize E s with
  | closed t ht =>
      simp [NormalizeResult.state?, hnorm] at hfixed
      subst t
      exact ht
  | await t wake =>
      simp [NormalizeResult.state?, hnorm] at hfixed
  | reepoch t reason =>
      simp [NormalizeResult.state?, hnorm] at hfixed
  | halt t residue =>
      simp [NormalizeResult.state?, hnorm] at hfixed

/-- Every closed state is a normalizer fixed point. -/
theorem core_complete (E : Exec) (s : E.State) :
    (coreObject E).Adm s → (coreObject E).D s s := by
  intro hclosed
  change E.closed s at hclosed
  change (normalize E s).state? = some s
  exact normalize_state_of_closed E s hclosed

/-- The first RCC/CoreObject bridge: fixed points are exactly executable closed states. -/
theorem core_exact_iff (E : Exec) (s : E.State) :
    (coreObject E).D s s ↔ (coreObject E).Adm s := by
  exact ⟨core_sound E s, core_complete E s⟩

/-- Pointwise bridge packaged as `CoreObject.Exact`. -/
theorem core_exact (E : Exec) : (coreObject E).Exact := by
  intro s
  exact core_exact_iff E s

/-! ## 5. Named interfaces for later RCC-SPEC-v2 layers -/

/-- A typed address domain; digest equality is never used without these laws. -/
structure AddressKernel where
  Object : Type u
  Context : Type v
  NormalForm : Type w
  equivalent : Context → Object → Object → Prop
  normalize : Context → Object → Option NormalForm
  canonicalBytes : NormalForm → String
  canonicalSound : ∀ {ctx x y nx ny},
    normalize ctx x = some nx →
    normalize ctx y = some ny →
    canonicalBytes nx = canonicalBytes ny →
    equivalent ctx x y

/-- Grounding dependency must descend in rank; same-level circular support is unconstructible. -/
structure GroundedEvidence where
  Claim : Type u
  rank : Claim → Nat
  supports : Claim → Claim → Prop
  supportLower : ∀ {claim premise}, supports claim premise → rank premise < rank claim

/-- Authorization is not finality; this interface carries the single-valued finalizer law. -/
structure AdmissionLinearizer where
  Proposal : Type u
  Slot : Type v
  Judgment : Type w
  slot : Proposal → Slot
  judgment : Proposal → Judgment
  finalized : Proposal → Prop
  atMostOneFinalized : ∀ {p q},
    finalized p → finalized q → slot p = slot q → judgment p = judgment q

/-- Minimal serial execution model for cross-slot invariant preservation. -/
structure SerializableModel where
  State : Type u
  Event : Type v
  apply : State → Event → State
  invariant : State → Prop
  preserves : ∀ {s e}, invariant s → invariant (apply s e)

/-- Explicit world boundary: observation and actuation are separate proof obligations. -/
structure WorldInterface where
  World : Type u
  Observation : Type v
  Event : Type w
  observe : World → Observation
  actuate : World → Event → World
  observationValid : Observation → Prop
  observeSound : ∀ world, observationValid (observe world)

/-- Component seam: local closure and steps must transport through one explicit mapping. -/
structure Seam (A B : Rel) where
  map : A.State → B.State
  closedPreserved : ∀ {s}, A.closed s → B.closed (map s)
  stepPreserved : ∀ {s t}, A.step s t → B.step (map s) (map t)

end Residua.RCC

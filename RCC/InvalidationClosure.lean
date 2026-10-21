/-!
# RCC-21 Parametric Invalidation-Closure Kernel

This module proves invalidation safety from a supplied dependency-extraction
completeness certificate.  It does not prove that any concrete repository or runtime
extractor is complete, so this kernel alone does not discharge RCC-21.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or custom assumptions.
-/

namespace Residua.RCC

universe u v w x y

/-- Nonempty transitive closure of a direct dependency relation. -/
inductive DependencyClosure {Node : Type u} (direct : Node → Node → Prop) :
    Node → Node → Prop where
  | direct {parent dependency : Node} :
      direct parent dependency → DependencyClosure direct parent dependency
  | trans {parent intermediate dependency : Node} :
      DependencyClosure direct parent intermediate →
      DependencyClosure direct intermediate dependency →
      DependencyClosure direct parent dependency

/-- The extracted dependency closure is transitive by construction. -/
theorem DependencyClosure.transitive {Node : Type u} (direct : Node → Node → Prop) :
    ∀ {a b c}, DependencyClosure direct a b →
      DependencyClosure direct b c → DependencyClosure direct a c := by
  intro a b c hab hbc
  exact .trans hab hbc

/-- Current authority state; historical validity is stored separately. -/
inductive InvalidationJudgmentState (Judgment : Type u) where
  | usable
  | transported (replacement : Judgment)
  | reopened
  deriving DecidableEq

/-- Domain facts consumed by the invalidation kernel. -/
structure InvalidationSystem where
  Node : Type u
  Judgment : Type v
  Head : Type w
  Edit : Type x
  Projection : Type y
  judgmentNode : Judgment → Node
  directDepends : Node → Node → Prop
  directDependsDecidable : (parent dependency : Node) →
    Decidable (directDepends parent dependency)
  actualInfluence : Node → Judgment → Prop
  writes : Edit → Node → Prop
  writesDecidable : (edit : Edit) → (node : Node) → Decidable (writes edit node)
  validAt : Head → Judgment → Prop
  transportable : Judgment → Judgment → Prop
  deriveProjection :
    Head → (Judgment → InvalidationJudgmentState Judgment) → Projection

/-- An edit invalidates a judgment when it writes any node in its full dependency closure. -/
def Invalidated (S : InvalidationSystem) (edit : S.Edit) (judgment : S.Judgment) : Prop :=
  ∃ node, S.writes edit node ∧
    DependencyClosure S.directDepends (S.judgmentNode judgment) node

/--
Proof-carrying extracted closure. `detected` is executable, `detectedExact` ties it to
the mathematical transitive closure, and `covers` states the still-parametric
actual-influence completeness premise.
-/
structure DependencyExtractionComplete (S : InvalidationSystem) where
  detected : S.Edit → S.Judgment → Bool
  detectedExact : ∀ edit judgment,
    detected edit judgment = true ↔ Invalidated S edit judgment
  covers : ∀ node judgment,
    S.actualInfluence node judgment →
    DependencyClosure S.directDepends (S.judgmentNode judgment) node

/-- Same-epoch certified invalidation or conservative full re-derivation. -/
inductive InvalidationMode (S : InvalidationSystem) where
  | certified (certificate : DependencyExtractionComplete S)
  | fullRederive

/-- Historical truth, terminality, current authority, and the derived projection. -/
structure InvalidationSnapshot (S : InvalidationSystem) where
  head : S.Head
  historicalValid : S.Judgment → Bool
  terminal : S.Judgment → Bool
  currentState : S.Judgment → InvalidationJudgmentState S.Judgment
  projection : S.Projection

/-- Executable selector derived from the mode and old terminal judgments. -/
def needsResolution (S : InvalidationSystem)
    (snapshot : InvalidationSnapshot S) (edit : S.Edit)
    (mode : InvalidationMode S) (judgment : S.Judgment) : Bool :=
  snapshot.terminal judgment &&
    match mode with
    | .certified certificate => certificate.detected edit judgment
    | .fullRederive => true

/-- Proposition exposed to proof plans; it is definitionally tied to the Bool selector. -/
def NeedsResolution (S : InvalidationSystem)
    (snapshot : InvalidationSnapshot S) (edit : S.Edit)
    (mode : InvalidationMode S) (judgment : S.Judgment) : Prop :=
  needsResolution S snapshot edit mode judgment = true

/-- Lawful resolution of one selected terminal judgment. -/
inductive InvalidationResolution
    (S : InvalidationSystem) (newHead : S.Head) (judgment : S.Judgment) where
  | revalidated (certificate : S.validAt newHead judgment)
  | transported (replacement : S.Judgment)
      (certificate : S.transportable judgment replacement)
  | reopened

/-- Current-state projection of a proof-carrying resolution. -/
def InvalidationResolution.state
    {S : InvalidationSystem} {newHead : S.Head} {judgment : S.Judgment} :
    InvalidationResolution S newHead judgment →
      InvalidationJudgmentState S.Judgment
  | .revalidated _ => .usable
  | .transported replacement _ => .transported replacement
  | .reopened => .reopened

/-- A pointwise resolution for every mechanically selected judgment. -/
structure InvalidationPlan
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (edit : S.Edit) (mode : InvalidationMode S) (newHead : S.Head := snapshot.head) where
  resolve : (judgment : S.Judgment) →
    NeedsResolution S snapshot edit mode judgment →
    InvalidationResolution S newHead judgment

/-- Semantic validity of the three possible selected-judgment outcomes. -/
def LawfullyResolved
    (S : InvalidationSystem) (newHead : S.Head) (judgment : S.Judgment) :
    InvalidationJudgmentState S.Judgment → Prop
  | .usable => S.validAt newHead judgment
  | .transported replacement => S.transportable judgment replacement
  | .reopened => True

/-- Current-state function selected by the certified invalidation plan. -/
def invalidatedPostState
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment) : InvalidationJudgmentState S.Judgment :=
  if hrequired : needsResolution S snapshot edit mode judgment = true then
    (plan.resolve judgment hrequired).state
  else
    snapshot.currentState judgment

/--
Apply invalidation at a new head. Historical validity is copied definitionally.
The projection is recomputed from the new head and the post-state judgments.
-/
def applyInvalidation
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead) :
    InvalidationSnapshot S :=
  {
    head := newHead
    historicalValid := snapshot.historicalValid
    terminal := snapshot.terminal
    currentState := invalidatedPostState S snapshot newHead edit mode plan
    projection := S.deriveProjection newHead
      (invalidatedPostState S snapshot newHead edit mode plan)
  }

/-- Completeness converts a written actual influence into extracted invalidation. -/
theorem actual_influence_write_invalidates
    (S : InvalidationSystem)
    (complete : DependencyExtractionComplete S)
    (edit : S.Edit) (node : S.Node) (judgment : S.Judgment)
    (hinfluence : S.actualInfluence node judgment)
    (hwrites : S.writes edit node) :
    Invalidated S edit judgment := by
  exact ⟨node, hwrites, complete.covers node judgment hinfluence⟩

/-- Every mechanically required judgment has one of the three lawful post-states. -/
theorem required_judgment_lawfully_resolved
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment)
    (hrequired : NeedsResolution S snapshot edit mode judgment) :
    LawfullyResolved S newHead judgment
      ((applyInvalidation S snapshot newHead edit mode plan).currentState judgment) := by
  change needsResolution S snapshot edit mode judgment = true at hrequired
  simp only [applyInvalidation, invalidatedPostState, hrequired, dite_true]
  cases hresolution : plan.resolve judgment hrequired with
  | revalidated certificate =>
      simpa [hresolution, InvalidationResolution.state, LawfullyResolved] using certificate
  | transported replacement certificate =>
      simpa [hresolution, InvalidationResolution.state, LawfullyResolved] using certificate
  | reopened =>
      simp [hresolution, InvalidationResolution.state, LawfullyResolved]

/-- The result packages both mechanical selection and lawful resolution. -/
structure InvalidatedTerminalResolution
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment) : Prop where
  required : NeedsResolution S snapshot edit mode judgment
  lawful : LawfullyResolved S newHead judgment
    ((applyInvalidation S snapshot newHead edit mode plan).currentState judgment)

/-- Every invalidated terminal is selected and lawfully resolved in either mode. -/
theorem invalidated_terminal_lawfully_resolved
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment)
    (hterminal : snapshot.terminal judgment = true)
    (hinvalidated : Invalidated S edit judgment) :
    InvalidatedTerminalResolution S snapshot newHead edit mode plan judgment := by
  have hrequired : NeedsResolution S snapshot edit mode judgment := by
    cases mode with
    | certified certificate =>
        simp [NeedsResolution, needsResolution, hterminal,
          (certificate.detectedExact edit judgment).2 hinvalidated]
    | fullRederive =>
        simp [NeedsResolution, needsResolution, hterminal]
  exact {
    required := hrequired
    lawful := required_judgment_lawfully_resolved
      S snapshot newHead edit mode plan judgment hrequired
  }

/--
RCC-21 composition: a write to an actual influence of an old terminal
judgment is selected and lawfully resolved by the same certified complete
dependency extractor and invalidation plan.
-/
theorem actual_influence_terminal_lawfully_resolved
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit)
    (complete : DependencyExtractionComplete S)
    (plan :
      InvalidationPlan S snapshot edit (.certified complete) newHead)
    (node : S.Node) (judgment : S.Judgment)
    (hterminal : snapshot.terminal judgment = true)
    (hinfluence : S.actualInfluence node judgment)
    (hwrites : S.writes edit node) :
    InvalidatedTerminalResolution
      S snapshot newHead edit (.certified complete) plan judgment :=
  invalidated_terminal_lawfully_resolved
    S snapshot newHead edit (.certified complete) plan judgment hterminal
      (actual_influence_write_invalidates
        S complete edit node judgment hinfluence hwrites)

/-- A selected judgment may remain usable only through new-head revalidation. -/
theorem invalidated_usable_implies_revalidated
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment)
    (hrequired : NeedsResolution S snapshot edit mode judgment) :
    (applyInvalidation S snapshot newHead edit mode plan).currentState judgment = .usable →
      S.validAt newHead judgment := by
  intro husable
  have hlawful := required_judgment_lawfully_resolved
    S snapshot newHead edit mode plan judgment hrequired
  simpa [husable, LawfullyResolved] using hlawful

/-- Full re-derivation selects exactly all previously terminal judgments. -/
theorem full_rederive_selects_every_terminal
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (edit : S.Edit) (judgment : S.Judgment) :
    NeedsResolution S snapshot edit .fullRederive judgment ↔
      snapshot.terminal judgment = true := by
  simp [NeedsResolution, needsResolution]

/-- Current invalidation never rewrites historical validity. -/
theorem invalidation_preserves_historical_validity
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment) :
    (applyInvalidation S snapshot newHead edit mode plan).historicalValid judgment =
      snapshot.historicalValid judgment := by
  rfl

/-- Projection truth is recomputed from the new head and post-state judgments. -/
theorem invalidation_rederives_projection
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead) :
    (applyInvalidation S snapshot newHead edit mode plan).projection =
      S.deriveProjection newHead
        (applyInvalidation S snapshot newHead edit mode plan).currentState := by
  rfl

/-- A judgment not selected by this mode preserves its prior current state. -/
theorem unaffected_judgment_state_preserved
    (S : InvalidationSystem) (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit) (mode : InvalidationMode S)
    (plan : InvalidationPlan S snapshot edit mode newHead)
    (judgment : S.Judgment)
    (hnot : ¬ NeedsResolution S snapshot edit mode judgment) :
    (applyInvalidation S snapshot newHead edit mode plan).currentState judgment =
      snapshot.currentState judgment := by
  change needsResolution S snapshot edit mode judgment ≠ true at hnot
  simp [applyInvalidation, invalidatedPostState, hnot]

end Residua.RCC

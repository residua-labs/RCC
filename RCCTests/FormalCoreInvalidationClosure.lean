import RCC.InvalidationClosure

/-!
# RCC-21 Invalidation-Closure Witnesses

This file instantiates only the parametric invalidation kernel.  The three-node
countermodel shows why a direct-edge scan is insufficient, but it is not a certificate
that any concrete repository/runtime dependency extractor is complete.
-/

open Residua.RCC

namespace Residua.RCC.InvalidationClosureTests

inductive DemoNode
  | judgment
  | generated
  | source
  | unrelated
  deriving DecidableEq

inductive DemoJudgment
  | staleGreen
  | unrelatedGreen
  deriving DecidableEq

inductive DemoHead
  | old
  | new
  deriving DecidableEq

inductive DemoEdit
  | sourceEdit
  deriving DecidableEq

inductive DemoProjection
  | oldProjection
  | newProjectionWithStaleReopened
  | newProjectionWithAllUsable
  deriving DecidableEq

def demoDirectDepends : DemoNode → DemoNode → Prop
  | .judgment, .generated => True
  | .generated, .source => True
  | _, _ => False

def demoActualInfluence : DemoNode → DemoJudgment → Prop
  | .source, .staleGreen => True
  | _, _ => False

def demoWrites : DemoEdit → DemoNode → Prop
  | .sourceEdit, .source => True
  | _, _ => False

def demoProjection :
    DemoHead → (DemoJudgment → InvalidationJudgmentState DemoJudgment) → DemoProjection
  | .old, _ => .oldProjection
  | .new, state =>
      match state .staleGreen with
      | .reopened => .newProjectionWithStaleReopened
      | _ => .newProjectionWithAllUsable

def demoSystem : InvalidationSystem where
  Node := DemoNode
  Judgment := DemoJudgment
  Head := DemoHead
  Edit := DemoEdit
  Projection := DemoProjection
  judgmentNode := fun
    | .staleGreen => .judgment
    | .unrelatedGreen => .unrelated
  directDepends := demoDirectDepends
  directDependsDecidable := fun parent child =>
    match parent, child with
    | .judgment, .generated => isTrue trivial
    | .generated, .source => isTrue trivial
    | .judgment, .judgment
    | .judgment, .source
    | .judgment, .unrelated
    | .generated, .judgment
    | .generated, .generated
    | .generated, .unrelated
    | .source, _
    | .unrelated, _ => isFalse (fun h => h)
  actualInfluence := demoActualInfluence
  writes := demoWrites
  writesDecidable := fun edit node =>
    match edit, node with
    | .sourceEdit, .source => isTrue trivial
    | .sourceEdit, .judgment
    | .sourceEdit, .generated
    | .sourceEdit, .unrelated => isFalse (fun h => h)
  validAt := fun head judgment =>
    match head, judgment with
    | .new, .staleGreen => False
    | _, _ => True
  transportable := fun _ _ => False
  deriveProjection := demoProjection

/-- The extracted closure contains the full two-edge path. -/
theorem staleDependsTransitivelyOnSource :
    DependencyClosure demoDirectDepends .judgment .source := by
  have hfirst : DependencyClosure demoDirectDepends .judgment .generated :=
    DependencyClosure.direct (by trivial)
  have hsecond : DependencyClosure demoDirectDepends .generated .source :=
    DependencyClosure.direct (by trivial)
  exact DependencyClosure.trans hfirst hsecond

/-- A path can only start at a node that owns some direct dependency edge. -/
theorem directDependencyStartIsNotUnrelated
    {parent node : DemoNode}
    (hdirect : demoDirectDepends parent node) :
    parent ≠ .unrelated := by
  intro heq
  subst parent
  cases node <;> simp [demoDirectDepends] at hdirect

/-- Transitive dependency paths inherit the direct edge's rooted source. -/
theorem dependencyPathStartIsNotUnrelated
    {parent node : DemoNode}
    (hclosure : DependencyClosure demoDirectDepends parent node) :
    parent ≠ .unrelated := by
  induction hclosure with
  | direct hdirect =>
      exact directDependencyStartIsNotUnrelated hdirect
  | trans _ _ ihParent _ =>
      exact ihParent

/-- No dependency path starts at the unrelated node. -/
theorem noDependencyFromUnrelated (node : DemoNode) :
    ¬ DependencyClosure demoDirectDepends .unrelated node := by
  intro hclosure
  exact dependencyPathStartIsNotUnrelated hclosure rfl

/-- Executable selector for the frozen demonstration graph. -/
def demoDetected : DemoEdit → DemoJudgment → Bool
  | .sourceEdit, .staleGreen => true
  | .sourceEdit, .unrelatedGreen => false

def demoExtractionComplete : DependencyExtractionComplete demoSystem where
  detected := demoDetected
  detectedExact := by
    intro edit judgment
    cases edit
    cases judgment with
    | staleGreen =>
        constructor
        · intro _
          exact ⟨.source, trivial, staleDependsTransitivelyOnSource⟩
        · intro _
          rfl
    | unrelatedGreen =>
        constructor
        · intro h
          cases h
        · intro hinvalidated
          rcases hinvalidated with ⟨node, hwrites, hclosure⟩
          cases node <;> simp [demoSystem, demoWrites] at hwrites
          exact False.elim (noDependencyFromUnrelated .source hclosure)
  covers := by
    intro node judgment hinfluence
    cases node <;> cases judgment <;>
      simp [demoSystem, demoActualInfluence] at hinfluence
    simpa [demoSystem] using staleDependsTransitivelyOnSource

def initialSnapshot : InvalidationSnapshot demoSystem where
  head := .old
  historicalValid := fun _ => true
  terminal := fun _ => true
  currentState := fun _ => .usable
  projection := .oldProjection

def certifiedMode : InvalidationMode demoSystem :=
  .certified demoExtractionComplete

def certifiedPlan :
    InvalidationPlan demoSystem initialSnapshot .sourceEdit certifiedMode .new where
  resolve := fun judgment hrequired => by
    cases judgment with
    | staleGreen => exact .reopened
    | unrelatedGreen =>
        simp [NeedsResolution, needsResolution, certifiedMode,
          demoExtractionComplete, demoDetected, initialSnapshot] at hrequired

def invalidatedSnapshot : InvalidationSnapshot demoSystem :=
  applyInvalidation demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan

theorem transitive_closure_catches_source_edit :
    Invalidated demoSystem .sourceEdit .staleGreen := by
  exact actual_influence_write_invalidates
    demoSystem demoExtractionComplete .sourceEdit .source .staleGreen
      (by simp [demoSystem, demoActualInfluence])
      (by simp [demoSystem, demoWrites])

theorem stale_green_is_required :
    NeedsResolution demoSystem initialSnapshot .sourceEdit certifiedMode .staleGreen := by
  exact (invalidated_terminal_lawfully_resolved
    demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan .staleGreen
      (by simp [initialSnapshot])
      transitive_closure_catches_source_edit).required

theorem stale_green_is_reopened :
    invalidatedSnapshot.currentState .staleGreen = .reopened := by
  have hlawful := required_judgment_lawfully_resolved
    demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan .staleGreen
      stale_green_is_required
  change LawfullyResolved demoSystem .new .staleGreen
    (invalidatedSnapshot.currentState .staleGreen) at hlawful
  cases hstate : invalidatedSnapshot.currentState .staleGreen with
  | usable =>
      simp [demoSystem, LawfullyResolved, hstate] at hlawful
  | transported replacement =>
      simp [demoSystem, LawfullyResolved, hstate] at hlawful
  | reopened =>
      exact hstate

theorem stale_green_cannot_remain_usable :
    invalidatedSnapshot.currentState .staleGreen ≠ .usable := by
  intro husable
  have hrevalidated := invalidated_usable_implies_revalidated
    demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan .staleGreen
      stale_green_is_required husable
  exact hrevalidated

theorem historical_validity_is_immutable :
    invalidatedSnapshot.historicalValid .staleGreen = true := by
  simpa [invalidatedSnapshot, initialSnapshot] using
    invalidation_preserves_historical_validity
      demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan .staleGreen

theorem projection_is_rederived :
    invalidatedSnapshot.projection = .newProjectionWithStaleReopened := by
  change
    (applyInvalidation demoSystem initialSnapshot .new .sourceEdit
      certifiedMode certifiedPlan).projection = .newProjectionWithStaleReopened
  rw [invalidation_rederives_projection]
  change demoProjection .new invalidatedSnapshot.currentState =
    .newProjectionWithStaleReopened
  simp [demoProjection, stale_green_is_reopened]

/-- A direct-only detector checks only `judgment -> source`, missing the generated node. -/
def DirectInvalidated (edit : DemoEdit) (judgment : DemoJudgment) : Prop :=
  ∃ node, demoWrites edit node ∧
    demoDirectDepends (demoSystem.judgmentNode judgment) node

theorem direct_only_mutant_misses_transitive_source :
    ¬ DirectInvalidated .sourceEdit .staleGreen := by
  intro h
  rcases h with ⟨node, hwrites, hdirect⟩
  cases node <;> simp [demoWrites, demoDirectDepends, demoSystem] at hwrites hdirect

/-- Mutant outcome: the direct-only scan preserves stale authority as usable. -/
def directOnlyMutant : InvalidationSnapshot demoSystem :=
  {
    initialSnapshot with
    head := .new
    projection := .newProjectionWithAllUsable
  }

theorem direct_only_mutant_leaves_stale_green_usable :
    directOnlyMutant.currentState .staleGreen = .usable := by
  rfl

theorem full_closure_refuses_direct_only_mutant :
    invalidatedSnapshot.currentState .staleGreen ≠
      directOnlyMutant.currentState .staleGreen := by
  rw [stale_green_is_reopened]
  simp [directOnlyMutant, initialSnapshot]

def fullPlan :
    InvalidationPlan demoSystem initialSnapshot .sourceEdit .fullRederive .new where
  resolve := fun judgment _ => by
    cases judgment with
    | staleGreen => exact .reopened
    | unrelatedGreen => exact .revalidated (by simp [demoSystem])

def fullyRederivedSnapshot : InvalidationSnapshot demoSystem :=
  applyInvalidation demoSystem initialSnapshot .new .sourceEdit .fullRederive fullPlan

theorem full_rederive_requires_unrelated_terminal :
    NeedsResolution demoSystem initialSnapshot .sourceEdit .fullRederive
      .unrelatedGreen := by
  exact (full_rederive_selects_every_terminal
    demoSystem initialSnapshot .sourceEdit .unrelatedGreen).2 (by
      simp [initialSnapshot])

theorem unrelated_state_is_preserved_in_certified_mode :
    invalidatedSnapshot.currentState .unrelatedGreen = .usable := by
  exact unaffected_judgment_state_preserved
    demoSystem initialSnapshot .new .sourceEdit certifiedMode certifiedPlan
      .unrelatedGreen (by
        simp [NeedsResolution, needsResolution, certifiedMode,
          demoExtractionComplete, demoDetected, initialSnapshot])

end Residua.RCC.InvalidationClosureTests

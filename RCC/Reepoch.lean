/-!
# RCC-23 Reepoch Anti-Churn and Migration Refinement Kernel

A reepoch certificate cannot be constructed from a changed address alone. It carries
one witnessed semantic component change, exactly one admitted trigger, a fresh trigger
occurrence, a snapshot-global occurrence-to-edge reservation, an exact parent binding,
total old-debt disposition, and either a decreasing finite-campaign measure or an
acyclic open-lineage edge.

This kernel verifies a supplied successor and migration certificate. It does not prove
that a successor exists, that an open institution globally terminates, or that a
repository extractor has discovered every goal or trigger. Prelude-only Lean 4.14;
no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC

universe u v w x y

/-- The six semantic epoch coordinates whose change can justify reepoching. -/
inductive EpochSemanticSlot where
  | policy
  | kernel
  | sourceRule
  | theory
  | intent
  | assumptions
  deriving DecidableEq, Repr

/--
Domain records consumed by the RCC-23 kernel. Strict ancestry and cumulative trigger
consumption are derived below from `parentEpoch` and `triggerOccurrence`; callers do not
supply either relation.
-/
structure ReepochSystem where
  Epoch : Type u
  Goal : Type v
  Occurrence : Type w
  SemanticValue : Type x
  GoalOrigin : Type y
  semanticValue : Epoch → EpochSemanticSlot → SemanticValue
  parentEpoch : Epoch → Option Epoch
  goalOrigin : Goal → GoalOrigin
  goalSatisfied : Epoch → Goal → Prop
  nonterminal : Epoch → Goal → Prop
  terminalAtMigration : Epoch → Goal → Prop
  /-- The admitted trigger occurrence that created an epoch; genesis has `none`. -/
  triggerOccurrence : Epoch → Option Occurrence
  /--
  Snapshot-global single-valued reservation of an occurrence to one migration edge.
  This closes sibling reuse, which ancestor-chain consumption alone cannot observe.
  -/
  migrationForOccurrence : Occurrence → Option (Epoch × Epoch)
  newObservationAdmitted : Epoch → Occurrence → Prop
  policyDecisionAdmitted : Epoch → Occurrence → Prop
  kernelReplacementAdmitted : Epoch → Occurrence → Prop
  stableObstructionAdmitted : Epoch → Occurrence → Prop
  epochMeasure : Epoch → Nat

/-- Strict ancestry derived solely from the transitive closure of `parentEpoch`. -/
inductive ParentAncestor
    (S : ReepochSystem.{u, v, w, x, y}) :
    S.Epoch → S.Epoch → Prop where
  | direct
      {parent child : S.Epoch}
      (parentBound : S.parentEpoch child = some parent) :
      ParentAncestor S parent child
  | trans
      {earlier middle later : S.Epoch}
      (left : ParentAncestor S earlier middle)
      (right : ParentAncestor S middle later) :
      ParentAncestor S earlier later

namespace ParentAncestor

/-- Every strict ancestor proof ends at an epoch with a recorded direct parent. -/
theorem target_has_parent
    {S : ReepochSystem.{u, v, w, x, y}}
    {earlier later : S.Epoch}
    (ancestry : ParentAncestor S earlier later) :
    ∃ parent, S.parentEpoch later = some parent := by
  induction ancestry with
  | direct parentBound =>
      exact ⟨_, parentBound⟩
  | trans left right ihLeft ihRight =>
      exact ihRight

end ParentAncestor

/--
An occurrence is cumulatively consumed when it created the current epoch or any epoch
on its exact parent chain. There is no caller-supplied local consumption predicate.
-/
inductive OccurrenceConsumed
    (S : ReepochSystem.{u, v, w, x, y}) :
    S.Epoch → S.Occurrence → Prop where
  | here
      {epoch : S.Epoch} {occurrence : S.Occurrence}
      (recorded : S.triggerOccurrence epoch = some occurrence) :
      OccurrenceConsumed S epoch occurrence
  | inherited
      {epoch parent : S.Epoch} {occurrence : S.Occurrence}
      (parentBound : S.parentEpoch epoch = some parent)
      (consumedAtParent : OccurrenceConsumed S parent occurrence) :
      OccurrenceConsumed S epoch occurrence

namespace OccurrenceConsumed

/-- Consumption at an epoch is witnessed locally or through a recorded direct parent. -/
theorem current_record_or_parent
    {S : ReepochSystem.{u, v, w, x, y}}
    {epoch : S.Epoch} {occurrence : S.Occurrence}
    (consumed : OccurrenceConsumed S epoch occurrence) :
    S.triggerOccurrence epoch = some occurrence ∨
      ∃ parent, S.parentEpoch epoch = some parent := by
  cases consumed with
  | here recorded =>
      exact Or.inl recorded
  | inherited parentBound consumedAtParent =>
      exact Or.inr ⟨_, parentBound⟩

end OccurrenceConsumed

/--
At least one actual semantic coordinate differs. There is deliberately no constructor
for address/head inequality.
-/
inductive EpochDelta (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch) where
  | policyChanged
      (different :
        S.semanticValue parent .policy ≠
          S.semanticValue successor .policy)
  | kernelChanged
      (different :
        S.semanticValue parent .kernel ≠
          S.semanticValue successor .kernel)
  | sourceRuleChanged
      (different :
        S.semanticValue parent .sourceRule ≠
          S.semanticValue successor .sourceRule)
  | theoryChanged
      (different :
        S.semanticValue parent .theory ≠
          S.semanticValue successor .theory)
  | intentChanged
      (different :
        S.semanticValue parent .intent ≠
          S.semanticValue successor .intent)
  | assumptionsChanged
      (different :
        S.semanticValue parent .assumptions ≠
          S.semanticValue successor .assumptions)

namespace EpochDelta

/-- A witnessed component inequality rules out a self-reepoch. -/
theorem parent_ne_successor
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (delta : EpochDelta S parent successor) :
    parent ≠ successor := by
  intro hequal
  subst successor
  cases delta with
  | policyChanged different => exact different rfl
  | kernelChanged different => exact different rfl
  | sourceRuleChanged different => exact different rfl
  | theoryChanged different => exact different rfl
  | intentChanged different => exact different rfl
  | assumptionsChanged different => exact different rfl

end EpochDelta

/--
The trigger union has exactly the four admitted constructors frozen by RCC-23.
Scheduler choice has no constructor.
-/
inductive AdmittedTrigger
    (S : ReepochSystem.{u, v, w, x, y}) (parent : S.Epoch) where
  | newObservation
      (occurrence : S.Occurrence)
      (admitted : S.newObservationAdmitted parent occurrence)
  | policyDecision
      (occurrence : S.Occurrence)
      (admitted : S.policyDecisionAdmitted parent occurrence)
  | kernelReplacement
      (occurrence : S.Occurrence)
      (admitted : S.kernelReplacementAdmitted parent occurrence)
  | stableObstruction
      (occurrence : S.Occurrence)
      (admitted : S.stableObstructionAdmitted parent occurrence)

namespace AdmittedTrigger

/-- The unique occurrence carried by any admitted trigger constructor. -/
def occurrence
    {S : ReepochSystem.{u, v, w, x, y}} {parent : S.Epoch} :
    AdmittedTrigger S parent → S.Occurrence
  | .newObservation occurrence _ => occurrence
  | .policyDecision occurrence _ => occurrence
  | .kernelReplacement occurrence _ => occurrence
  | .stableObstruction occurrence _ => occurrence

end AdmittedTrigger

/-- A trigger is fresh exactly when its occurrence is absent from the pre-epoch ledger. -/
def TriggerFresh
    (S : ReepochSystem.{u, v, w, x, y})
    (parent : S.Epoch)
    (trigger : AdmittedTrigger S parent) : Prop :=
  ¬ OccurrenceConsumed S parent trigger.occurrence

/--
Semantic migration is contravariant in satisfaction: satisfying the successor goal
must discharge the old goal.
-/
def SemanticallyRefines
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch)
    (oldGoal newGoal : S.Goal) : Prop :=
  S.goalSatisfied successor newGoal →
    S.goalSatisfied parent oldGoal

/--
Migration binds the successor goal to the old origin and, separately, proves semantic
refinement. Origin equality cannot stand in for the refinement proof.
-/
structure GoalMigration
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch)
    (oldGoal : S.Goal) where
  newGoal : S.Goal
  originBound : S.goalOrigin newGoal = S.goalOrigin oldGoal
  semanticRefinement :
    SemanticallyRefines S parent successor oldGoal newGoal

/-- Every old nonterminal goal is terminal at the boundary or has a certified successor. -/
inductive GoalDisposition
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch)
    (oldGoal : S.Goal) where
  | terminal
      (certificate : S.terminalAtMigration parent oldGoal)
  | migrated
      (migration : GoalMigration S parent successor oldGoal)

/-- Total disposition over the supplied old nonterminal-goal predicate. -/
structure DebtPlan
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch) where
  resolve :
    (oldGoal : S.Goal) →
    S.nonterminal parent oldGoal →
    GoalDisposition S parent successor oldGoal

/--
Finite campaigns justify an edge with a strict epoch measure. Open institutions instead
justify that the new edge has no back path in the admitted strict ancestry relation.
-/
inductive LineageCert
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch) where
  | finiteCampaign
      (decreases : S.epochMeasure successor < S.epochMeasure parent)
  | openLineage
      (noBackEdge : ¬ ParentAncestor S successor parent)

namespace LineageCert

/-- Constructor predicate used to extract the finite-campaign proof without a tag. -/
def IsFinite
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch} :
    LineageCert S parent successor → Prop
  | .finiteCampaign _ => True
  | .openLineage _ => False

/-- Constructor predicate used to extract the open-lineage proof without a tag. -/
def IsOpen
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch} :
    LineageCert S parent successor → Prop
  | .finiteCampaign _ => False
  | .openLineage _ => True

/-- A finite constructor always exposes its strict epoch-measure decrease. -/
theorem finite_decreases
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (lineage : LineageCert S parent successor)
    (isFinite : lineage.IsFinite) :
    S.epochMeasure successor < S.epochMeasure parent := by
  cases lineage with
  | finiteCampaign decreases => exact decreases
  | openLineage noBackEdge => exact False.elim isFinite

/-- An open constructor always exposes the absence of a back edge. -/
theorem open_has_no_back_edge
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (lineage : LineageCert S parent successor)
    (isOpen : lineage.IsOpen) :
    ¬ ParentAncestor S successor parent := by
  cases lineage with
  | finiteCampaign decreases => exact False.elim isOpen
  | openLineage noBackEdge => exact noBackEdge

end LineageCert

/-- Complete proof-carrying RCC-23 reepoch certificate. -/
structure ReepochCert
    (S : ReepochSystem.{u, v, w, x, y})
    (parent successor : S.Epoch) where
  delta : EpochDelta S parent successor
  trigger : AdmittedTrigger S parent
  triggerFresh : TriggerFresh S parent trigger
  parentBound : S.parentEpoch successor = some parent
  triggerBound :
    S.triggerOccurrence successor = some trigger.occurrence
  occurrenceReserved :
    S.migrationForOccurrence trigger.occurrence = some (parent, successor)
  debtPlan : DebtPlan S parent successor
  lineage : LineageCert S parent successor

/-- Every certificate carries a real semantic change, not an address-only delta. -/
def reepochSemanticDelta
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    EpochDelta S parent successor :=
  certificate.delta

/-- A certified successor is distinct from its exact parent. -/
theorem reepoch_parent_ne_successor
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    parent ≠ successor :=
  certificate.delta.parent_ne_successor

/-- The trigger is one of the four admitted constructors and is anchored to the parent. -/
def reepochAdmittedTrigger
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    AdmittedTrigger S parent :=
  certificate.trigger

/-- A consumed observation/decision/replacement/obstruction cannot be reused. -/
theorem reepoch_trigger_is_fresh
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    ¬ OccurrenceConsumed S parent certificate.trigger.occurrence :=
  certificate.triggerFresh

/-- The successor record names exactly the certified parent epoch. -/
theorem reepoch_binds_exact_parent
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    S.parentEpoch successor = some parent :=
  certificate.parentBound

/-- The exact parent binding creates the direct strict-ancestry edge. -/
theorem reepoch_parent_is_ancestor
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    ParentAncestor S parent successor :=
  .direct certificate.parentBound

/-- The successor durably records the exact fresh occurrence consumed by the edge. -/
theorem reepoch_records_trigger
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    S.triggerOccurrence successor = some certificate.trigger.occurrence :=
  certificate.triggerBound

/-- The snapshot-global occurrence ledger binds the trigger to this exact edge. -/
theorem reepoch_reserves_exact_edge
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    S.migrationForOccurrence certificate.trigger.occurrence =
      some (parent, successor) :=
  certificate.occurrenceReserved

/--
Two certified edges using the same occurrence are identical. This is the global
single-valued safety law that rejects reuse across sibling branches.
-/
theorem same_occurrence_reservation_unique
    {S : ReepochSystem.{u, v, w, x, y}}
    {leftParent leftSuccessor rightParent rightSuccessor : S.Epoch}
    (left : ReepochCert S leftParent leftSuccessor)
    (right : ReepochCert S rightParent rightSuccessor)
    (sameOccurrence :
      left.trigger.occurrence = right.trigger.occurrence) :
    (leftParent, leftSuccessor) = (rightParent, rightSuccessor) := by
  have leftReserved := left.occurrenceReserved
  have rightReserved := right.occurrenceReserved
  rw [sameOccurrence] at leftReserved
  exact Option.some.inj (leftReserved.symm.trans rightReserved)

/-- The edge's exact trigger is consumed at its successor. -/
theorem reepoch_consumes_trigger
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor) :
    OccurrenceConsumed S successor certificate.trigger.occurrence :=
  .here certificate.triggerBound

/-- Consumption is cumulative along the exact parent edge. -/
theorem reepoch_preserves_consumption
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor)
    {occurrence : S.Occurrence}
    (consumed : OccurrenceConsumed S parent occurrence) :
    OccurrenceConsumed S successor occurrence :=
  .inherited certificate.parentBound consumed

/--
No old nonterminal goal disappears: it is terminal at the boundary or has a successor
whose satisfaction semantically discharges the old goal.
-/
theorem reepoch_preserves_old_debt
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor)
    (oldGoal : S.Goal)
    (hnonterminal : S.nonterminal parent oldGoal) :
    S.terminalAtMigration parent oldGoal ∨
      ∃ migration : GoalMigration S parent successor oldGoal,
        SemanticallyRefines
          S parent successor oldGoal migration.newGoal := by
  cases certificate.debtPlan.resolve oldGoal hnonterminal with
  | terminal terminalCertificate =>
      exact Or.inl terminalCertificate
  | migrated migration =>
      exact Or.inr ⟨migration, migration.semanticRefinement⟩

/-- Extract strict campaign progress from the finite-campaign branch. -/
theorem finite_campaign_decreases
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor)
    (isFinite : certificate.lineage.IsFinite) :
    S.epochMeasure successor < S.epochMeasure parent := by
  exact certificate.lineage.finite_decreases isFinite

/-- Extract local acyclicity from the open-lineage branch. -/
theorem open_lineage_has_no_back_edge
    {S : ReepochSystem.{u, v, w, x, y}}
    {parent successor : S.Epoch}
    (certificate : ReepochCert S parent successor)
    (isOpen : certificate.lineage.IsOpen) :
    ¬ ParentAncestor S successor parent := by
  exact certificate.lineage.open_has_no_back_edge isOpen

end Residua.RCC

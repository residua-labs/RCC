import RCC.Reepoch

/-! RCC-23 candidate: proof-carrying reepoch ancestry, trigger freshness and debt conservation. -/

namespace Residua.RCC.RCC23Target

open Residua.RCC

universe u v w x y

structure Certificate where
  parentDistinct :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      ReepochCert S parent successor → parent ≠ successor
  triggerFresh :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      (certificate : ReepochCert S parent successor) →
      ¬ OccurrenceConsumed S parent certificate.trigger.occurrence
  exactParent :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      ReepochCert S parent successor →
      S.parentEpoch successor = some parent
  occurrenceUnique :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {leftParent leftSuccessor rightParent rightSuccessor : S.Epoch}
      (left : ReepochCert S leftParent leftSuccessor)
      (right : ReepochCert S rightParent rightSuccessor),
      left.trigger.occurrence = right.trigger.occurrence →
      (leftParent, leftSuccessor) = (rightParent, rightSuccessor)
  oldDebtPreserved :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      (certificate : ReepochCert S parent successor) →
      ∀ oldGoal : S.Goal, S.nonterminal parent oldGoal →
        S.terminalAtMigration parent oldGoal ∨
          ∃ migration : GoalMigration S parent successor oldGoal,
            SemanticallyRefines S parent successor oldGoal migration.newGoal
  finiteProgress :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      (certificate : ReepochCert S parent successor) →
      certificate.lineage.IsFinite →
      S.epochMeasure successor < S.epochMeasure parent
  openAcyclic :
    ∀ {S : ReepochSystem.{u, v, w, x, y}}
      {parent successor : S.Epoch},
      (certificate : ReepochCert S parent successor) →
      certificate.lineage.IsOpen →
      ¬ ParentAncestor S successor parent

def certificate : Certificate where
  parentDistinct := fun certificate => reepoch_parent_ne_successor certificate
  triggerFresh := fun certificate => reepoch_trigger_is_fresh certificate
  exactParent := fun certificate => reepoch_binds_exact_parent certificate
  occurrenceUnique := fun left right same =>
    same_occurrence_reservation_unique left right same
  oldDebtPreserved := fun certificate oldGoal hnonterminal =>
    reepoch_preserves_old_debt certificate oldGoal hnonterminal
  finiteProgress := fun certificate isFinite =>
    finite_campaign_decreases certificate isFinite
  openAcyclic := fun certificate isOpen =>
    open_lineage_has_no_back_edge certificate isOpen

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC23Target

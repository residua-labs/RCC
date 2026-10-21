import RCC.GoalWork

/-!
# RCC-20 Goal Refinement Kernel

Goal refinement is forward-sound: satisfying every replacement must establish every
original goal. Registration preserves the original goal ledger and keeps registered
parents open; it does not grant waiver, reverse exactness, or dependency completeness.

Prelude-only Lean 4.14; no Mathlib, no `sorry`, no custom axioms (some theorems use the standard `propext` and `Quot.sound`).
-/

namespace Residua.RCC

universe u v w

/-- History-indexed meaning for the Goals owned by one Goal/Work system. -/
structure GoalSemantics (S : GoalWorkSystem.{u, v}) where
  History : Type w
  satisfied : History → S.Goal → Prop

/-- Every listed Goal is semantically satisfied in the selected history. -/
def GoalsSatisfied {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S) (history : G.History) (goals : List S.Goal) : Prop :=
  ∀ goal, goal ∈ goals → G.satisfied history goal

/--
A one-way refinement certificate. Replacements may be stronger than originals; reverse
exactness is deliberately not required.
-/
structure RefinementCert {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S)
    (originals replacements : List S.Goal) where
  originalsNonempty : originals ≠ []
  replacementsNonempty : replacements ≠ []
  forwardSufficient :
    ∀ history, GoalsSatisfied G history replacements →
      GoalsSatisfied G history originals

/-- Splitting one parent into multiple replacement children. -/
abbrev SplitRefinementCert {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S) (parent : S.Goal) (children : List S.Goal) :=
  RefinementCert G [parent] children

/-- Merging multiple original Goals into one replacement Goal. -/
abbrev MergeRefinementCert {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S) (originals : List S.Goal) (replacement : S.Goal) :=
  RefinementCert G originals [replacement]

/-- Satisfying every registered split child establishes the original parent meaning. -/
theorem split_refinement_sound {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics S} {parent : S.Goal} {children : List S.Goal}
    (certificate : SplitRefinementCert G parent children)
    (history : G.History)
    (hchildren : GoalsSatisfied G history children) :
    G.satisfied history parent :=
  certificate.forwardSufficient history hchildren parent (by simp)

/-- Satisfying a registered merge replacement establishes every original Goal. -/
theorem merge_refinement_sound {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics S} {originals : List S.Goal} {replacement : S.Goal}
    (certificate : MergeRefinementCert G originals replacement)
    (history : G.History)
    (hreplacement : G.satisfied history replacement) :
    GoalsSatisfied G history originals :=
  certificate.forwardSufficient history
    (by simpa [GoalsSatisfied] using hreplacement)

/--
Proof-carrying registration of a split. Registration retains the parent in the Goal
ledger and cannot close it merely because child Goals were introduced.
-/
structure SplitRegistration {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S)
    (before after : GoalWorkSnapshot S)
    (parent : S.Goal) (children : List S.Goal) where
  certificate : SplitRefinementCert G parent children
  childrenPresent :
    ∀ child, child ∈ children →
      after.goalPresent child = true
  parentPresencePreserved :
    after.goalPresent parent = before.goalPresent parent
  parentOpenPreserved :
    before.goalStatus parent = .open →
      after.goalStatus parent = .open

/--
Proof-carrying registration of a merge. Every original Goal remains present and open
while the replacement is registered.
-/
structure MergeRegistration {S : GoalWorkSystem.{u, v}}
    (G : GoalSemantics S)
    (before after : GoalWorkSnapshot S)
    (originals : List S.Goal) (replacement : S.Goal) where
  certificate : MergeRefinementCert G originals replacement
  replacementPresent :
    after.goalPresent replacement = true
  originalPresencePreserved :
    ∀ original, original ∈ originals →
      after.goalPresent original = before.goalPresent original
  originalOpenPreserved :
    ∀ original, original ∈ originals →
      before.goalStatus original = .open →
        after.goalStatus original = .open

/-- A split registration cannot delete or prematurely close its original parent. -/
theorem split_parent_not_dropped {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics S}
    {before after : GoalWorkSnapshot S}
    {parent : S.Goal} {children : List S.Goal}
    (registration : SplitRegistration G before after parent children)
    (hpresent : before.goalPresent parent = true)
    (hopen : before.goalStatus parent = .open) :
    after.goalPresent parent = true ∧
      after.goalStatus parent = .open :=
  ⟨registration.parentPresencePreserved.trans hpresent,
    registration.parentOpenPreserved hopen⟩

/-- A merge registration cannot delete or prematurely close any selected original Goal. -/
theorem merge_parent_not_dropped {S : GoalWorkSystem.{u, v}}
    {G : GoalSemantics S}
    {before after : GoalWorkSnapshot S}
    {originals : List S.Goal} {replacement : S.Goal}
    (registration : MergeRegistration G before after originals replacement)
    (parent : S.Goal)
    (hparent : parent ∈ originals)
    (hpresent : before.goalPresent parent = true)
    (hopen : before.goalStatus parent = .open) :
    after.goalPresent parent = true ∧
      after.goalStatus parent = .open :=
  ⟨(registration.originalPresencePreserved parent hparent).trans hpresent,
    registration.originalOpenPreserved parent hparent hopen⟩

end Residua.RCC


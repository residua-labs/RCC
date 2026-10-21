import RCC.QuorumIntersectionSafety

/-!
# RCC-40 Quorum Intersection Safety Witnesses

The load-bearing property is the general finite-set condition
`Q₁ ∩ Q₂ ⊄ F` for every pair of lawful quorums and every declared allowed
fault set.  Cardinality arithmetic appears only as a derived sanity check.
-/

namespace Residua.RCC.QuorumIntersectionSafety.Tests

open Residua.RCC.QuorumIntersectionSafety

private theorem mem_one_eq {α : Type} {value only : α}
    (listed : value ∈ [only]) : value = only := by
  rcases List.mem_cons.mp listed with equal | impossible
  · exact equal
  · cases impossible

private theorem mem_three_cases {α : Type} {value first second third : α}
    (listed : value ∈ [first, second, third]) :
    value = first ∨ value = second ∨ value = third := by
  rcases List.mem_cons.mp listed with equal | listed
  · exact Or.inl equal
  · rcases List.mem_cons.mp listed with equal | listed
    · exact Or.inr (Or.inl equal)
    · exact Or.inr (Or.inr (mem_one_eq listed))

private theorem mem_four_cases {α : Type}
    {value first second third fourth : α}
    (listed : value ∈ [first, second, third, fourth]) :
    value = first ∨ value = second ∨ value = third ∨ value = fourth := by
  rcases List.mem_cons.mp listed with equal | listed
  · exact Or.inl equal
  · rcases List.mem_cons.mp listed with equal | listed
    · exact Or.inr (Or.inl equal)
    · rcases List.mem_cons.mp listed with equal | listed
      · exact Or.inr (Or.inr (Or.inl equal))
      · exact Or.inr (Or.inr (Or.inr (mem_one_eq listed)))

private theorem mem_five_cases {α : Type}
    {value first second third fourth fifth : α}
    (listed : value ∈ [first, second, third, fourth, fifth]) :
    value = first ∨ value = second ∨ value = third ∨
      value = fourth ∨ value = fifth := by
  rcases List.mem_cons.mp listed with equal | listed
  · exact Or.inl equal
  · rcases List.mem_cons.mp listed with equal | listed
    · exact Or.inr (Or.inl equal)
    · rcases List.mem_cons.mp listed with equal | listed
      · exact Or.inr (Or.inr (Or.inl equal))
      · rcases List.mem_cons.mp listed with equal | listed
        · exact Or.inr (Or.inr (Or.inr (Or.inl equal)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (mem_one_eq listed))))

inductive Slot
  | deploy
  deriving DecidableEq

inductive Judgment
  | left
  | right
  deriving DecidableEq

inductive Member2
  | a
  | b
  deriving DecidableEq

private def member2DecidableEq : DecidableEq Member2 := by
  intro first second
  cases first <;> cases second <;> exact inferInstance

local instance explicitMember2DecidableEq : DecidableEq Member2 :=
  member2DecidableEq

def twoOfTwo : FiniteQuorumSystem where
  Member := Member2
  Slot := Slot
  Judgment := Judgment
  equivalent := Eq
  members := [.a, .b]
  quorums := [[.a, .b]]
  allowedFaultSets := [[], [.a], [.b]]

local instance explicitTwoOfTwoMemberDecidableEq :
    DecidableEq twoOfTwo.Member := member2DecidableEq

theorem two_of_two_f_one_general_intersection_safe :
    QuorumIntersectionSafe twoOfTwo := by
  intro first hfirst second hsecond fault hfault
  rcases hfirst with ⟨hfirstListed, hfirstNodup, hfirstMembers⟩
  rcases hsecond with ⟨hsecondListed, hsecondNodup, hsecondMembers⟩
  rcases hfault with ⟨hfaultListed, hfaultNodup, hfaultMembers⟩
  have hfirstEq : first = [.a, .b] := by
    apply mem_one_eq
    exact hfirstListed
  have hsecondEq : second = [.a, .b] := by
    apply mem_one_eq
    exact hsecondListed
  have hfaultCases : fault = [] ∨ fault = [.a] ∨ fault = [.b] := by
    exact mem_three_cases hfaultListed
  rcases hfirstEq with rfl
  rcases hsecondEq with rfl
  rcases hfaultCases with rfl | rfl | rfl
  ·
    exact ⟨.a, by simp⟩
  ·
    exact ⟨.b, by simp⟩
  ·
    exact ⟨.a, by simp⟩

theorem two_of_two_same_slot_qcs_agree
    (locks : VoteLockState twoOfTwo)
    (fault : List Member2)
    (hfault : AllowedFaultSet twoOfTwo fault)
    (honestLocks : HonestNonEquivocation twoOfTwo locks fault)
    {firstJudgment secondJudgment : Judgment}
    (firstQC : ValidQC twoOfTwo locks .deploy firstJudgment)
    (secondQC : ValidQC twoOfTwo locks .deploy secondJudgment) :
    firstJudgment = secondJudgment := by
  exact valid_qcs_same_slot_equivalent
    twoOfTwo locks two_of_two_f_one_general_intersection_safe
    fault hfault honestLocks firstQC secondQC

inductive Member3
  | a
  | b
  | c
  deriving DecidableEq

private def member3DecidableEq : DecidableEq Member3 := by
  intro first second
  cases first <;> cases second <;> exact inferInstance

local instance explicitMember3DecidableEq : DecidableEq Member3 :=
  member3DecidableEq

def twoOfThree : FiniteQuorumSystem where
  Member := Member3
  Slot := Slot
  Judgment := Judgment
  equivalent := Eq
  members := [.a, .b, .c]
  quorums := [[.a, .b], [.a, .c], [.b, .c]]
  allowedFaultSets := [[], [.a], [.b], [.c]]

local instance explicitTwoOfThreeMemberDecidableEq :
    DecidableEq twoOfThree.Member := member3DecidableEq

theorem two_of_three_ab_lawful :
    LawfulQuorum twoOfThree [.a, .b] := by
  refine ⟨by decide, by decide, ?_⟩
  · intro signer hsigner
    cases signer <;> decide

theorem two_of_three_ac_lawful :
    LawfulQuorum twoOfThree [.a, .c] := by
  refine ⟨by decide, by decide, ?_⟩
  · intro signer hsigner
    cases signer <;> decide

theorem two_of_three_fault_a_allowed :
    AllowedFaultSet twoOfThree [.a] := by
  refine ⟨by decide, by decide, ?_⟩
  · intro signer hsigner
    cases signer <;> decide

theorem two_of_three_f_one_general_intersection_fails :
    ¬ QuorumIntersectionSafe twoOfThree := by
  intro safe
  have honestIntersection := safe
    [.a, .b] two_of_three_ab_lawful
    [.a, .c] two_of_three_ac_lawful
    [.a] two_of_three_fault_a_allowed
  rcases honestIntersection with
    ⟨signer, hfirst, hsecond, hnotFaulty⟩
  cases signer <;> simp at hfirst hsecond hnotFaulty

def splitVoteLocks : VoteLockState twoOfThree where
  lockedVotes :=
    [ ⟨.a, .deploy, .left⟩
    , ⟨.a, .deploy, .right⟩
    , ⟨.b, .deploy, .left⟩
    , ⟨.c, .deploy, .right⟩
    ]

theorem b_locked_vote_is_left
    {slot : Slot} {judgment : Judgment}
    (locked : HasLockedVote splitVoteLocks .b slot judgment) :
    judgment = .left := by
  rcases locked with
    ⟨entry, hentry, hsigner, hslot, hjudgment⟩
  simp only [splitVoteLocks, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl
  · cases hsigner
  · cases hsigner
  · exact hjudgment.symm
  · cases hsigner

theorem c_locked_vote_is_right
    {slot : Slot} {judgment : Judgment}
    (locked : HasLockedVote splitVoteLocks .c slot judgment) :
    judgment = .right := by
  rcases locked with
    ⟨entry, hentry, hsigner, hslot, hjudgment⟩
  simp only [splitVoteLocks, List.mem_cons, List.not_mem_nil, or_false] at hentry
  rcases hentry with rfl | rfl | rfl | rfl
  · cases hsigner
  · cases hsigner
  · cases hsigner
  · exact hjudgment.symm

theorem split_vote_locks_are_honest_outside_a :
    HonestNonEquivocation twoOfThree splitVoteLocks [.a] := by
  intro signer hmember hhonest slot first second hfirst hsecond
  cases signer with
  | a => exact (hhonest (by simp)).elim
  | b =>
      have hfirstJudgment := b_locked_vote_is_left hfirst
      have hsecondJudgment := b_locked_vote_is_left hsecond
      subst first
      subst second
      rfl
  | c =>
      have hfirstJudgment := c_locked_vote_is_right hfirst
      have hsecondJudgment := c_locked_vote_is_right hsecond
      subst first
      subst second
      rfl

def leftQC : ValidQC twoOfThree splitVoteLocks .deploy .left where
  quorum := [.a, .b]
  lawful := two_of_three_ab_lawful
  votes := by
    intro signer hsigner
    cases signer <;>
      simp [HasLockedVote, splitVoteLocks] at hsigner ⊢

def rightQC : ValidQC twoOfThree splitVoteLocks .deploy .right where
  quorum := [.a, .c]
  lawful := two_of_three_ac_lawful
  votes := by
    intro signer hsigner
    cases signer <;>
      simp [HasLockedVote, splitVoteLocks] at hsigner ⊢

/--
Countermodel: A double-signs while B and C split, yielding two same-slot valid
QCs for inequivalent judgments.  The only common signer is in the allowed fault
set, so honest non-equivocation cannot bridge the two certificates.
-/
theorem two_of_three_double_sign_split_countermodel :
    AllowedFaultSet twoOfThree [.a] ∧
      HonestNonEquivocation twoOfThree splitVoteLocks [.a] ∧
      Nonempty (ValidQC twoOfThree splitVoteLocks .deploy .left) ∧
      Nonempty (ValidQC twoOfThree splitVoteLocks .deploy .right) ∧
      ¬ twoOfThree.equivalent .left .right ∧
      ¬ QuorumIntersectionSafe twoOfThree := by
  exact
    ⟨two_of_three_fault_a_allowed,
      split_vote_locks_are_honest_outside_a,
      ⟨leftQC⟩,
      ⟨rightQC⟩,
      by simp [twoOfThree],
      two_of_three_f_one_general_intersection_fails⟩

inductive Member4
  | a
  | b
  | c
  | d
  deriving DecidableEq

private def member4DecidableEq : DecidableEq Member4 := by
  intro first second
  cases first <;> cases second <;> exact inferInstance

local instance explicitMember4DecidableEq : DecidableEq Member4 :=
  member4DecidableEq

def threeOfFour : FiniteQuorumSystem where
  Member := Member4
  Slot := Slot
  Judgment := Judgment
  equivalent := Eq
  members := [.a, .b, .c, .d]
  quorums :=
    [[.a, .b, .c], [.a, .b, .d], [.a, .c, .d], [.b, .c, .d]]
  allowedFaultSets := [[], [.a], [.b], [.c], [.d]]

local instance explicitThreeOfFourMemberDecidableEq :
    DecidableEq threeOfFour.Member := member4DecidableEq

theorem three_of_four_f_one_general_intersection_safe :
    QuorumIntersectionSafe threeOfFour := by
  intro first hfirst second hsecond fault hfault
  rcases hfirst with ⟨hfirstListed, hfirstNodup, hfirstMembers⟩
  rcases hsecond with ⟨hsecondListed, hsecondNodup, hsecondMembers⟩
  rcases hfault with ⟨hfaultListed, hfaultNodup, hfaultMembers⟩
  have hfirstCases :
      first = [.a, .b, .c] ∨ first = [.a, .b, .d] ∨
        first = [.a, .c, .d] ∨ first = [.b, .c, .d] := by
    exact mem_four_cases hfirstListed
  have hsecondCases :
      second = [.a, .b, .c] ∨ second = [.a, .b, .d] ∨
        second = [.a, .c, .d] ∨ second = [.b, .c, .d] := by
    exact mem_four_cases hsecondListed
  have hfaultCases :
      fault = [] ∨ fault = [.a] ∨ fault = [.b] ∨
        fault = [.c] ∨ fault = [.d] := by
    exact mem_five_cases hfaultListed
  rcases hfirstCases with rfl | rfl | rfl | rfl <;>
    rcases hsecondCases with rfl | rfl | rfl | rfl <;>
      rcases hfaultCases with rfl | rfl | rfl | rfl | rfl <;>
        decide

/--
These arithmetic facts match the finite examples but are not used by either
general intersection proof.
-/
theorem cardinality_corollary_sanity_only :
    2 * 2 > 2 + 1 ∧
      ¬ 2 * 2 > 3 + 1 ∧
      2 * 3 > 4 + 1 := by
  decide

#print axioms valid_qcs_same_slot_equivalent
#print axioms two_of_two_f_one_general_intersection_safe
#print axioms two_of_two_same_slot_qcs_agree
#print axioms two_of_three_double_sign_split_countermodel
#print axioms three_of_four_f_one_general_intersection_safe
#print axioms cardinality_corollary_sanity_only

end Residua.RCC.QuorumIntersectionSafety.Tests

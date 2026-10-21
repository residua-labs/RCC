import RCC.AddressedGraphPermutation

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph

namespace Residua.RCC.Addressing.AddressedGraph.Permutation.Tests

/-! AK-6B freezes executable enumeration and universal finite-order laws. -/

theorem permutations_complete_contract :
    ∀ n candidate,
      IsPermutation candidate (range n) →
      candidate ∈ permutations (range n) :=
  permutations_range_complete

theorem permutations_range_nodup_contract :
    ∀ n, NoDuplicates (permutations (range n)) :=
  permutations_range_no_duplicates

theorem permutations_nodup_contract :
    ∀ {α : Type} (values : List α),
      NoDuplicates values →
      NoDuplicates (permutations values) :=
  permutations_no_duplicates_of_no_duplicates

theorem permutations_sound_contract :
    ∀ n candidate,
      candidate ∈ permutations (range n) →
      IsPermutation candidate (range n) :=
  permutations_range_sound

/-! These exact computations prevent an empty or bounded dummy enumerator. -/
example : permutations (range 0) = [[]] := by decide
example : permutations (range 1) = [[0]] := by decide
example :
    permutations (range 2) = [[0, 1], [1, 0]] := by decide
example :
    permutations (range 3) =
      [[0, 1, 2], [1, 0, 2], [1, 2, 0],
       [0, 2, 1], [2, 0, 1], [2, 1, 0]] := by decide

/-! Every admitted permutation exposes both inverse laws, not only a list
membership theorem. -/
theorem inverse_permutation_left_contract
    (permutation : PermutationWitness n) :
    ∀ index,
      (permutationBijection permutation).inverse
          ((permutationBijection permutation).forward index) = index :=
  (permutationBijection permutation).leftInverse

theorem inverse_permutation_right_contract
    (permutation : PermutationWitness n) :
    ∀ index,
      (permutationBijection permutation).forward
          ((permutationBijection permutation).inverse index) = index :=
  (permutationBijection permutation).rightInverse

theorem graph_byte_reverse_lt_contract :
    ∀ left right,
      compareGraphBytes left right = .lt →
      compareGraphBytes right left = .gt :=
  compare_graph_bytes_reverse_lt

theorem graph_byte_lt_transitive_contract :
    ∀ first second third,
      compareGraphBytes first second = .lt →
      compareGraphBytes second third = .lt →
      compareGraphBytes first third = .lt :=
  compare_graph_bytes_lt_transitive

theorem graph_byte_trichotomy_contract :
    ∀ left right,
      compareGraphBytes left right = .lt ∨
      compareGraphBytes left right = .eq ∨
      compareGraphBytes left right = .gt :=
  compare_graph_bytes_trichotomy

theorem minimum_member_contract
    (nonempty : candidates ≠ []) :
    lexicographicMinimum candidates nonempty ∈ candidates :=
  lexicographic_minimum_mem candidates nonempty

theorem minimum_lower_bound_contract
    (nonempty : candidates ≠ []) :
    ∀ candidate ∈ candidates,
      compareGraphBytes
        (lexicographicMinimum candidates nonempty) candidate ≠ .gt :=
  lexicographic_minimum_lower_bound candidates nonempty

/-! A concrete heterogeneous candidate bijection exercises the exact carrier,
its inverse laws, encoding preservation, and minimizer theorem. -/
def leftCandidates : List Nat := [0, 1]
def rightCandidates : List Bool := [false, true]
def leftEncoding : Nat → GraphBytes
  | 0 => [4, 2]
  | _ => [9]
def rightEncoding : Bool → GraphBytes
  | false => [4, 2]
  | true => [9]

def concreteEncodingBijection :
    CandidateEncodingBijection leftCandidates rightCandidates
      leftEncoding rightEncoding where
  leftNoDuplicates := by decide
  rightNoDuplicates := by decide
  forward
    | 0 => false
    | _ => true
  inverse
    | false => 0
    | true => 1
  forwardMember := by
    intro candidate member
    simp [leftCandidates] at member
    rcases member with rfl | rfl <;> decide
  inverseMember := by
    intro candidate member
    cases candidate <;> decide
  leftInverse := by
    intro candidate member
    simp [leftCandidates] at member
    rcases member with rfl | rfl <;> rfl
  rightInverse := by
    intro candidate member
    cases candidate <;> rfl
  encodingPreserved := by
    intro candidate member
    simp [leftCandidates] at member
    rcases member with rfl | rfl <;> rfl

theorem concrete_minimizer_bijection_contract :
    minimizerCount leftEncoding leftCandidates =
      minimizerCount rightEncoding rightCandidates :=
  minimizer_count_preserved_by_candidate_bijection concreteEncodingBijection

example : minimizerCount leftEncoding leftCandidates = 1 := by decide
example : compareGraphBytes [1, 9] [2] = .lt := by decide
example :
    lexicographicMinimum [[3], [1, 9], [2]] (by decide) = [1, 9] := by
  decide

#print axioms permutations_range_sound
#print axioms permutations_range_complete
#print axioms permutations_range_no_duplicates
#print axioms permutations_no_duplicates_of_no_duplicates
#print axioms compare_graph_bytes_eq_iff
#print axioms compare_graph_bytes_lt_transitive
#print axioms compare_graph_bytes_trichotomy
#print axioms minimizer_count_preserved_by_candidate_bijection
#print axioms concrete_minimizer_bijection_contract

end Residua.RCC.Addressing.AddressedGraph.Permutation.Tests


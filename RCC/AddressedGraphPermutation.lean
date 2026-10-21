import RCC.AddressedGraphClosure

/-!
# RCC addressed-graph finite permutation kernel

This module enumerates every finite local relabeling and supplies the total
byte order and finite-minimum facts used by AK-6B canonicalization.
-/

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressedGraph

abbrev IsPermutation (left right : List α) : Prop :=
  List.Perm left right

abbrev NoDuplicates (values : List α) : Prop :=
  values.Pairwise (fun left right => left ≠ right)

def range : Nat → List Nat :=
  List.range

def insertEverywhere (value : α) : List α → List (List α)
  | [] => [[value]]
  | head :: tail =>
      (value :: head :: tail) ::
        (insertEverywhere value tail).map (fun rest => head :: rest)

def permutations : List α → List (List α)
  | [] => [[]]
  | head :: tail =>
      (permutations tail).flatMap (insertEverywhere head)

theorem insert_everywhere_sound
    {value : α} {values candidate : List α}
    (member : candidate ∈ insertEverywhere value values) :
    IsPermutation candidate (value :: values) := by
  induction values generalizing candidate with
  | nil =>
      simp [insertEverywhere] at member
      subst candidate
      exact .rfl
  | cons head tail ih =>
      simp [insertEverywhere] at member
      rcases member with rfl | ⟨rest, restMember, rfl⟩
      · exact .rfl
      · exact (ih restMember).cons head |>.trans (.swap value head tail)

theorem insert_everywhere_complete_at_prefix
    (pre suffix : List α) (value : α) :
    pre ++ value :: suffix ∈
      insertEverywhere value (pre ++ suffix) := by
  induction pre with
  | nil =>
      cases suffix <;> simp [insertEverywhere]
  | cons head tail ih =>
      simp [insertEverywhere, ih]

theorem insert_everywhere_complete
    {value : α} {values candidate : List α}
    (permuted : IsPermutation candidate (value :: values)) :
    ∃ remainder,
      IsPermutation remainder values ∧
      candidate ∈ insertEverywhere value remainder := by
  have valueMember : value ∈ candidate :=
    permuted.symm.subset (by simp)
  obtain ⟨pre, suffix, candidateExact⟩ :=
    List.append_of_mem valueMember
  subst candidate
  have remainderPermuted :
      IsPermutation (pre ++ suffix) values :=
    List.perm_inv_core (l₁ := pre) (r₁ := suffix)
      (l₂ := []) (r₂ := values) (by simpa using permuted)
  have inserted :=
    insert_everywhere_complete_at_prefix pre suffix value
  exact ⟨pre ++ suffix, remainderPermuted, inserted⟩

theorem permutations_sound :
    ∀ {values candidate : List α},
      candidate ∈ permutations values →
      IsPermutation candidate values := by
  intro values
  induction values with
  | nil =>
      intro candidate member
      simp [permutations] at member
      subst candidate
      exact .rfl
  | cons head tail ih =>
      intro candidate member
      simp [permutations] at member
      rcases member with ⟨tailCandidate, tailMember, candidateMember⟩
      exact (insert_everywhere_sound candidateMember).trans
        ((ih tailMember).cons head)

theorem permutations_complete :
    ∀ {values candidate : List α},
      IsPermutation candidate values →
      candidate ∈ permutations values := by
  intro values
  induction values with
  | nil =>
      intro candidate permuted
      have candidateExact : candidate = [] := permuted.eq_nil
      subst candidate
      simp [permutations]
  | cons head tail ih =>
      intro candidate permuted
      obtain ⟨remainder, remainderPermuted, inserted⟩ :=
        insert_everywhere_complete permuted
      have remainderMember : remainder ∈ permutations tail :=
        ih remainderPermuted
      simp [permutations]
      exact ⟨remainder, remainderMember, inserted⟩

private theorem insert_everywhere_cons_member
    {value head : α} {tail candidate : List α}
    (member :
      candidate ∈ insertEverywhere value (head :: tail)) :
    candidate = value :: head :: tail ∨
      ∃ rest,
        rest ∈ insertEverywhere value tail ∧
          candidate = head :: rest := by
  have outer :
      candidate = value :: head :: tail ∨
        candidate ∈
          (insertEverywhere value tail).map
            (fun rest => head :: rest) := by
    exact List.mem_cons.mp member
  cases outer with
  | inl exactHead =>
      exact Or.inl exactHead
  | inr mapped =>
      obtain ⟨rest, restMember, exactCandidate⟩ :=
        List.mem_map.mp mapped
      exact Or.inr ⟨rest, restMember, exactCandidate.symm⟩

private theorem insert_everywhere_nil_member
    {value : α} {candidate : List α}
    (member : candidate ∈ insertEverywhere value []) :
    candidate = [value] := by
  have outer : candidate = [value] ∨ candidate ∈ [] :=
    List.mem_cons.mp member
  cases outer with
  | inl exactCandidate =>
      exact exactCandidate
  | inr impossible =>
      exact nomatch impossible

theorem insert_everywhere_source_unique
    {value : α} {left right candidate : List α}
    (valueNotLeft : value ∉ left)
    (valueNotRight : value ∉ right)
    (leftMember : candidate ∈ insertEverywhere value left)
    (rightMember : candidate ∈ insertEverywhere value right) :
    left = right := by
  induction left generalizing right candidate with
  | nil =>
      have candidateExact :=
        insert_everywhere_nil_member leftMember
      cases right with
      | nil =>
          rfl
      | cons rightHead rightTail =>
          have rightShape :=
            insert_everywhere_cons_member rightMember
          cases rightShape with
          | inl rightAtHead =>
              rw [candidateExact] at rightAtHead
              cases rightAtHead
          | inr rightBelow =>
              obtain ⟨rightRest, _, rightExact⟩ := rightBelow
              rw [candidateExact] at rightExact
              have headExact : rightHead = value :=
                List.cons.inj rightExact.symm |>.1
              apply False.elim
              apply valueNotRight
              rw [headExact]
              exact List.mem_cons.mpr (Or.inl rfl)
  | cons leftHead leftTail ih =>
      cases right with
      | nil =>
          have candidateExact :=
            insert_everywhere_nil_member rightMember
          have leftShape :=
            insert_everywhere_cons_member leftMember
          cases leftShape with
          | inl leftAtHead =>
              rw [candidateExact] at leftAtHead
              cases leftAtHead
          | inr leftBelow =>
              obtain ⟨leftRest, _, leftExact⟩ := leftBelow
              rw [candidateExact] at leftExact
              have headExact : leftHead = value :=
                List.cons.inj leftExact.symm |>.1
              apply False.elim
              apply valueNotLeft
              rw [headExact]
              exact List.mem_cons.mpr (Or.inl rfl)
      | cons rightHead rightTail =>
          have leftShape :=
            insert_everywhere_cons_member leftMember
          have rightShape :=
            insert_everywhere_cons_member rightMember
          cases leftShape with
          | inl leftAtHead =>
              cases rightShape with
              | inl rightAtHead =>
                  rw [leftAtHead] at rightAtHead
                  exact List.cons.inj rightAtHead |>.2
              | inr rightBelow =>
                  obtain ⟨rightRest, _, rightExact⟩ := rightBelow
                  rw [leftAtHead] at rightExact
                  have headExact : rightHead = value :=
                    List.cons.inj rightExact.symm |>.1
                  apply False.elim
                  apply valueNotRight
                  rw [headExact]
                  exact List.mem_cons.mpr (Or.inl rfl)
          | inr leftBelow =>
              obtain ⟨leftRest, leftRestMember, leftExact⟩ :=
                leftBelow
              cases rightShape with
              | inl rightAtHead =>
                  rw [leftExact] at rightAtHead
                  have headExact : leftHead = value :=
                    List.cons.inj rightAtHead |>.1
                  apply False.elim
                  apply valueNotLeft
                  rw [headExact]
                  exact List.mem_cons.mpr (Or.inl rfl)
              | inr rightBelow =>
                  obtain ⟨rightRest, rightRestMember, rightExact⟩ :=
                    rightBelow
                  rw [leftExact] at rightExact
                  have headsExact : leftHead = rightHead :=
                    List.cons.inj rightExact |>.1
                  have restsExact : leftRest = rightRest :=
                    List.cons.inj rightExact |>.2
                  subst rightHead
                  subst rightRest
                  have valueNotLeftTail : value ∉ leftTail := by
                    intro member
                    exact valueNotLeft
                      (List.mem_cons_of_mem leftHead member)
                  have valueNotRightTail : value ∉ rightTail := by
                    intro member
                    exact valueNotRight
                      (List.mem_cons_of_mem leftHead member)
                  have tailsExact :=
                    ih valueNotLeftTail valueNotRightTail
                      leftRestMember rightRestMember
                  rw [tailsExact]

theorem insert_everywhere_no_duplicates
    {value : α} {values : List α}
    (valueNotMem : value ∉ values) :
    NoDuplicates (insertEverywhere value values) := by
  induction values with
  | nil =>
      simp [NoDuplicates, insertEverywhere]
  | cons head tail ih =>
      have valueNeHead : value ≠ head := by
        intro equal
        exact valueNotMem (by simp [equal])
      have valueNotTail : value ∉ tail := by
        intro member
        exact valueNotMem (by simp [member])
      simp only [insertEverywhere, List.pairwise_cons]
      constructor
      · intro candidate candidateMember equal
        simp at candidateMember
        rcases candidateMember with ⟨rest, restMember, rfl⟩
        cases equal
        exact valueNeHead rfl
      · rw [List.pairwise_map]
        exact (ih valueNotTail).imp (by
          intro left right different equal
          exact different (List.cons.inj equal |>.2))

theorem permutations_no_duplicates_of_no_duplicates :
    ∀ {α : Type} (values : List α),
      NoDuplicates values →
      NoDuplicates (permutations values) := by
  intro α values
  induction values with
  | nil =>
      intro _
      simp [NoDuplicates, permutations]
  | cons head tail ih =>
      intro valuesNoDuplicates
      have headNotTail : head ∉ tail := by
        intro headMember
        exact
          ((List.pairwise_cons.mp valuesNoDuplicates).1 head headMember) rfl
      have tailNoDuplicates : NoDuplicates tail :=
        (List.pairwise_cons.mp valuesNoDuplicates).2
      rw [permutations]
      change List.Pairwise (fun left right => left ≠ right)
        ((permutations tail).flatMap (insertEverywhere head))
      rw [List.pairwise_flatMap]
      constructor
      · intro candidate candidateMember
        have candidatePermuted : IsPermutation candidate tail :=
          permutations_sound candidateMember
        apply insert_everywhere_no_duplicates
        intro headMember
        exact headNotTail (candidatePermuted.subset headMember)
      · have outerNoDuplicates := ih tailNoDuplicates
        rw [List.Pairwise.imp_mem]
        refine outerNoDuplicates.imp ?_
        intro left right different leftMember rightMember
        intro leftResult leftResultMember rightResult rightResultMember equal
        apply different
        apply insert_everywhere_source_unique
        · intro headMember
          exact headNotTail
            ((permutations_sound leftMember).subset headMember)
        · intro headMember
          exact headNotTail
            ((permutations_sound rightMember).subset headMember)
        · exact leftResultMember
        · simpa [equal] using rightResultMember

theorem range_no_duplicates :
    ∀ n, NoDuplicates (range n) := by
  intro n
  induction n with
  | zero =>
      exact List.Pairwise.nil
  | succ n ih =>
      rw [range, List.range_succ]
      change
        List.Pairwise (fun left right : Nat => left ≠ right)
          (List.range n ++ [n])
      rw [List.pairwise_append]
      refine ⟨ih, List.Pairwise.cons ?_ List.Pairwise.nil, ?_⟩
      · intro value impossible
        exact nomatch impossible
      · intro left leftMember right rightMember
        have rightExact : right = n :=
          List.mem_singleton.mp rightMember
        subst right
        exact Nat.ne_of_lt (List.mem_range.mp leftMember)

theorem permutations_range_no_duplicates :
    ∀ n, NoDuplicates (permutations (range n)) := by
  intro n
  exact permutations_no_duplicates_of_no_duplicates
    (range n) (range_no_duplicates n)

theorem permutations_range_complete :
    ∀ n candidate,
      IsPermutation candidate (range n) →
      candidate ∈ permutations (range n) := by
  intro n candidate
  exact permutations_complete

theorem permutations_range_sound :
    ∀ n candidate,
      candidate ∈ permutations (range n) →
      IsPermutation candidate (range n) := by
  intro n candidate
  exact permutations_sound

structure PermutationWitness (n : Nat) where
  values : List Nat
  permutesRange : IsPermutation values (range n)

def permutationWitnesses (n : Nat) :
    List (PermutationWitness n) :=
  (permutations (range n)).attach.map fun candidate =>
    ⟨candidate.val,
      permutations_range_sound n candidate.val candidate.property⟩

theorem attach_no_duplicates
    {values : List α}
    (noDuplicates : NoDuplicates values) :
    NoDuplicates values.attach := by
  have mapped :
      List.Pairwise (fun left right : α => left ≠ right)
        (values.attach.map (fun item => item.val)) := by
    change
      List.Pairwise (fun left right : α => left ≠ right)
        values.attach.unattach
    rw [List.unattach_attach]
    exact noDuplicates
  have valuesDifferent :
      List.Pairwise
        (fun left right : { value // value ∈ values } =>
          left.val ≠ right.val)
        values.attach :=
    (List.pairwise_map
      (f := fun item : { value // value ∈ values } => item.val)
      (R := fun left right : α => left ≠ right)).mp mapped
  exact valuesDifferent.imp (by
    intro left right different equal
    exact different (congrArg Subtype.val equal))

theorem permutation_witness_ext
    (left right : PermutationWitness n)
    (valuesExact : left.values = right.values) :
    left = right := by
  cases left
  cases right
  simp only [PermutationWitness.mk.injEq]
  exact valuesExact

theorem permutation_witnesses_complete
    (witness : PermutationWitness n) :
    witness ∈ permutationWitnesses n := by
  let candidate :
      { values // values ∈ permutations (range n) } :=
    ⟨witness.values,
      permutations_range_complete n witness.values
        witness.permutesRange⟩
  apply List.mem_map.mpr
  refine ⟨candidate, List.mem_attach _ candidate, ?_⟩
  apply permutation_witness_ext
  rfl

theorem permutation_witnesses_no_duplicates (n : Nat) :
    NoDuplicates (permutationWitnesses n) := by
  unfold permutationWitnesses
  change
    List.Pairwise
      (fun left right : PermutationWitness n => left ≠ right)
      ((permutations (range n)).attach.map fun candidate =>
        ⟨candidate.val,
          permutations_range_sound n candidate.val candidate.property⟩)
  rw [List.pairwise_map]
  exact
    (attach_no_duplicates (permutations_range_no_duplicates n)).imp (by
      intro left right different equal
      apply different
      apply Subtype.ext
      exact congrArg PermutationWitness.values equal)

theorem permutation_witnesses_nonempty (n : Nat) :
    permutationWitnesses n ≠ [] := by
  intro empty
  have sourceEmpty : permutations (range n) = [] := by
    simpa [permutationWitnesses] using empty
  have selfMember :
      range n ∈ permutations (range n) :=
    permutations_range_complete n (range n) (.refl _)
  rw [sourceEmpty] at selfMember
  simp at selfMember

def indexOfMember [DecidableEq α]
    (value : α) :
    (values : List α) → value ∈ values → Fin values.length
  | [], member => False.elim (by simp at member)
  | head :: tail, member =>
      if equal : value = head then
        ⟨0, by simp⟩
      else
        let tailIndex :=
          indexOfMember value tail
            ((List.mem_cons.mp member).resolve_left equal)
        ⟨tailIndex.val + 1, by
          simpa [Nat.add_comm] using Nat.succ_lt_succ tailIndex.isLt⟩

theorem get_indexOfMember [DecidableEq α]
    (value : α) (values : List α) (member : value ∈ values) :
    values.get (indexOfMember value values member) = value := by
  induction values with
  | nil =>
      simp at member
  | cons head tail ih =>
      by_cases equal : value = head
      · subst head
        simp [indexOfMember]
      · simp only [indexOfMember, equal]
        exact ih ((List.mem_cons.mp member).resolve_left equal)

theorem get_mem_compat
    (values : List α) (index : Fin values.length) :
    values.get index ∈ values := by
  induction values with
  | nil =>
      exact Fin.elim0 index
  | cons head tail ih =>
      cases index with
      | mk indexValue indexBound =>
          cases indexValue with
          | zero =>
              simp
          | succ tailIndex =>
              have tailBound : tailIndex < tail.length := by
                simpa using indexBound
              exact List.mem_cons_of_mem head
                (ih ⟨tailIndex, tailBound⟩)

theorem indexOfMember_get [DecidableEq α]
    (values : List α)
    (noDuplicates : NoDuplicates values)
    (index : Fin values.length) :
    indexOfMember (values.get index) values
        (get_mem_compat values index) =
      index := by
  induction values with
  | nil =>
      exact Fin.elim0 index
  | cons head tail ih =>
      have tailNoDuplicates : NoDuplicates tail :=
        (List.pairwise_cons.mp noDuplicates).2
      cases index with
      | mk indexValue indexBound =>
          cases indexValue with
          | zero =>
              apply Fin.ext
              simp [indexOfMember]
          | succ tailIndex =>
              have tailBound : tailIndex < tail.length := by
                simpa using indexBound
              let tailFin : Fin tail.length := ⟨tailIndex, tailBound⟩
              have valueNotHead : tail.get tailFin ≠ head := by
                intro equal
                exact
                  ((List.pairwise_cons.mp noDuplicates).1
                    (tail.get tailFin)
                    (get_mem_compat tail tailFin)) equal.symm
              apply Fin.ext
              suffices
                  ∀ (value : α) (member : value ∈ head :: tail),
                    value = tail.get tailFin →
                    (indexOfMember value (head :: tail) member).val =
                      tailIndex + 1 by
                apply this
                exact List.get_cons_succ
              intro value member valueExact
              subst value
              simp only [indexOfMember, valueNotHead]
              exact congrArg (fun current => current + 1)
                (congrArg Fin.val (ih tailNoDuplicates tailFin))

theorem permutation_length_eq
    {n : Nat} {values : List Nat}
    (sound : IsPermutation values (range n)) :
    values.length = n := by
  simpa [range] using sound.length_eq

def permutationForward
    (n : Nat) (permutation : List Nat)
    (sound : IsPermutation permutation (range n)) :
    Fin n → Fin n :=
  fun index =>
    let member : index.val ∈ permutation :=
      sound.symm.subset (by simp [range, index.isLt])
    let position := indexOfMember index.val permutation member
    ⟨position.val, by
      rw [← permutation_length_eq sound]
      exact position.isLt⟩

def inversePermutation
    (n : Nat) (permutation : List Nat)
    (sound : IsPermutation permutation (range n)) :
    Fin n → Fin n :=
  fun index =>
    let position : Fin permutation.length :=
      ⟨index.val, by
        rw [permutation_length_eq sound]
        exact index.isLt⟩
    let value := permutation.get position
    ⟨value, by
      have member : value ∈ permutation :=
        get_mem_compat permutation position
      have rangeMember : value ∈ range n :=
        sound.subset member
      simpa [range] using rangeMember⟩

structure LocalBijection (n : Nat) where
  forward : Fin n → Fin n
  inverse : Fin n → Fin n
  leftInverse : ∀ index, inverse (forward index) = index
  rightInverse : ∀ index, forward (inverse index) = index

def permutationBijection
    {n : Nat} (permutation : PermutationWitness n) :
    LocalBijection n where
  forward :=
    permutationForward n permutation.values permutation.permutesRange
  inverse :=
    inversePermutation n permutation.values permutation.permutesRange
  leftInverse := by
    intro index
    apply Fin.ext
    simp only [permutationForward, inversePermutation]
    exact get_indexOfMember index.val permutation.values
      (permutation.permutesRange.symm.subset
        (by simp [range, index.isLt]))
  rightInverse := by
    intro index
    apply Fin.ext
    simp only [permutationForward, inversePermutation]
    let position : Fin permutation.values.length :=
      ⟨index.val, by
        rw [permutation_length_eq permutation.permutesRange]
        exact index.isLt⟩
    have noDuplicates : NoDuplicates permutation.values :=
      List.Perm.pairwise permutation.permutesRange.symm
        (range_no_duplicates n)
        (fun different => different.symm)
    exact congrArg Fin.val
      (indexOfMember_get permutation.values noDuplicates position)

def compareGraphBytes : GraphBytes → GraphBytes → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | left :: leftRest, right :: rightRest =>
      match compare left right with
      | .eq => compareGraphBytes leftRest rightRest
      | order => order

inductive GraphBytesLess : GraphBytes → GraphBytes → Prop
  | nilCons (head : Nat) (tail : GraphBytes) :
      GraphBytesLess [] (head :: tail)
  | headLt {left right : Nat} {leftRest rightRest : GraphBytes} :
      left < right →
      GraphBytesLess (left :: leftRest) (right :: rightRest)
  | tail {head : Nat} {leftRest rightRest : GraphBytes} :
      GraphBytesLess leftRest rightRest →
      GraphBytesLess (head :: leftRest) (head :: rightRest)

theorem compare_graph_bytes_lt_iff :
    ∀ {left right},
      compareGraphBytes left right = .lt ↔
      GraphBytesLess left right := by
  intro left
  induction left with
  | nil =>
      intro right
      cases right with
      | nil =>
          constructor
          · intro impossible
            contradiction
          · intro impossible
            cases impossible
      | cons head tail =>
          constructor
          · intro _
            exact GraphBytesLess.nilCons head tail
          · intro _
            rfl
  | cons leftHead leftRest ih =>
      intro right
      cases right with
      | nil =>
          simp [compareGraphBytes]
          intro impossible
          cases impossible
      | cons rightHead rightRest =>
          by_cases headsEqual : leftHead = rightHead
          · subst rightHead
            have headsCompared :
                compare leftHead leftHead = .eq :=
              Nat.compare_eq_eq.mpr rfl
            rw [compareGraphBytes, headsCompared, ih]
            constructor
            · intro tailLess
              exact GraphBytesLess.tail tailLess
            · intro less
              cases less with
              | headLt headLess =>
                  exact False.elim ((Nat.lt_irrefl leftHead) headLess)
              | tail tailLess =>
                  exact tailLess
          · cases compared : compare leftHead rightHead with
            | lt =>
                have headLess : leftHead < rightHead :=
                  Nat.compare_eq_lt.mp compared
                constructor
                · intro _
                  exact GraphBytesLess.headLt headLess
                · intro _
                  simp [compareGraphBytes, compared]
            | eq =>
                have equal : leftHead = rightHead :=
                  Nat.compare_eq_eq.mp compared
                exact False.elim (headsEqual equal)
            | gt =>
                have rightLess : rightHead < leftHead :=
                  Nat.compare_eq_gt.mp compared
                constructor
                · intro impossible
                  simp [compareGraphBytes, compared] at impossible
                intro less
                cases less with
                | headLt leftLess =>
                    exact False.elim
                      ((Nat.not_lt_of_ge (Nat.le_of_lt rightLess)) leftLess)
                | tail tailLess =>
                    exact False.elim (headsEqual rfl)

theorem graph_bytes_less_transitive :
    ∀ {first second third},
      GraphBytesLess first second →
      GraphBytesLess second third →
      GraphBytesLess first third := by
  intro first second third firstSecond secondThird
  induction firstSecond generalizing third with
  | nilCons secondHead secondTail =>
      cases third with
      | nil =>
          cases secondThird
      | cons thirdHead thirdTail =>
          exact GraphBytesLess.nilCons thirdHead thirdTail
  | @headLt firstHead secondHead firstTail secondTail headLess =>
      cases secondThird with
      | headLt secondLess =>
          exact GraphBytesLess.headLt
            (Nat.lt_trans headLess secondLess)
      | tail tailLess =>
          exact GraphBytesLess.headLt headLess
  | @tail head firstTail secondTail firstSecondTail ih =>
      cases secondThird with
      | headLt headLess =>
          exact GraphBytesLess.headLt headLess
      | tail secondThirdTail =>
          exact GraphBytesLess.tail (ih secondThirdTail)

theorem compare_graph_bytes_reverse_lt :
    ∀ left right,
      compareGraphBytes left right = .lt →
      compareGraphBytes right left = .gt := by
  intro left
  induction left with
  | nil =>
      intro right less
      cases right <;> simp [compareGraphBytes] at less ⊢
  | cons leftHead leftRest ih =>
      intro right less
      cases right with
      | nil =>
          simp [compareGraphBytes] at less
      | cons rightHead rightRest =>
          cases compared : compare leftHead rightHead with
          | lt =>
              have swapped :
                  compare rightHead leftHead = .gt := by
                rw [← Nat.compare_swap]
                simp only [compared, Ordering.swap]
              simp [compareGraphBytes, swapped]
          | eq =>
              have swapped :
                  compare rightHead leftHead = .eq := by
                rw [← Nat.compare_swap]
                simp only [compared, Ordering.swap]
              simp [compareGraphBytes, compared] at less
              simpa [compareGraphBytes, swapped] using ih rightRest less
          | gt =>
              simp [compareGraphBytes, compared] at less

theorem compare_graph_bytes_lt_transitive :
    ∀ first second third,
      compareGraphBytes first second = .lt →
      compareGraphBytes second third = .lt →
      compareGraphBytes first third = .lt := by
  intro first second third firstSecond secondThird
  exact compare_graph_bytes_lt_iff.mpr
    (graph_bytes_less_transitive
      (compare_graph_bytes_lt_iff.mp firstSecond)
      (compare_graph_bytes_lt_iff.mp secondThird))

theorem compare_graph_bytes_trichotomy :
    ∀ left right,
      compareGraphBytes left right = .lt ∨
      compareGraphBytes left right = .eq ∨
      compareGraphBytes left right = .gt := by
  intro left right
  generalize compareGraphBytes left right = result
  cases result <;> simp_all

theorem compare_graph_bytes_swap :
    ∀ left right,
      (compareGraphBytes left right).swap =
      compareGraphBytes right left := by
  intro left
  induction left with
  | nil =>
      intro right
      cases right <;> rfl
  | cons leftHead leftRest ih =>
      intro right
      cases right with
      | nil => rfl
      | cons rightHead rightRest =>
          cases compared : compare leftHead rightHead with
          | lt =>
              have reverse :
                  compare rightHead leftHead = .gt := by
                rw [← Nat.compare_swap]
                simp only [compared, Ordering.swap]
              simp [compareGraphBytes, compared, reverse, Ordering.swap]
          | eq =>
              have reverse :
                  compare rightHead leftHead = .eq := by
                rw [← Nat.compare_swap]
                simp only [compared, Ordering.swap]
              simpa [compareGraphBytes, compared, reverse] using ih rightRest
          | gt =>
              have reverse :
                  compare rightHead leftHead = .lt := by
                rw [← Nat.compare_swap]
                simp only [compared, Ordering.swap]
              simp [compareGraphBytes, compared, reverse, Ordering.swap]

theorem compare_graph_bytes_self :
    ∀ value, compareGraphBytes value value = .eq := by
  intro value
  induction value with
  | nil => rfl
  | cons head tail ih =>
      rw [compareGraphBytes, Nat.compare_eq_eq.mpr rfl]
      exact ih

theorem compare_graph_bytes_eq_iff :
    ∀ {left right},
      compareGraphBytes left right = .eq ↔ left = right := by
  intro left
  induction left with
  | nil =>
      intro right
      cases right with
      | nil =>
          exact ⟨fun _ => rfl, fun _ => rfl⟩
      | cons rightHead rightRest =>
          constructor
          · intro encodedExact
            change Ordering.lt = Ordering.eq at encodedExact
            cases encodedExact
          · intro listExact
            cases listExact
  | cons leftHead leftRest ih =>
      intro right
      cases right with
      | nil =>
          constructor
          · intro encodedExact
            change Ordering.gt = Ordering.eq at encodedExact
            cases encodedExact
          · intro listExact
            cases listExact
      | cons rightHead rightRest =>
          constructor
          · intro encodedExact
            cases compared : compare leftHead rightHead with
            | lt =>
                rw [compareGraphBytes, compared] at encodedExact
                cases encodedExact
            | gt =>
                rw [compareGraphBytes, compared] at encodedExact
                cases encodedExact
            | eq =>
                have headsExact : leftHead = rightHead :=
                  Nat.compare_eq_eq.mp compared
                cases headsExact
                have headCompared :
                    compare leftHead leftHead = Ordering.eq :=
                  Nat.compare_eq_eq.mpr rfl
                rw [compareGraphBytes, headCompared] at encodedExact
                have tailsExact : leftRest = rightRest :=
                  ih.mp encodedExact
                exact congrArg (List.cons leftHead) tailsExact
          · intro listExact
            cases listExact
            exact compare_graph_bytes_self (leftHead :: leftRest)

theorem compare_graph_bytes_le_transitive
    {first second third : GraphBytes}
    (firstSecond : compareGraphBytes first second ≠ .gt)
    (secondThird : compareGraphBytes second third ≠ .gt) :
    compareGraphBytes first third ≠ .gt := by
  rcases compare_graph_bytes_trichotomy first second with
    firstLt | firstEq | firstGt
  · rcases compare_graph_bytes_trichotomy second third with
      secondLt | secondEq | secondGt
    · have firstThird :=
        compare_graph_bytes_lt_transitive
          first second third firstLt secondLt
      simp [firstThird]
    · have equal : second = third :=
        compare_graph_bytes_eq_iff.mp secondEq
      subst third
      simp [firstLt]
    · exact False.elim (secondThird secondGt)
  · have equal : first = second :=
      compare_graph_bytes_eq_iff.mp firstEq
    subst second
    exact secondThird
  · exact False.elim (firstSecond firstGt)

def minGraphBytes (left right : GraphBytes) : GraphBytes :=
  if compareGraphBytes left right = .gt then right else left

theorem min_graph_bytes_choice (left right : GraphBytes) :
    minGraphBytes left right = left ∨
    minGraphBytes left right = right := by
  unfold minGraphBytes
  split <;> simp_all

theorem min_graph_bytes_le_left (left right : GraphBytes) :
    compareGraphBytes (minGraphBytes left right) left ≠ .gt := by
  cases compared : compareGraphBytes left right with
  | lt =>
      simp [minGraphBytes, compared, compare_graph_bytes_self]
  | eq =>
      simp [minGraphBytes, compared, compare_graph_bytes_self]
  | gt =>
      have swapped := compare_graph_bytes_swap left right
      simp [compared, Ordering.swap] at swapped
      have reverse :
          compareGraphBytes right left = .lt :=
        swapped.symm
      simp [minGraphBytes, compared, reverse]

theorem min_graph_bytes_le_right (left right : GraphBytes) :
    compareGraphBytes (minGraphBytes left right) right ≠ .gt := by
  cases compared : compareGraphBytes left right with
  | lt =>
      simp [minGraphBytes, compared]
  | eq =>
      simp [minGraphBytes, compared]
  | gt =>
      simp [minGraphBytes, compared, compare_graph_bytes_self]

def minimumGraphBytesFrom :
    GraphBytes → List GraphBytes → GraphBytes
  | current, [] => current
  | current, candidate :: rest =>
      minimumGraphBytesFrom
        (minGraphBytes current candidate) rest

def lexicographicMinimum
    (candidates : List GraphBytes)
    (_nonempty : candidates ≠ []) : GraphBytes :=
  match candidates with
  | [] => []
  | head :: tail => minimumGraphBytesFrom head tail

theorem minimum_graph_bytes_from_mem :
    ∀ current candidates,
      minimumGraphBytesFrom current candidates = current ∨
      minimumGraphBytesFrom current candidates ∈ candidates := by
  intro current candidates
  induction candidates generalizing current with
  | nil =>
      exact Or.inl rfl
  | cons candidate rest ih =>
      rcases ih (minGraphBytes current candidate) with
        equal | member
      · rcases min_graph_bytes_choice current candidate with
          currentMinimum | candidateMinimum
        · exact Or.inl (equal.trans currentMinimum)
        · exact Or.inr (List.mem_cons.mpr (Or.inl (by
            simpa [minimumGraphBytesFrom] using
              equal.trans candidateMinimum)))
      · exact Or.inr (List.mem_cons_of_mem candidate member)

theorem minimum_graph_bytes_from_lower_bound :
    ∀ current candidates,
      compareGraphBytes
          (minimumGraphBytesFrom current candidates) current ≠ .gt ∧
      ∀ candidate ∈ candidates,
        compareGraphBytes
          (minimumGraphBytesFrom current candidates) candidate ≠ .gt := by
  intro current candidates
  induction candidates generalizing current with
  | nil =>
      constructor
      · simp [minimumGraphBytesFrom, compare_graph_bytes_self]
      · intro candidate member
        simp at member
  | cons candidate rest ih =>
      let next := minGraphBytes current candidate
      have lower := ih next
      constructor
      · exact compare_graph_bytes_le_transitive lower.1
          (min_graph_bytes_le_left current candidate)
      · intro value member
        rcases List.mem_cons.mp member with equal | tailMember
        · subst value
          exact compare_graph_bytes_le_transitive lower.1
            (min_graph_bytes_le_right current candidate)
        · exact lower.2 value tailMember

theorem lexicographic_minimum_mem
    (candidates : List GraphBytes) (nonempty : candidates ≠ []) :
    lexicographicMinimum candidates nonempty ∈ candidates := by
  cases candidates with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      rcases minimum_graph_bytes_from_mem head tail with
        equal | member
      · exact List.mem_cons.mpr (Or.inl equal)
      · exact List.mem_cons_of_mem head member

theorem lexicographic_minimum_lower_bound
    (candidates : List GraphBytes) (nonempty : candidates ≠ []) :
    ∀ candidate ∈ candidates,
      compareGraphBytes
        (lexicographicMinimum candidates nonempty) candidate ≠ .gt := by
  cases candidates with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons head tail =>
      intro candidate member
      rcases List.mem_cons.mp member with equal | tailMember
      · subst candidate
        exact (minimum_graph_bytes_from_lower_bound head tail).1
      · exact
          (minimum_graph_bytes_from_lower_bound head tail).2
            candidate tailMember

def graphBytesLowerBound
    (candidates : List GraphBytes)
    (candidate : GraphBytes) : Bool :=
  candidates.all fun other =>
    compareGraphBytes candidate other != .gt

def minimizerCount
    (encodeCandidate : Candidate → GraphBytes)
    (candidates : List Candidate) : Nat :=
  let encoded := candidates.map encodeCandidate
  encoded.countP (graphBytesLowerBound encoded)

theorem minimizer_count_permutation_witness_cast
    {left right : Nat}
    (exact : left = right)
    (encode : PermutationWitness left → GraphBytes) :
    minimizerCount encode (permutationWitnesses left) =
      minimizerCount
        (fun permutation : PermutationWitness right =>
          encode (exact.symm ▸ permutation))
        (permutationWitnesses right) := by
  subst right
  rfl

structure CandidateEncodingBijection
    (leftCandidates : List Left)
    (rightCandidates : List Right)
    (leftEncode : Left → GraphBytes)
    (rightEncode : Right → GraphBytes) where
  leftNoDuplicates : NoDuplicates leftCandidates
  rightNoDuplicates : NoDuplicates rightCandidates
  forward : Left → Right
  inverse : Right → Left
  forwardMember :
    ∀ candidate, candidate ∈ leftCandidates →
      forward candidate ∈ rightCandidates
  inverseMember :
    ∀ candidate, candidate ∈ rightCandidates →
      inverse candidate ∈ leftCandidates
  leftInverse :
    ∀ candidate, candidate ∈ leftCandidates →
      inverse (forward candidate) = candidate
  rightInverse :
    ∀ candidate, candidate ∈ rightCandidates →
      forward (inverse candidate) = candidate
  encodingPreserved :
    ∀ candidate, candidate ∈ leftCandidates →
      rightEncode (forward candidate) = leftEncode candidate

theorem no_duplicates_mem_iff_permutation :
    ∀ {left right : List α},
      NoDuplicates left →
      NoDuplicates right →
      (∀ value, value ∈ left ↔ value ∈ right) →
      IsPermutation left right := by
  intro left
  induction left with
  | nil =>
      intro right _ _ membership
      cases right with
      | nil => exact .nil
      | cons head tail =>
          have impossible : head ∈ ([] : List α) :=
            (membership head).mpr (by simp)
          simp at impossible
  | cons head tail ih =>
      intro right leftNoDuplicates rightNoDuplicates membership
      have headRight : head ∈ right :=
        (membership head).mp (by simp)
      obtain ⟨pre, suffix, rightExact⟩ :=
        List.append_of_mem headRight
      subst right
      have movedNoDuplicates :
          NoDuplicates (head :: (pre ++ suffix)) :=
        List.Perm.pairwise List.perm_middle rightNoDuplicates
          (fun different => different.symm)
      have headNotTail :
          ∀ value ∈ tail, head ≠ value :=
        (List.pairwise_cons.mp leftNoDuplicates).1
      have headNotRightTail :
          ∀ value ∈ pre ++ suffix, head ≠ value :=
        (List.pairwise_cons.mp movedNoDuplicates).1
      have tailNoDuplicates : NoDuplicates tail :=
        (List.pairwise_cons.mp leftNoDuplicates).2
      have rightTailNoDuplicates :
          NoDuplicates (pre ++ suffix) :=
        (List.pairwise_cons.mp movedNoDuplicates).2
      have tailMembership :
          ∀ value,
            value ∈ tail ↔ value ∈ pre ++ suffix := by
        intro value
        constructor
        · intro valueTail
          have valueRight :
              value ∈ pre ++ head :: suffix :=
            (membership value).mp
              (List.mem_cons_of_mem head valueTail)
          have valueMoved :
              value ∈ head :: (pre ++ suffix) :=
            List.perm_middle.mem_iff.mp valueRight
          exact
            (List.mem_cons.mp valueMoved).resolve_left
              (headNotTail value valueTail).symm
        · intro valueRightTail
          have valueMoved :
              value ∈ head :: (pre ++ suffix) :=
            List.mem_cons_of_mem head valueRightTail
          have valueRight :
              value ∈ pre ++ head :: suffix :=
            List.perm_middle.mem_iff.mpr valueMoved
          have valueLeft :
              value ∈ head :: tail :=
            (membership value).mpr valueRight
          exact
            (List.mem_cons.mp valueLeft).resolve_left
              (headNotRightTail value valueRightTail).symm
      exact
        (ih tailNoDuplicates rightTailNoDuplicates tailMembership).cons head
          |>.trans List.perm_middle.symm

theorem mapped_forward_no_duplicates
    {leftCandidates : List Left}
    {rightCandidates : List Right}
    {leftEncode : Left → GraphBytes}
    {rightEncode : Right → GraphBytes}
    (bijection :
      CandidateEncodingBijection leftCandidates rightCandidates
        leftEncode rightEncode) :
    NoDuplicates (leftCandidates.map bijection.forward) := by
  change
    List.Pairwise (fun left right => left ≠ right)
      (leftCandidates.map bijection.forward)
  rw [List.pairwise_map]
  exact bijection.leftNoDuplicates.imp_of_mem (by
    intro left right leftMember rightMember different equal
    apply different
    calc
      left = bijection.inverse (bijection.forward left) :=
        (bijection.leftInverse left leftMember).symm
      _ = bijection.inverse (bijection.forward right) :=
        congrArg bijection.inverse equal
      _ = right :=
        bijection.leftInverse right rightMember)

theorem mapped_forward_membership
    {leftCandidates : List Left}
    {rightCandidates : List Right}
    {leftEncode : Left → GraphBytes}
    {rightEncode : Right → GraphBytes}
    (bijection :
      CandidateEncodingBijection leftCandidates rightCandidates
        leftEncode rightEncode) :
    ∀ candidate,
      candidate ∈ leftCandidates.map bijection.forward ↔
      candidate ∈ rightCandidates := by
  intro candidate
  constructor
  · intro member
    rcases List.mem_map.mp member with
      ⟨source, sourceMember, sourceExact⟩
    subst candidate
    exact bijection.forwardMember source sourceMember
  · intro member
    have inverseMember :=
      bijection.inverseMember candidate member
    apply List.mem_map.mpr
    exact
      ⟨bijection.inverse candidate, inverseMember,
        bijection.rightInverse candidate member⟩

theorem candidate_encoding_lists_permutation
    {leftCandidates : List Left}
    {rightCandidates : List Right}
    {leftEncode : Left → GraphBytes}
    {rightEncode : Right → GraphBytes}
    (bijection :
      CandidateEncodingBijection leftCandidates rightCandidates
        leftEncode rightEncode) :
    IsPermutation
      (leftCandidates.map leftEncode)
      (rightCandidates.map rightEncode) := by
  have candidatePermutation :
      IsPermutation
        (leftCandidates.map bijection.forward)
        rightCandidates :=
    no_duplicates_mem_iff_permutation
      (mapped_forward_no_duplicates bijection)
      bijection.rightNoDuplicates
      (mapped_forward_membership bijection)
  have leftEncodingExact :
      leftCandidates.map leftEncode =
        (leftCandidates.map bijection.forward).map rightEncode := by
    rw [List.map_map]
    apply List.map_congr_left
    intro candidate member
    exact (bijection.encodingPreserved candidate member).symm
  exact
    (List.Perm.of_eq leftEncodingExact).trans
      (candidatePermutation.map rightEncode)

theorem graph_bytes_lower_bound_permutation
    {left right : List GraphBytes}
    (permuted : IsPermutation left right) :
    ∀ candidate,
      graphBytesLowerBound left candidate =
      graphBytesLowerBound right candidate := by
  intro candidate
  rw [Bool.eq_iff_iff]
  simp only [graphBytesLowerBound, List.all_eq_true]
  constructor
  · intro lower value member
    exact lower value (permuted.symm.subset member)
  · intro lower value member
    exact lower value (permuted.subset member)

theorem minimizer_count_preserved_by_candidate_bijection
    {Left Right : Type}
    {leftCandidates : List Left}
    {rightCandidates : List Right}
    {leftEncode : Left → GraphBytes}
    {rightEncode : Right → GraphBytes}
    (bijection :
      CandidateEncodingBijection leftCandidates rightCandidates
        leftEncode rightEncode) :
    minimizerCount leftEncode leftCandidates =
      minimizerCount rightEncode rightCandidates := by
  let leftEncoded := leftCandidates.map leftEncode
  let rightEncoded := rightCandidates.map rightEncode
  have encodedPermutation :
      IsPermutation leftEncoded rightEncoded :=
    candidate_encoding_lists_permutation bijection
  unfold minimizerCount
  exact encodedPermutation.countP_congr (by
    intro candidate member
    exact graph_bytes_lower_bound_permutation
      encodedPermutation candidate)

end Residua.RCC.Addressing.AddressedGraph


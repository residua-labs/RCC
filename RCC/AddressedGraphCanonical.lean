import RCC.AddressedGraphPermutation

/-!
# RCC addressed-graph canonicalization

This module begins AK-6B with the proof-carrying, multiplicity-preserving
normalization of unordered edge collections.  Later sections construct the
lower-rank materialization and canonical registry on this kernel.
-/

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph.Foundation
open Residua.RCC.Addressing.AddressedGraph.Closure

namespace Residua.RCC.Addressing.AddressedGraph

set_option linter.deprecated false

def collectionWithTargets
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    EdgeCollection schema TargetExternal :=
  match collection with
  | .ordered label direction kind _ =>
      .ordered label direction kind targets
  | .unordered label direction kind _ =>
      .unordered label direction kind targets

def targetSortBytes
    (collection : EdgeCollection schema (ExternalRef schema))
    (target : GraphRef (ExternalRef schema)) : GraphBytes :=
  encodeCanonicalBlock
    (.dagSingleton (sourceKind := collection.expectedTargetKind)
      { payload := 0
        edgeCollections := [collectionWithTargets collection [target]] })

def bytesLessOrEqual
    (encode : α → GraphBytes) (left right : α) : Prop :=
  compareGraphBytes (encode left) (encode right) ≠ .gt

def insertByBytes
    (encode : α → GraphBytes) (value : α) : List α → List α
  | [] => [value]
  | head :: tail =>
      if compareGraphBytes (encode value) (encode head) = .gt then
        head :: insertByBytes encode value tail
      else
        value :: head :: tail

def stableSortByBytes (encode : α → GraphBytes) : List α → List α
  | [] => []
  | head :: tail =>
      insertByBytes encode head (stableSortByBytes encode tail)

theorem insert_by_bytes_permutation
    (encode : α → GraphBytes) (value : α) :
    ∀ values,
      IsPermutation (insertByBytes encode value values)
        (value :: values) := by
  intro values
  induction values with
  | nil =>
      exact .rfl
  | cons head tail ih =>
      unfold insertByBytes
      split
      · exact (ih.cons head).trans (.swap value head tail)
      · exact .rfl

theorem insert_by_bytes_length
    (encode : α → GraphBytes) (value : α) :
    ∀ values,
      (insertByBytes encode value values).length =
        values.length + 1 := by
  intro values
  have permuted := insert_by_bytes_permutation encode value values
  simpa [Nat.add_comm] using permuted.length_eq

theorem stable_sort_by_bytes_permutation
    (encode : α → GraphBytes) :
    ∀ values,
      IsPermutation (stableSortByBytes encode values) values := by
  intro values
  induction values with
  | nil =>
      exact .rfl
  | cons head tail ih =>
      exact
        (insert_by_bytes_permutation encode head
          (stableSortByBytes encode tail)).trans
          (ih.cons head)

theorem stable_sort_by_bytes_length
    (encode : α → GraphBytes) :
    ∀ values,
      (stableSortByBytes encode values).length = values.length := by
  intro values
  exact (stable_sort_by_bytes_permutation encode values).length_eq

theorem bytes_less_or_equal_transitive
    (encode : α → GraphBytes)
    {first second third : α}
    (firstSecond : bytesLessOrEqual encode first second)
    (secondThird : bytesLessOrEqual encode second third) :
    bytesLessOrEqual encode first third :=
  compare_graph_bytes_le_transitive firstSecond secondThird

theorem compare_graph_bytes_gt_reverse_le
    {left right : GraphBytes}
    (greater : compareGraphBytes left right = .gt) :
    compareGraphBytes right left ≠ .gt := by
  have swapped := compare_graph_bytes_swap left right
  have reverse : compareGraphBytes right left = .lt := by
    simpa [greater, Ordering.swap] using swapped.symm
  simp [reverse]

theorem insert_by_bytes_sorted
    (encode : α → GraphBytes) (value : α) :
    ∀ values,
      List.Pairwise (bytesLessOrEqual encode) values →
      List.Pairwise (bytesLessOrEqual encode)
        (insertByBytes encode value values) := by
  intro values sorted
  induction values with
  | nil =>
      simp [insertByBytes]
  | cons head tail ih =>
      have headLower :
          ∀ candidate ∈ tail,
            bytesLessOrEqual encode head candidate :=
        (List.pairwise_cons.mp sorted).1
      have tailSorted :
          List.Pairwise (bytesLessOrEqual encode) tail :=
        (List.pairwise_cons.mp sorted).2
      unfold insertByBytes
      split
      · next greater =>
          apply List.pairwise_cons.mpr
          constructor
          · intro candidate candidateMember
            have insertedMember :
                candidate = value ∨ candidate ∈ tail := by
              have member :
                  candidate ∈ value :: tail :=
                (insert_by_bytes_permutation encode value tail).subset
                  candidateMember
              exact List.mem_cons.mp member
            rcases insertedMember with equal | tailMember
            · subst candidate
              exact compare_graph_bytes_gt_reverse_le greater
            · exact headLower candidate tailMember
          · exact ih tailSorted
      · next notGreater =>
          apply List.pairwise_cons.mpr
          constructor
          · intro candidate candidateMember
            rcases List.mem_cons.mp candidateMember with
              equal | tailMember
            · subst candidate
              exact notGreater
            · exact bytes_less_or_equal_transitive encode notGreater
                (headLower candidate tailMember)
          · exact sorted

theorem stable_sort_by_bytes_sorted
    (encode : α → GraphBytes) :
    ∀ values,
      List.Pairwise (bytesLessOrEqual encode)
        (stableSortByBytes encode values) := by
  intro values
  induction values with
  | nil =>
      exact .nil
  | cons head tail ih =>
      exact insert_by_bytes_sorted encode head
        (stableSortByBytes encode tail) ih

theorem bytes_less_or_equal_antisymmetric
    (encode : α → GraphBytes)
    (encodeInjective : ∀ {left right}, encode left = encode right → left = right)
    {left right : α}
    (leftRight : bytesLessOrEqual encode left right)
    (rightLeft : bytesLessOrEqual encode right left) :
    left = right := by
  rcases compare_graph_bytes_trichotomy
      (encode left) (encode right) with
    less | equal | greater
  · have reverse :=
      compare_graph_bytes_reverse_lt (encode left) (encode right) less
    exact False.elim (rightLeft reverse)
  · exact encodeInjective (compare_graph_bytes_eq_iff.mp equal)
  · exact False.elim (leftRight greater)

theorem stable_sort_by_bytes_permutation_invariant
    (encode : α → GraphBytes)
    (encodeInjective : ∀ {left right}, encode left = encode right → left = right)
    {left right : List α}
    (permuted : IsPermutation left right) :
    stableSortByBytes encode left =
      stableSortByBytes encode right := by
  apply List.Perm.eq_of_sorted
    (fun first second _ _ =>
      bytes_less_or_equal_antisymmetric encode encodeInjective)
    (stable_sort_by_bytes_sorted encode left)
    (stable_sort_by_bytes_sorted encode right)
  exact
    (stable_sort_by_bytes_permutation encode left).trans
      (permuted.trans
        (stable_sort_by_bytes_permutation encode right).symm)

theorem stable_sort_by_bytes_idempotent
    (encode : α → GraphBytes)
    (encodeInjective : ∀ {left right}, encode left = encode right → left = right)
    (values : List α) :
    stableSortByBytes encode (stableSortByBytes encode values) =
      stableSortByBytes encode values :=
  stable_sort_by_bytes_permutation_invariant encode encodeInjective
    (stable_sort_by_bytes_permutation encode values)

theorem target_sort_bytes_injective
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    ∀ {left right},
      targetSortBytes collection left =
        targetSortBytes collection right →
      left = right := by
  intro left right encodedEqual
  let leftBlock :
      CanonicalBlock schema collection.expectedTargetKind :=
    .dagSingleton
      { payload := 0
        edgeCollections :=
          [collectionWithTargets collection [left]] }
  let rightBlock :
      CanonicalBlock schema collection.expectedTargetKind :=
    .dagSingleton
      { payload := 0
        edgeCollections :=
          [collectionWithTargets collection [right]] }
  have encodedBlocksEqual :
      encodeCanonicalBlock leftBlock =
        encodeCanonicalBlock rightBlock := by
    simpa [leftBlock, rightBlock, targetSortBytes] using encodedEqual
  have codecEqual :
      (constructiveBlockCodec schema
        collection.expectedTargetKind).encode leftBlock =
      (constructiveBlockCodec schema
        collection.expectedTargetKind).encode rightBlock := by
    change encodeCanonicalBlock leftBlock =
      encodeCanonicalBlock rightBlock
    exact encodedBlocksEqual
  have blockEqual : leftBlock = rightBlock :=
    canonical_encode_injective
      (constructiveBlockCodec schema
        collection.expectedTargetKind) codecEqual
  simp [leftBlock, rightBlock] at blockEqual
  cases collection <;> simp [collectionWithTargets] at blockEqual
  all_goals
    exact blockEqual

def normalizeTargetList
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    List (GraphRef (ExternalRef schema)) :=
  match collection with
  | .ordered _ _ _ targets => targets
  | .unordered _ _ _ targets =>
      stableSortByBytes (targetSortBytes collection) targets

theorem normalize_target_list_permutation_invariant
    {schema : GraphKindSchema}
    (collection : EdgeCollection schema (ExternalRef schema))
    (unordered : collection.mode = .unordered)
    (left right : List (GraphRef (ExternalRef schema)))
    (permutation : List.Perm left right) :
    normalizeTargetList (collectionWithTargets collection left) =
      normalizeTargetList (collectionWithTargets collection right) := by
  cases collection with
  | ordered label direction kind targets =>
      simp [EdgeCollection.mode] at unordered
  | unordered label direction kind targets =>
      exact
        stable_sort_by_bytes_permutation_invariant
          (targetSortBytes
            (.unordered label direction kind targets))
          (target_sort_bytes_injective
            (.unordered label direction kind targets))
          permutation

theorem normalize_target_list_length
    {schema : GraphKindSchema}
    (collection : EdgeCollection schema (ExternalRef schema)) :
    (normalizeTargetList collection).length =
      collection.targets.length := by
  cases collection with
  | ordered =>
      rfl
  | unordered label direction kind targets =>
      exact stable_sort_by_bytes_length
        (targetSortBytes
          (.unordered label direction kind targets)) targets

theorem normalize_target_list_idempotent
    {schema : GraphKindSchema}
    (collection : EdgeCollection schema (ExternalRef schema)) :
    normalizeTargetList
        (collectionWithTargets collection
          (normalizeTargetList collection)) =
      normalizeTargetList collection := by
  cases collection with
  | ordered =>
      rfl
  | unordered label direction kind targets =>
      exact stable_sort_by_bytes_idempotent
        (targetSortBytes
          (.unordered label direction kind targets))
        (target_sort_bytes_injective
          (.unordered label direction kind targets))
        targets

def collectionSortBytes
    (collection : EdgeCollection schema (ExternalRef schema)) : GraphBytes :=
  encodeCanonicalBlock
    (.dagSingleton (sourceKind := collection.expectedTargetKind)
      { payload := 0, edgeCollections := [collection] })

theorem collection_sort_bytes_injective :
    ∀ {left right :
        EdgeCollection schema (ExternalRef schema)},
      collectionSortBytes left = collectionSortBytes right →
      left = right := by
  intro left right encodedEqual
  let leftBlock :
      CanonicalBlock schema left.expectedTargetKind :=
    .dagSingleton
      { payload := 0, edgeCollections := [left] }
  let rightBlock :
      CanonicalBlock schema left.expectedTargetKind :=
    .dagSingleton
      { payload := 0, edgeCollections := [right] }
  have encodedBlocksEqual :
      encodeCanonicalBlock leftBlock =
        encodeCanonicalBlock rightBlock := by
    simpa [leftBlock, rightBlock, collectionSortBytes] using encodedEqual
  have codecEqual :
      (constructiveBlockCodec schema
        left.expectedTargetKind).encode leftBlock =
      (constructiveBlockCodec schema
        left.expectedTargetKind).encode rightBlock := by
    change encodeCanonicalBlock leftBlock =
      encodeCanonicalBlock rightBlock
    exact encodedBlocksEqual
  have blockEqual : leftBlock = rightBlock :=
    canonical_encode_injective
      (constructiveBlockCodec schema left.expectedTargetKind)
      codecEqual
  simp [leftBlock, rightBlock] at blockEqual
  cases left <;> cases right <;>
    simp at blockEqual
  all_goals
    rcases blockEqual with ⟨rfl, rfl, rfl, rfl⟩
    rfl

def normalizeOuterCollections
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) :
    List (EdgeCollection schema (ExternalRef schema)) :=
  stableSortByBytes collectionSortBytes collections

theorem normalize_outer_collections_permutation_invariant
    {schema : GraphKindSchema}
    (left right :
      List (EdgeCollection schema (ExternalRef schema)))
    (permutation : List.Perm left right) :
    normalizeOuterCollections left =
      normalizeOuterCollections right :=
  stable_sort_by_bytes_permutation_invariant
    collectionSortBytes collection_sort_bytes_injective permutation

theorem normalize_outer_collections_length
    {schema : GraphKindSchema}
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) :
    (normalizeOuterCollections collections).length =
    collections.length :=
  stable_sort_by_bytes_length collectionSortBytes collections

theorem normalize_outer_collections_idempotent
    {schema : GraphKindSchema}
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) :
    normalizeOuterCollections
        (normalizeOuterCollections collections) =
      normalizeOuterCollections collections :=
  stable_sort_by_bytes_idempotent
    collectionSortBytes collection_sort_bytes_injective collections

/-! ## Source-local relabeling -/

def finiteIndices : (n : Nat) → List (Fin n)
  | 0 => []
  | n + 1 =>
      ⟨0, Nat.zero_lt_succ n⟩ ::
        (finiteIndices n).map fun index =>
          ⟨index.val + 1, Nat.succ_lt_succ index.isLt⟩

theorem finite_indices_length :
    ∀ n, (finiteIndices n).length = n := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [finiteIndices, ih]

theorem finite_indices_complete :
    ∀ {n} (index : Fin n), index ∈ finiteIndices n := by
  intro n index
  induction n with
  | zero =>
      exact Fin.elim0 index
  | succ n ih =>
      cases index with
      | mk value bound =>
          cases value with
          | zero =>
              simp [finiteIndices]
          | succ prior =>
              have priorBound : prior < n := by
                simpa using bound
              have priorMember := ih ⟨prior, priorBound⟩
              rw [finiteIndices]
              apply List.mem_cons.mpr
              apply Or.inr
              apply List.mem_map.mpr
              refine ⟨⟨prior, priorBound⟩, priorMember, ?_⟩
              apply Fin.ext
              rfl

theorem finite_indices_get
    (n : Nat) (index : Fin n) :
    (finiteIndices n)[index.val]'(by
        simp [finite_indices_length, index.isLt]) =
      index := by
  induction n with
  | zero =>
      exact Fin.elim0 index
  | succ n ih =>
      cases index with
      | mk value bound =>
          cases value with
          | zero =>
              rfl
          | succ prior =>
              have priorBound : prior < n := by
                simpa using bound
              have priorIdentity := ih ⟨prior, priorBound⟩
              simp only [finiteIndices, List.getElem_cons_succ,
                List.getElem_map] at *
              apply Fin.ext
              simpa using congrArg Fin.val priorIdentity

theorem finite_indices_cast
    {left right : Nat}
    (exact : left = right) :
    finiteIndices left =
      (finiteIndices right).map (Fin.cast exact.symm) := by
  subst right
  simp

theorem list_map_map_apply
    (items : List α)
    (first : α → β)
    (second : β → γ) :
    (items.map first).map second =
      items.map (fun item => second (first item)) := by
  induction items with
  | nil =>
      rfl
  | cons head tail ih =>
      simp [ih]

def relabelGraphRef
    (bijection : LocalBijection n) :
    GraphRef External → GraphRef External
  | .external ref => .external ref
  | .local index =>
      if bounded : index < n then
        .local (bijection.forward ⟨index, bounded⟩).val
      else
        .local index

theorem local_bijection_forward_injective
    (bijection : LocalBijection n) :
    ∀ left right,
      bijection.forward left = bijection.forward right →
        left = right := by
  intro left right equal
  have inverseEqual := congrArg bijection.inverse equal
  simpa only [bijection.leftInverse] using inverseEqual

theorem local_bijection_ext
    (left right : LocalBijection n)
    (forwardExact :
      ∀ index, left.forward index = right.forward index) :
    left = right := by
  have forwardFunctionExact : left.forward = right.forward :=
    funext forwardExact
  have inverseExact :
      ∀ index, left.inverse index = right.inverse index := by
    intro index
    apply local_bijection_forward_injective left
    calc
      left.forward (left.inverse index) = index :=
        left.rightInverse index
      _ = right.forward (right.inverse index) :=
        (right.rightInverse index).symm
      _ = left.forward (right.inverse index) := by
        rw [forwardFunctionExact]
  cases left
  cases right
  simp only [LocalBijection.mk.injEq] at forwardFunctionExact ⊢
  exact ⟨forwardFunctionExact, funext inverseExact⟩

theorem relabel_graph_ref_local
    (bijection : LocalBijection n)
    (index : Nat) (bounded : index < n) :
    relabelGraphRef bijection
        (.local index : GraphRef External) =
      .local (bijection.forward ⟨index, bounded⟩).val := by
  simp [relabelGraphRef, bounded]

theorem relabel_graph_ref_external
    (bijection : LocalBijection n)
    (reference : External) :
    relabelGraphRef bijection (.external reference) =
      .external reference := by
  rfl

theorem relabel_graph_ref_eq_external_iff
    (bijection : LocalBijection n)
    (reference : GraphRef External)
    (external : External) :
    relabelGraphRef bijection reference = .external external ↔
      reference = .external external := by
  cases reference with
  | external =>
      simp [relabelGraphRef]
  | «local» index =>
      simp only [relabelGraphRef]
      split <;> simp

def identityLocalBijection (n : Nat) : LocalBijection n where
  forward := fun index => index
  inverse := fun index => index
  leftInverse := by
    intro index
    rfl
  rightInverse := by
    intro index
    rfl

def composeLocalBijection
    (first second : LocalBijection n) :
    LocalBijection n where
  forward := fun index => second.forward (first.forward index)
  inverse := fun index => first.inverse (second.inverse index)
  leftInverse := by
    intro index
    simp only [second.leftInverse, first.leftInverse]
  rightInverse := by
    intro index
    simp only [first.rightInverse, second.rightInverse]

def inverseLocalBijection
    (bijection : LocalBijection n) :
    LocalBijection n where
  forward := bijection.inverse
  inverse := bijection.forward
  leftInverse := bijection.rightInverse
  rightInverse := bijection.leftInverse

def transportLocalBijection
    {left right : Nat}
    (exact : left = right)
    (bijection : LocalBijection left) :
    LocalBijection right :=
  exact ▸ bijection

def transportPermutationValue
    (bijection : LocalBijection n)
    (value : Nat) : Nat :=
  if bounded : value < n then
    (bijection.forward ⟨value, bounded⟩).val
  else
    value

def transportPermutationSameCount
    (bijection : LocalBijection n)
    (permutation : PermutationWitness n) :
    PermutationWitness n where
  values :=
    permutation.values.map
      (transportPermutationValue bijection)
  permutesRange := by
    have sourceNoDuplicates :
        NoDuplicates permutation.values :=
      List.Perm.pairwise permutation.permutesRange.symm
        (range_no_duplicates n)
        (fun different => different.symm)
    have mappedNoDuplicates :
        NoDuplicates
          (permutation.values.map
            (transportPermutationValue bijection)) := by
      change
        List.Pairwise (fun left right => left ≠ right)
          (permutation.values.map
            (transportPermutationValue bijection))
      rw [List.pairwise_map]
      exact sourceNoDuplicates.imp_of_mem (by
        intro left right leftMember rightMember different equal
        have leftBound : left < n := by
          have member :
              left ∈ range n :=
            permutation.permutesRange.subset leftMember
          simpa [range] using member
        have rightBound : right < n := by
          have member :
              right ∈ range n :=
            permutation.permutesRange.subset rightMember
          simpa [range] using member
        have forwardExact :
            bijection.forward ⟨left, leftBound⟩ =
              bijection.forward ⟨right, rightBound⟩ := by
          apply Fin.ext
          simpa [transportPermutationValue, leftBound,
            rightBound] using equal
        apply different
        exact congrArg Fin.val
          (local_bijection_forward_injective
            bijection _ _ forwardExact))
    apply no_duplicates_mem_iff_permutation
      mappedNoDuplicates
      (range_no_duplicates n)
    intro value
    constructor
    · intro member
      rcases List.mem_map.mp member with
        ⟨source, sourceMember, sourceExact⟩
      have sourceBound : source < n := by
        have rangeMember :
            source ∈ range n :=
          permutation.permutesRange.subset sourceMember
        simpa [range] using rangeMember
      subst value
      simp [transportPermutationValue, sourceBound, range,
        (bijection.forward ⟨source, sourceBound⟩).isLt]
    · intro member
      have valueBound : value < n := by
        simpa [range] using member
      let sourceIndex : Fin n :=
        bijection.inverse ⟨value, valueBound⟩
      have sourceMember :
          sourceIndex.val ∈ permutation.values :=
        permutation.permutesRange.symm.subset
          (by simp [range, sourceIndex.isLt])
      apply List.mem_map.mpr
      refine ⟨sourceIndex.val, sourceMember, ?_⟩
      simp [transportPermutationValue, sourceIndex.isLt,
        sourceIndex, bijection.rightInverse]

theorem transport_permutation_same_count_inverse
    (bijection : LocalBijection n)
    (permutation : PermutationWitness n) :
    transportPermutationSameCount
        (inverseLocalBijection bijection)
        (transportPermutationSameCount bijection permutation) =
      permutation := by
  apply permutation_witness_ext
  change
    (permutation.values.map
      (transportPermutationValue bijection)).map
        (transportPermutationValue
          (inverseLocalBijection bijection)) =
      permutation.values
  rw [list_map_map_apply]
  calc
    permutation.values.map
        (fun item =>
          transportPermutationValue (inverseLocalBijection bijection)
            (transportPermutationValue bijection item)) =
        permutation.values.map id := by
      apply List.map_congr_left
      intro value member
      have valueBound : value < n := by
        have rangeMember : value ∈ range n :=
          permutation.permutesRange.subset member
        simpa [range] using rangeMember
      simp [transportPermutationValue, valueBound,
        inverseLocalBijection, bijection.leftInverse]
    _ = permutation.values :=
      List.map_id permutation.values

theorem transport_permutation_same_count_forward
    (bijection : LocalBijection n)
    (permutation : PermutationWitness n) :
    transportPermutationSameCount bijection
        (transportPermutationSameCount
          (inverseLocalBijection bijection) permutation) =
      permutation := by
  have inverseInverse :
      inverseLocalBijection (inverseLocalBijection bijection) =
        bijection := by
    apply local_bijection_ext
    intro index
    rfl
  have roundtrip :=
    transport_permutation_same_count_inverse
      (inverseLocalBijection bijection) permutation
  rw [inverseInverse] at roundtrip
  exact roundtrip

theorem transport_permutation_inverse_same_count
    (bijection : LocalBijection n)
    (permutation : PermutationWitness n)
    (index : Fin n) :
    (permutationBijection
        (transportPermutationSameCount bijection permutation)).inverse
        index =
      bijection.forward
        ((permutationBijection permutation).inverse index) := by
  let position : Fin permutation.values.length :=
    ⟨index.val, by
      rw [permutation_length_eq permutation.permutesRange]
      exact index.isLt⟩
  have indexBound :
      index.val < permutation.values.length := by
    rw [permutation_length_eq permutation.permutesRange]
    exact index.isLt
  have valueBound :
      permutation.values.get position < n := by
    have rangeMember :
        permutation.values.get position ∈ range n :=
      permutation.permutesRange.subset
        (get_mem_compat permutation.values position)
    simpa [range] using rangeMember
  have valueBoundAt :
      permutation.values[index.val]'indexBound < n := by
    simpa [position] using valueBound
  apply Fin.ext
  simp [permutationBijection, inversePermutation,
    transportPermutationSameCount, transportPermutationValue,
    valueBoundAt]

theorem transport_permutation_forward_same_count
    (bijection : LocalBijection n)
    (permutation : PermutationWitness n)
    (index : Fin n) :
    (permutationBijection
        (transportPermutationSameCount bijection permutation)).forward
        (bijection.forward index) =
      (permutationBijection permutation).forward index := by
  let transported :=
    permutationBijection
      (transportPermutationSameCount bijection permutation)
  let original := permutationBijection permutation
  have inverseAtOriginal :
      transported.inverse (original.forward index) =
        bijection.forward index := by
    calc
      transported.inverse (original.forward index) =
          bijection.forward
            (original.inverse (original.forward index)) := by
        exact transport_permutation_inverse_same_count
          bijection permutation (original.forward index)
      _ = bijection.forward index :=
        congrArg bijection.forward (original.leftInverse index)
  calc
    transported.forward (bijection.forward index) =
        transported.forward
          (transported.inverse (original.forward index)) :=
      congrArg transported.forward inverseAtOriginal.symm
    _ = original.forward index :=
      transported.rightInverse (original.forward index)

def composeRelabeledLocalBijection
    (first : LocalBijection n)
    (second : LocalBijection m)
    (lengthExact : m = n) :
    LocalBijection n where
  forward := fun index =>
    Fin.cast lengthExact
      (second.forward
        (Fin.cast lengthExact.symm (first.forward index)))
  inverse := fun index =>
    first.inverse
      (Fin.cast lengthExact
        (second.inverse (Fin.cast lengthExact.symm index)))
  leftInverse := by
    intro index
    have secondLeft :=
      second.leftInverse
        (Fin.cast lengthExact.symm (first.forward index))
    have castSecondLeft :
        Fin.cast lengthExact
            (second.inverse
              (second.forward
                (Fin.cast lengthExact.symm
                  (first.forward index)))) =
          first.forward index := by
      apply Fin.ext
      simpa using congrArg Fin.val secondLeft
    change
      first.inverse
          (Fin.cast lengthExact
            (second.inverse
              (second.forward
                (Fin.cast lengthExact.symm
                  (first.forward index))))) =
        index
    rw [castSecondLeft]
    exact first.leftInverse index
  rightInverse := by
    intro index
    have firstRight :=
      first.rightInverse
        (Fin.cast lengthExact
          (second.inverse (Fin.cast lengthExact.symm index)))
    have secondRight :=
      second.rightInverse (Fin.cast lengthExact.symm index)
    change
      Fin.cast lengthExact
          (second.forward
            (Fin.cast lengthExact.symm
              (first.forward
                (first.inverse
                  (Fin.cast lengthExact
                    (second.inverse
                      (Fin.cast lengthExact.symm index))))))) =
        index
    rw [firstRight]
    apply Fin.ext
    simpa using congrArg Fin.val secondRight

theorem relabel_graph_ref_compose
    (first second : LocalBijection n)
    (reference : GraphRef External) :
    relabelGraphRef second (relabelGraphRef first reference) =
      relabelGraphRef
        (composeLocalBijection first second) reference := by
  cases reference with
  | external =>
      rfl
  | «local» index =>
      by_cases bounded : index < n
      · simp [relabelGraphRef, bounded, composeLocalBijection,
          (first.forward ⟨index, bounded⟩).isLt]
      · simp [relabelGraphRef, bounded]

theorem has_local_target_relabel
    {sourceKind expectedKind : schema.Kind}
    {targets : List (GraphRef (RawInRegistryRef schema))}
    (evidence :
      Closure.LocalTargetsEvidence schema sourceKind
        expectedKind n targets)
    (bijection : LocalBijection n)
    (target : Fin n) :
    Closure.HasLocalTarget
        (targets.map (relabelGraphRef bijection))
        (bijection.forward target).val =
      Closure.HasLocalTarget targets target.val := by
  induction evidence with
  | nil =>
      rfl
  | external rest ih =>
      simpa [Closure.HasLocalTarget, relabelGraphRef] using ih
  | @«local» index rest kindEqual indexBound restEvidence ih =>
      have forwardEqualIff :
          (bijection.forward ⟨index, indexBound⟩).val =
              (bijection.forward target).val ↔
            index = target.val := by
        constructor
        · intro equal
          have finEqual :
              bijection.forward ⟨index, indexBound⟩ =
                bijection.forward target := by
            exact Fin.ext equal
          have sourceEqual :=
            local_bijection_forward_injective
              bijection _ _ finEqual
          exact congrArg Fin.val sourceEqual
        · intro equal
          apply congrArg Fin.val
          apply congrArg bijection.forward
          exact Fin.ext equal
      have tailEqual := ih
      simp only [Closure.HasLocalTarget, List.any_map] at tailEqual
      simp [Closure.HasLocalTarget, relabelGraphRef, indexBound,
        forwardEqualIff, List.any_map, tailEqual]

def localCollectionsEvidenceAt
    {sourceKind : schema.Kind} {nodeCount : Nat} :
    ∀ {nodes : List (RawNode schema)},
      Closure.LocalNodesEvidence schema sourceKind nodeCount nodes →
      (index : Fin nodes.length) →
      Closure.LocalCollectionsEvidence schema sourceKind nodeCount
        (nodes.get index).edgeCollections
  | [], .nil, index => Fin.elim0 index
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨index + 1, bounded⟩ =>
      localCollectionsEvidenceAt tail
        ⟨index, Nat.lt_of_succ_lt_succ bounded⟩

def relabelCollection
    (bijection : LocalBijection n) :
    EdgeCollection schema External →
      EdgeCollection schema External
  | .ordered label direction kind targets =>
      .ordered label direction kind
        (targets.map (relabelGraphRef bijection))
  | .unordered label direction kind targets =>
      .unordered label direction kind
        (targets.map (relabelGraphRef bijection))

theorem relabel_collection_direction
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).direction =
      collection.direction := by
  cases collection <;> rfl

theorem relabel_collection_targets
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).targets =
      collection.targets.map (relabelGraphRef bijection) := by
  cases collection <;> rfl

theorem relabel_collection_expected_target_kind
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).expectedTargetKind =
      collection.expectedTargetKind := by
  cases collection <;> rfl

theorem relabel_collection_compose
    (first second : LocalBijection n)
    (collection : EdgeCollection schema External) :
    relabelCollection second (relabelCollection first collection) =
      relabelCollection
        (composeLocalBijection first second) collection := by
  cases collection <;>
    simp [relabelCollection, List.map_map,
      relabel_graph_ref_compose]

def relabelLocalTargetsEvidence
    {sourceKind expectedKind : schema.Kind}
    {targets : List (GraphRef (RawInRegistryRef schema))}
    (evidence :
      Closure.LocalTargetsEvidence schema sourceKind
        expectedKind n targets)
    (bijection : LocalBijection n) :
    Closure.LocalTargetsEvidence schema sourceKind expectedKind n
      (targets.map (relabelGraphRef bijection)) :=
  match evidence with
  | .nil => .nil
  | .external restEvidence =>
      .external
        (relabelLocalTargetsEvidence restEvidence bijection)
  | .local kindExact indexBound restEvidence => by
      simpa [relabelGraphRef, indexBound] using
        Closure.LocalTargetsEvidence.local kindExact
          (bijection.forward ⟨_, indexBound⟩).isLt
          (relabelLocalTargetsEvidence restEvidence bijection)

def relabelLocalCollectionsEvidence
    {sourceKind : schema.Kind}
    {collections :
      List (EdgeCollection schema (RawInRegistryRef schema))}
    (evidence :
      Closure.LocalCollectionsEvidence schema sourceKind n collections)
    (bijection : LocalBijection n) :
    Closure.LocalCollectionsEvidence schema sourceKind n
      (collections.map (relabelCollection bijection)) :=
  match evidence with
  | .nil => .nil
  | .cons targetEvidence restEvidence => by
      apply Closure.LocalCollectionsEvidence.cons
      · simpa [relabel_collection_expected_target_kind,
          relabel_collection_targets] using
          relabelLocalTargetsEvidence targetEvidence bijection
      · exact
          relabelLocalCollectionsEvidence restEvidence bijection

theorem local_collections_relabel
    {sourceKind : schema.Kind}
    {collections :
      List (EdgeCollection schema (RawInRegistryRef schema))}
    (evidence :
      Closure.LocalCollectionsEvidence schema sourceKind n collections)
    (bijection : LocalBijection n)
    (direction : EdgeDirection)
    (target : Fin n) :
    (collections.map (relabelCollection bijection)).any
        (fun collection =>
          decide (collection.direction = direction) &&
            Closure.HasLocalTarget collection.targets
              (bijection.forward target).val) =
      collections.any
        (fun collection =>
          decide (collection.direction = direction) &&
            Closure.HasLocalTarget collection.targets target.val) := by
  induction evidence with
  | nil =>
      rfl
  | cons targetEvidence restEvidence ih =>
      simp only [List.map_cons, List.any_cons,
        relabel_collection_direction, relabel_collection_targets]
      rw [has_local_target_relabel targetEvidence bijection target]
      rw [ih]

def relabelNode
    (bijection : LocalBijection n) :
    GraphNode schema External → GraphNode schema External
  | node =>
      { payload := node.payload
        edgeCollections :=
          node.edgeCollections.map (relabelCollection bijection) }

theorem relabel_node_compose
    (first second : LocalBijection n)
    (node : GraphNode schema External) :
    relabelNode second (relabelNode first node) =
      relabelNode (composeLocalBijection first second) node := by
  cases node
  simp [relabelNode, List.map_map, relabel_collection_compose]

theorem relabel_node_compose_relabeled
    (first : LocalBijection n)
    (second : LocalBijection m)
    (lengthExact : m = n)
    (node : GraphNode schema External) :
    relabelNode second (relabelNode first node) =
      relabelNode
        (composeRelabeledLocalBijection
          first second lengthExact) node := by
  subst m
  exact relabel_node_compose first second node

def relabelNodes
    (nodes : List (GraphNode schema External))
    (bijection : LocalBijection nodes.length) :
    List (GraphNode schema External) :=
  (finiteIndices nodes.length).map fun newIndex =>
    relabelNode bijection
      (nodes.get (bijection.inverse newIndex))

theorem relabel_nodes_length
    (nodes : List (GraphNode schema External))
    (bijection : LocalBijection nodes.length) :
    (relabelNodes nodes bijection).length = nodes.length := by
  simp [relabelNodes, finite_indices_length]

theorem relabel_nodes_get
    (nodes : List (GraphNode schema External))
    (bijection : LocalBijection nodes.length)
    (index : Fin nodes.length) :
    (relabelNodes nodes bijection)[(bijection.forward index).val]'(by
        simp [relabel_nodes_length,
          (bijection.forward index).isLt]) =
      relabelNode bijection (nodes.get index) := by
  simp only [relabelNodes, List.getElem_map]
  rw [finite_indices_get]
  rw [bijection.leftInverse]

theorem relabel_nodes_get?_forward
    (nodes : List (GraphNode schema External))
    (bijection : LocalBijection nodes.length)
    (index : Fin nodes.length) :
    (relabelNodes nodes bijection)[(bijection.forward index).val]? =
      some (relabelNode bijection (nodes.get index)) := by
  rw [List.getElem?_eq_getElem (by
    simp [relabel_nodes_length, (bijection.forward index).isLt])]
  exact congrArg some (relabel_nodes_get nodes bijection index)

def relabelLocalNodesEvidenceForIndices
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length) :
    ∀ indices : List (Fin nodes.length),
      Closure.LocalNodesEvidence schema sourceKind nodes.length
        (indices.map fun newIndex =>
          relabelNode bijection
            (nodes.get (bijection.inverse newIndex)))
  | [] => .nil
  | newIndex :: rest =>
      .cons
        (relabelLocalCollectionsEvidence
          (localCollectionsEvidenceAt evidence
            (bijection.inverse newIndex))
          bijection)
        (relabelLocalNodesEvidenceForIndices
          evidence bijection rest)

def relabelLocalNodesEvidence
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length) :
    Closure.LocalNodesEvidence schema sourceKind
      (relabelNodes nodes bijection).length
      (relabelNodes nodes bijection) := by
  rw [relabel_nodes_length]
  exact
    relabelLocalNodesEvidenceForIndices evidence bijection
      (finiteIndices nodes.length)

theorem relabel_nodes_compose
    (nodes : List (GraphNode schema External))
    (first : LocalBijection nodes.length)
    (second : LocalBijection (relabelNodes nodes first).length) :
    relabelNodes (relabelNodes nodes first) second =
      relabelNodes nodes
        (composeRelabeledLocalBijection first second
          (relabel_nodes_length nodes first)) := by
  apply List.ext_get
  · simp [relabel_nodes_length]
  · intro index leftBound rightBound
    let combined :=
      composeRelabeledLocalBijection first second
        (relabel_nodes_length nodes first)
    let finalIndex : Fin nodes.length :=
      ⟨index, by
        simpa [relabel_nodes_length] using rightBound⟩
    let relabeledFinalIndex :
        Fin (relabelNodes nodes first).length :=
      ⟨index, by
        simpa [relabel_nodes_length] using leftBound⟩
    let firstIndex :
        Fin (relabelNodes nodes first).length :=
      second.inverse relabeledFinalIndex
    let sourceIndex : Fin nodes.length :=
      first.inverse
        (Fin.cast (relabel_nodes_length nodes first) firstIndex)
    have sourceLookup :=
      relabel_nodes_get nodes first sourceIndex
    have outerLookup :=
      relabel_nodes_get
        (relabelNodes nodes first) second firstIndex
    have finalPosition :
        (second.forward firstIndex).val = index := by
      have secondRight := second.rightInverse relabeledFinalIndex
      simpa [firstIndex, relabeledFinalIndex] using
        congrArg Fin.val secondRight
    have firstPosition :
        firstIndex.val = (first.forward sourceIndex).val := by
      have firstRight :=
        first.rightInverse
          (Fin.cast (relabel_nodes_length nodes first) firstIndex)
      simpa [sourceIndex] using (congrArg Fin.val firstRight).symm
    have firstIndexExact :
        firstIndex =
          Fin.cast (relabel_nodes_length nodes first).symm
            (first.forward sourceIndex) := by
      apply Fin.ext
      exact firstPosition
    have leftValue :
        (relabelNodes (relabelNodes nodes first) second).get
            ⟨index, leftBound⟩ =
          relabelNode second
            (relabelNode first (nodes.get sourceIndex)) := by
      have outerAtFinal := outerLookup
      have sourceAtFirst :
          (relabelNodes nodes first).get firstIndex =
            relabelNode first (nodes.get sourceIndex) := by
        rw [firstIndexExact]
        simpa using sourceLookup
      simpa [finalPosition, firstPosition] using
        outerAtFinal.trans
          (congrArg (relabelNode second) sourceAtFirst)
    have rightLookup :=
      relabel_nodes_get nodes combined sourceIndex
    have combinedPosition :
        (combined.forward sourceIndex).val = index := by
      change
        (Fin.cast (relabel_nodes_length nodes first)
          (second.forward
            (Fin.cast (relabel_nodes_length nodes first).symm
              (first.forward sourceIndex)))).val = index
      rw [← firstIndexExact]
      exact finalPosition
    rw [leftValue]
    have nodeExact :=
      relabel_node_compose_relabeled first second
        (relabel_nodes_length nodes first)
        (nodes.get sourceIndex)
    have rightValue :
        (relabelNodes nodes combined).get
            ⟨index, rightBound⟩ =
          relabelNode combined (nodes.get sourceIndex) := by
      simpa [combinedPosition] using rightLookup
    exact nodeExact.trans rightValue.symm

theorem owns_local_occurrence_relabel
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length)
    (direction : EdgeDirection)
    (owner target : Fin nodes.length) :
    Closure.OwnsLocalOccurrence
        (relabelNodes nodes bijection)
        (bijection.forward owner).val direction
        (bijection.forward target).val =
      Closure.OwnsLocalOccurrence
        nodes owner.val direction target.val := by
  simp only [Closure.OwnsLocalOccurrence]
  rw [relabel_nodes_get?_forward]
  rw [List.getElem?_eq_getElem owner.isLt]
  simp only [relabelNode]
  exact local_collections_relabel
    (localCollectionsEvidenceAt evidence owner)
    bijection direction target

theorem relabel_local_edge_iff
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length)
    (source target : Fin nodes.length) :
    Closure.LocalEdge
        (relabelNodes nodes bijection)
        (bijection.forward source).val
        (bijection.forward target).val ↔
      Closure.LocalEdge nodes source.val target.val := by
  have criterionEqual :
      Closure.LocalEdgeCriterion
          (relabelNodes nodes bijection)
          (bijection.forward source).val
          (bijection.forward target).val =
        Closure.LocalEdgeCriterion
          nodes source.val target.val := by
    simp [Closure.LocalEdgeCriterion, relabel_nodes_length,
      (bijection.forward source).isLt,
      (bijection.forward target).isLt,
      source.isLt, target.isLt,
      owns_local_occurrence_relabel evidence]
  constructor
  · intro edge
    apply (Closure.local_edge_iff_criterion
      nodes source.val target.val).mpr
    have accepted :=
      (Closure.local_edge_iff_criterion
        (relabelNodes nodes bijection)
        (bijection.forward source).val
        (bijection.forward target).val).mp edge
    rwa [criterionEqual] at accepted
  · intro edge
    apply (Closure.local_edge_iff_criterion
      (relabelNodes nodes bijection)
      (bijection.forward source).val
      (bijection.forward target).val).mpr
    have accepted :=
      (Closure.local_edge_iff_criterion
        nodes source.val target.val).mp edge
    rwa [criterionEqual]

theorem relabel_local_path_forward
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length)
    {source target : Nat}
    (path : Closure.LocalPath nodes source target)
    (sourceBound : source < nodes.length)
    (targetBound : target < nodes.length) :
    Closure.LocalPath
      (relabelNodes nodes bijection)
      (bijection.forward ⟨source, sourceBound⟩).val
      (bijection.forward ⟨target, targetBound⟩).val := by
  induction path with
  | @refl node nodeBound =>
      exact Closure.LocalPath.refl (by
        simp [relabel_nodes_length,
          (bijection.forward ⟨node, nodeBound⟩).isLt])
  | @step first second last edge rest ih =>
      have secondBound :
          second < nodes.length :=
        Closure.local_edge_target_lt edge
      exact Closure.LocalPath.step
        ((relabel_local_edge_iff evidence bijection
          ⟨first, sourceBound⟩ ⟨second, secondBound⟩).mpr edge)
        (ih secondBound targetBound)

theorem relabel_local_path_backward
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length)
    {source target : Nat}
    (path :
      Closure.LocalPath
        (relabelNodes nodes bijection) source target)
    (sourceBound : source < (relabelNodes nodes bijection).length)
    (targetBound : target < (relabelNodes nodes bijection).length) :
    Closure.LocalPath nodes
      (bijection.inverse
        ⟨source, by
          simpa [relabel_nodes_length] using sourceBound⟩).val
      (bijection.inverse
        ⟨target, by
          simpa [relabel_nodes_length] using targetBound⟩).val := by
  induction path with
  | @refl node nodeBound =>
      exact Closure.LocalPath.refl
        (bijection.inverse
          ⟨node, by
            simpa [relabel_nodes_length] using nodeBound⟩).isLt
  | @step first second last edge rest ih =>
      have firstBound :
          first < (relabelNodes nodes bijection).length :=
        Closure.local_edge_source_lt edge
      have secondBound :
          second < (relabelNodes nodes bijection).length :=
        Closure.local_edge_target_lt edge
      let firstIndex : Fin nodes.length :=
        ⟨first, by
          simpa [relabel_nodes_length] using firstBound⟩
      let secondIndex : Fin nodes.length :=
        ⟨second, by
          simpa [relabel_nodes_length] using secondBound⟩
      have relabeledEdge :
          Closure.LocalEdge
            (relabelNodes nodes bijection)
            (bijection.forward
              (bijection.inverse firstIndex)).val
            (bijection.forward
              (bijection.inverse secondIndex)).val := by
        simpa [firstIndex, secondIndex,
          bijection.rightInverse] using edge
      have originalEdge :
          Closure.LocalEdge nodes
            (bijection.inverse firstIndex).val
            (bijection.inverse secondIndex).val :=
        (relabel_local_edge_iff evidence bijection
          (bijection.inverse firstIndex)
          (bijection.inverse secondIndex)).mp relabeledEdge
      exact Closure.LocalPath.step originalEdge
        (ih secondBound targetBound)

theorem relabel_local_path_iff
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length)
    (source target : Fin nodes.length) :
    Closure.LocalPath
        (relabelNodes nodes bijection)
        (bijection.forward source).val
        (bijection.forward target).val ↔
      Closure.LocalPath nodes source.val target.val := by
  constructor
  · intro path
    have transported :=
      relabel_local_path_backward evidence bijection path
        (by
          simp [relabel_nodes_length,
            (bijection.forward source).isLt])
        (by
          simp [relabel_nodes_length,
            (bijection.forward target).isLt])
    simpa only [bijection.leftInverse] using transported
  · intro path
    exact relabel_local_path_forward evidence bijection path
      source.isLt target.isLt

theorem relabel_connectivity_iff
    {sourceKind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema sourceKind nodes.length nodes)
    (bijection : LocalBijection nodes.length) :
    Closure.StronglyConnected (relabelNodes nodes bijection) ↔
      Closure.StronglyConnected nodes := by
  constructor
  · intro relabeledConnected
    have relabeledLengthNeZero :
        (relabelNodes nodes bijection).length ≠ 0 := by
      intro lengthZero
      exact relabeledConnected.1
        (List.eq_nil_of_length_eq_zero lengthZero)
    have relabeledPositive :
        0 < (relabelNodes nodes bijection).length :=
      Nat.pos_of_ne_zero relabeledLengthNeZero
    have nodesPositive : 0 < nodes.length := by
      rw [relabel_nodes_length] at relabeledPositive
      exact relabeledPositive
    refine ⟨List.ne_nil_of_length_pos nodesPositive, ?_⟩
    intro source target sourceBound targetBound
    let sourceIndex : Fin nodes.length :=
      ⟨source, sourceBound⟩
    let targetIndex : Fin nodes.length :=
      ⟨target, targetBound⟩
    have relabeledPath :=
      relabeledConnected.2
        (bijection.forward sourceIndex).val
        (bijection.forward targetIndex).val
        (by
          simp [relabel_nodes_length,
            (bijection.forward sourceIndex).isLt])
        (by
          simp [relabel_nodes_length,
            (bijection.forward targetIndex).isLt])
    exact (relabel_local_path_iff evidence bijection
      sourceIndex targetIndex).mp relabeledPath
  · intro connected
    have nodesLengthNeZero : nodes.length ≠ 0 := by
      intro lengthZero
      exact connected.1
        (List.eq_nil_of_length_eq_zero lengthZero)
    have nodesPositive : 0 < nodes.length :=
      Nat.pos_of_ne_zero nodesLengthNeZero
    have relabeledPositive :
        0 < (relabelNodes nodes bijection).length := by
      simpa [relabel_nodes_length] using nodesPositive
    refine
      ⟨List.ne_nil_of_length_pos relabeledPositive, ?_⟩
    intro source target sourceBound targetBound
    let sourceIndex : Fin nodes.length :=
      ⟨source, by
        simpa [relabel_nodes_length] using sourceBound⟩
    let targetIndex : Fin nodes.length :=
      ⟨target, by
        simpa [relabel_nodes_length] using targetBound⟩
    have originalPath :=
      connected.2
        (bijection.inverse sourceIndex).val
        (bijection.inverse targetIndex).val
        (bijection.inverse sourceIndex).isLt
        (bijection.inverse targetIndex).isLt
    have relabeledPath :=
      (relabel_local_path_iff evidence bijection
        (bijection.inverse sourceIndex)
        (bijection.inverse targetIndex)).mpr originalPath
    simpa [sourceIndex, targetIndex,
      bijection.rightInverse] using relabeledPath

def relabelRawBlock
    {schema : GraphKindSchema} {kind : schema.Kind}
    (block : RawBlockCandidate schema kind)
    (bijection : LocalBijection block.nodeCount) :
    RawBlockCandidate schema kind :=
  match block with
  | .dagSingleton node =>
      .dagSingleton (relabelNode bijection node)
  | .cyclic nodes supplied =>
      let relabeled := relabelNodes nodes bijection
      let relabeledCertificate :=
        match supplied with
        | none => none
        | some _ =>
            match Closure.buildConnectivityCertificate relabeled with
            | .ok certificate => some certificate
            | .error _ => none
      .cyclic relabeled relabeledCertificate

theorem relabel_raw_block_preserves_cyclic_certificate
    {schema : GraphKindSchema} {kind : schema.Kind}
    {nodes : List (RawNode schema)}
    (evidence :
      Closure.LocalNodesEvidence schema kind nodes.length nodes)
    (certificate : Closure.ConnectivityCertificate nodes)
    (bijection : LocalBijection nodes.length) :
    ∃ relabeledCertificate,
      relabelRawBlock
          (.cyclic nodes (some certificate) :
            RawBlockCandidate schema kind)
          bijection =
        .cyclic (relabelNodes nodes bijection)
          (some relabeledCertificate) := by
  have connected :
      Closure.StronglyConnected
        (relabelNodes nodes bijection) :=
    (relabel_connectivity_iff evidence bijection).mpr
      certificate.stronglyConnected
  obtain ⟨relabeledCertificate, built⟩ :=
    Closure.build_connectivity_complete connected
  exact ⟨relabeledCertificate, by
    simp [relabelRawBlock, built]⟩

theorem relabel_raw_block_node_count
    {schema : GraphKindSchema} {kind : schema.Kind}
    (block : RawBlockCandidate schema kind)
    (bijection : LocalBijection block.nodeCount) :
    (relabelRawBlock block bijection).nodeCount =
      block.nodeCount := by
  cases block with
  | dagSingleton =>
      rfl
  | cyclic nodes certificate =>
      exact relabel_nodes_length nodes bijection

theorem cyclic_candidate_eq_of_nodes_eq
    {schema : GraphKindSchema} {kind : schema.Kind}
    {left right : List (RawNode schema)}
    (nodesExact : left = right)
    (leftCertificate : Closure.ConnectivityCertificate left)
    (rightCertificate : Closure.ConnectivityCertificate right) :
    (RawBlockCandidate.cyclic left (some leftCertificate) :
        RawBlockCandidate schema kind) =
      .cyclic right (some rightCertificate) := by
  subst right
  have certificatesExact :
      leftCertificate = rightCertificate := by
    cases leftCertificate
    cases rightCertificate
    congr
  rw [certificatesExact]

theorem relabel_raw_block_congr
    {schema : GraphKindSchema} {kind : schema.Kind}
    {left right : RawBlockCandidate schema kind}
    (blockExact : left = right)
    (leftBijection : LocalBijection left.nodeCount)
    (rightBijection : LocalBijection right.nodeCount)
    (bijectionExact : HEq leftBijection rightBijection) :
    relabelRawBlock left leftBijection =
      relabelRawBlock right rightBijection := by
  subst right
  cases bijectionExact
  rfl

theorem relabel_raw_block_compose
    {schema : GraphKindSchema} {kind : schema.Kind}
    (block : RawBlockCandidate schema kind)
    (localEvidence :
      Closure.CandidateLocalEvidence schema kind block)
    (first : LocalBijection block.nodeCount)
    (second :
      LocalBijection (relabelRawBlock block first).nodeCount) :
    relabelRawBlock (relabelRawBlock block first) second =
      relabelRawBlock block
        (composeRelabeledLocalBijection first second
          (relabel_raw_block_node_count block first)) := by
  cases localEvidence with
  | @dag node dagEvidence =>
      simp only [relabelRawBlock]
      exact congrArg RawBlockCandidate.dagSingleton
        (relabel_node_compose_relabeled first second rfl node)
  | @cyclic nodes supplied nodesEvidence =>
      cases supplied with
      | none =>
          simp only [relabelRawBlock]
          exact congrArg (fun relabeled =>
            RawBlockCandidate.cyclic relabeled none)
            (relabel_nodes_compose nodes first second)
      | some certificate =>
          have firstConnected :
              Closure.StronglyConnected (relabelNodes nodes first) :=
            (relabel_connectivity_iff nodesEvidence first).mpr
              certificate.stronglyConnected
          obtain ⟨firstCertificate, firstBuilt⟩ :=
            Closure.build_connectivity_complete firstConnected
          have relabeledEvidence :=
            relabelLocalNodesEvidence nodesEvidence first
          have secondConnected :
              Closure.StronglyConnected
                (relabelNodes (relabelNodes nodes first) second) :=
            (relabel_connectivity_iff relabeledEvidence second).mpr
              firstCertificate.stronglyConnected
          obtain ⟨secondCertificate, secondBuilt⟩ :=
            Closure.build_connectivity_complete secondConnected
          let combined :=
            composeRelabeledLocalBijection first second
              (relabel_nodes_length nodes first)
          have combinedConnected :
              Closure.StronglyConnected
                (relabelNodes nodes combined) :=
            (relabel_connectivity_iff nodesEvidence combined).mpr
              certificate.stronglyConnected
          obtain ⟨combinedCertificate, combinedBuilt⟩ :=
            Closure.build_connectivity_complete combinedConnected
          have nodesExact :=
            relabel_nodes_compose nodes first second
          have firstExact :
              relabelRawBlock
                  (.cyclic nodes (some certificate) :
                    RawBlockCandidate schema kind)
                  first =
                .cyclic (relabelNodes nodes first)
                  (some firstCertificate) := by
            simp [relabelRawBlock, firstBuilt]
          have secondExact :
              relabelRawBlock
                  (.cyclic (relabelNodes nodes first)
                    (some firstCertificate) :
                    RawBlockCandidate schema kind)
                  second =
                .cyclic
                  (relabelNodes (relabelNodes nodes first) second)
                  (some secondCertificate) := by
            simp [relabelRawBlock, secondBuilt]
          have combinedExact :
              relabelRawBlock
                  (.cyclic nodes (some certificate) :
                    RawBlockCandidate schema kind)
                  combined =
                .cyclic (relabelNodes nodes combined)
                  (some combinedCertificate) := by
            simp [relabelRawBlock, combinedBuilt]
          have firstCongruence :=
            relabel_raw_block_congr firstExact second second
              (HEq.rfl : HEq second second)
          exact firstCongruence.trans
            (secondExact.trans
              ((cyclic_candidate_eq_of_nodes_eq nodesExact
                  secondCertificate combinedCertificate).trans
                combinedExact.symm))

/-! ## Lower-rank materialization carriers -/

structure SomeCanonicalBlock (context : GraphCodecContext) where
  kind : context.kindSchema.Kind
  blockQ :
    GraphWireAddress (context.kindSchema.toAddressKind kind)
  block : CanonicalBlock context.kindSchema kind

structure CanonicalRegistryKey (schema : GraphKindSchema) where
  kind : schema.Kind
  blockQ : GraphWireAddress (schema.toAddressKind kind)

def SomeCanonicalBlock.key
    (entry : SomeCanonicalBlock context) :
    CanonicalRegistryKey context.kindSchema :=
  ⟨entry.kind, entry.blockQ⟩

def encodeCanonicalRegistryKey
    (context : GraphCodecContext)
    (key : CanonicalRegistryKey context.kindSchema) : GraphBytes :=
  [context.kindSchema.kindCode key.kind,
    key.blockQ.algorithm.scalars.length,
    key.blockQ.domainQ.scalars.length,
    key.blockQ.schemaQ.scalars.length] ++
    key.blockQ.algorithm.scalars.map Char.toNat ++
    key.blockQ.domainQ.scalars.map Char.toNat ++
    key.blockQ.schemaQ.scalars.map Char.toNat ++
    key.blockQ.digest.scalars.map Char.toNat

def encodeRawKeyIdentity
    (key : Closure.RawKeyIdentity) : GraphBytes :=
  [key.kindCode,
    key.algorithm.scalars.length,
    key.domainQ.scalars.length,
    key.schemaQ.scalars.length] ++
    key.algorithm.scalars.map Char.toNat ++
    key.domainQ.scalars.map Char.toNat ++
    key.schemaQ.scalars.map Char.toNat ++
    key.digest.scalars.map Char.toNat

private def graphTextOfCodes (codes : GraphBytes) : GraphText :=
  ⟨codes.map Char.ofNat⟩

def decodeRawKeyIdentity :
    GraphBytes → Option Closure.RawKeyIdentity
  | kindCode :: algorithmLength :: domainLength ::
      schemaLength :: payload =>
      let algorithmCodes := payload.take algorithmLength
      let afterAlgorithm := payload.drop algorithmLength
      let domainCodes := afterAlgorithm.take domainLength
      let afterDomain := afterAlgorithm.drop domainLength
      let schemaCodes := afterDomain.take schemaLength
      let digestCodes := afterDomain.drop schemaLength
      some
        { kindCode
          algorithm := graphTextOfCodes algorithmCodes
          domainQ := graphTextOfCodes domainCodes
          schemaQ := graphTextOfCodes schemaCodes
          digest := graphTextOfCodes digestCodes }
  | _ =>
      none

private theorem graph_text_of_codes_encode
    (text : GraphText) :
    graphTextOfCodes (text.scalars.map Char.toNat) = text := by
  cases text with
  | mk scalars =>
      simp only [graphTextOfCodes]
      congr
      induction scalars with
      | nil =>
          rfl
      | cons head tail ih =>
          simp [ih, Char.ofNat_toNat]

theorem decode_encode_raw_key_identity
    (key : Closure.RawKeyIdentity) :
    decodeRawKeyIdentity (encodeRawKeyIdentity key) = some key := by
  rcases key with
    ⟨kindCode, algorithm, domainQ, schemaQ, digest⟩
  simp [
    decodeRawKeyIdentity, encodeRawKeyIdentity,
    List.length_map, graph_text_of_codes_encode
  ]

theorem encode_raw_key_identity_injective
    {left right : Closure.RawKeyIdentity}
    (encodedExact :
      encodeRawKeyIdentity left = encodeRawKeyIdentity right) :
    left = right := by
  have decodedExact :=
    congrArg decodeRawKeyIdentity encodedExact
  rw [
    decode_encode_raw_key_identity,
    decode_encode_raw_key_identity
  ] at decodedExact
  exact Option.some.inj decodedExact

def CanonicalRegistryKeysNoDup
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Prop :=
  NoDuplicates
    (registry.map
      (fun entry => encodeCanonicalRegistryKey context entry.key))

structure CanonicalLabelMap
    (rawBlock : RawBlockCandidate schema kind)
    (canonicalBlock : CanonicalBlock schema kind) where
  forward :
    Fin rawBlock.nodeCount →
      Fin canonicalBlock.nodes.length
  inverse :
    Fin canonicalBlock.nodes.length →
      Fin rawBlock.nodeCount
  leftInverse : ∀ index, inverse (forward index) = index
  rightInverse : ∀ index, forward (inverse index) = index

def transportCanonicalLabelMap
    {leftRaw rightRaw : RawBlockCandidate schema kind}
    {leftCanonical rightCanonical : CanonicalBlock schema kind}
    (rawExact : leftRaw = rightRaw)
    (canonicalExact : leftCanonical = rightCanonical)
    (labels : CanonicalLabelMap leftRaw leftCanonical) :
    CanonicalLabelMap rightRaw rightCanonical := by
  subst rightRaw
  subst rightCanonical
  exact labels

def canonicalLabelMapOfRelabeledRawBlock
    (rawBlock : RawBlockCandidate schema kind)
    (bijection : LocalBijection rawBlock.nodeCount)
    (canonicalBlock : CanonicalBlock schema kind)
    (labels :
      CanonicalLabelMap
        (relabelRawBlock rawBlock bijection) canonicalBlock) :
    CanonicalLabelMap rawBlock canonicalBlock :=
  let nodeCountExact :=
    relabel_raw_block_node_count rawBlock bijection
  { forward := fun index =>
      labels.forward
        (Fin.cast nodeCountExact.symm (bijection.forward index))
    inverse := fun index =>
      bijection.inverse
        (Fin.cast nodeCountExact (labels.inverse index))
    leftInverse := by
      intro index
      change
        bijection.inverse
            (Fin.cast nodeCountExact
              (labels.inverse
                (labels.forward
                  (Fin.cast nodeCountExact.symm
                    (bijection.forward index))))) =
          index
      rw [labels.leftInverse]
      rw [Fin.cast_trans]
      exact bijection.leftInverse index
    rightInverse := by
      intro index
      change
        labels.forward
            (Fin.cast nodeCountExact.symm
              (bijection.forward
                (bijection.inverse
                  (Fin.cast nodeCountExact
                    (labels.inverse index))))) =
          index
      rw [bijection.rightInverse]
      rw [Fin.cast_trans]
      exact labels.rightInverse index
  }

structure FinalizedTarget
    (closed : StructurallyClosedRootedGraph context ingest)
    (raw : RawInRegistryRef context.kindSchema)
    (target : RawTargetMember closed.rawGraph raw)
    (sourceRank : Nat) where
  targetRankLower :
    target.targetEntry.dependencyRank < sourceRank
  canonicalBlock :
    CanonicalBlock context.kindSchema raw.kind
  labelMap :
    CanonicalLabelMap target.targetEntry.candidate canonicalBlock
  derivedBlockQ :
    GraphWireAddress
      (context.kindSchema.toAddressKind raw.kind)
  derivedBlockQExact :
    derivedBlockQ.toAddress =
      (context.blockBinding raw.kind).address
        (encodeCanonicalBlock canonicalBlock)
  claimedAddressAgreement :
    raw.targetKey.claimedBlockQ = derivedBlockQ

structure TargetFinalizationEnv
    (closed : StructurallyClosedRootedGraph context ingest)
    (sourceRank : Nat) where
  lookup :
    ∀ (raw : RawInRegistryRef context.kindSchema)
      (target : RawTargetMember closed.rawGraph raw)
      (_rawBound : RawTargetMemberBound target)
      (_rankLower :
        target.targetEntry.dependencyRank < sourceRank),
      FinalizedTarget closed raw target sourceRank

def RawExternalRefOccursAt
    (candidate : RawBlockCandidate schema kind)
    (sourceNodeIndex owningCollectionIndex : Nat)
    (expectedTargetKind : schema.Kind)
    (targetPosition : Nat)
    (ref : RawInRegistryRef schema) : Prop :=
  ∃ node collection,
    candidate.nodes[sourceNodeIndex]? = some node ∧
    node.edgeCollections[owningCollectionIndex]? =
      some collection ∧
    collection.expectedTargetKind = expectedTargetKind ∧
    collection.targets[targetPosition]? =
      some (.external ref)

structure RawExternalReferenceOccurrence
    (candidate : RawBlockCandidate schema kind) where
  sourceNodeIndex : Nat
  owningCollectionIndex : Nat
  expectedTargetKind : schema.Kind
  ref : RawInRegistryRef schema
  targetPosition : Nat
  occursExactly :
    RawExternalRefOccursAt candidate sourceNodeIndex
      owningCollectionIndex expectedTargetKind targetPosition ref

structure ValidatedRawOccurrenceEvidence
    (closed : StructurallyClosedRootedGraph context ingest)
    (sourceEntry : SomeRawBlockEntry context.kindSchema)
    (candidate :
      RawBlockCandidate context.kindSchema sourceEntry.kind)
    (occurrence : RawExternalReferenceOccurrence candidate) where
  target : RawTargetMember closed.rawGraph occurrence.ref
  rawBound : RawTargetMemberBound target
  strictRank :
    target.targetEntry.dependencyRank <
      sourceEntry.entry.dependencyRank
  retainedResolvedTarget :
    ResolvedRawTarget context ingest occurrence.ref
  retainedFromClosure :
    ∃ occurrenceProof :
        RawReferenceOccurs closed.rawGraph occurrence.ref,
      closed.resolvedTarget occurrence.ref occurrenceProof =
        ⟨target, rawBound, retainedResolvedTarget⟩

structure ValidatedRawSourceBlock
    (closed : StructurallyClosedRootedGraph context ingest) where
  sourceEntry : SomeRawBlockEntry context.kindSchema
  sourceEntryMember :
    sourceEntry ∈ closed.rawGraph.blockRegistry
  sourceLocalEvidence :
    Nonempty
      (Closure.CandidateLocalEvidence
        context.kindSchema sourceEntry.kind
        sourceEntry.entry.candidate)
  candidate :
    RawBlockCandidate context.kindSchema sourceEntry.kind
  candidateRelabeling :
    LocalBijection sourceEntry.entry.candidate.nodeCount
  candidateDerivedFromMember :
    candidate =
      relabelRawBlock sourceEntry.entry.candidate
        candidateRelabeling
  occurrenceEvidence :
    ∀ occurrence : RawExternalReferenceOccurrence candidate,
      ValidatedRawOccurrenceEvidence
        closed sourceEntry candidate occurrence

def canonicalLabelMapFromValidatedSource
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (canonicalBlock :
      CanonicalBlock
        context.kindSchema source.sourceEntry.kind)
    (labels : CanonicalLabelMap source.candidate canonicalBlock) :
    CanonicalLabelMap
      source.sourceEntry.entry.candidate canonicalBlock := by
  exact
    canonicalLabelMapOfRelabeledRawBlock
      source.sourceEntry.entry.candidate source.candidateRelabeling
      canonicalBlock
      (transportCanonicalLabelMap
        source.candidateDerivedFromMember rfl labels)

def transportValidatedSourceCanonicalLabelMap
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (raw : SomeRawBlockEntry context.kindSchema)
    (sourceEntryExact : source.sourceEntry = raw)
    (sourceCanonical :
      CanonicalBlock
        context.kindSchema source.sourceEntry.kind)
    (rawCanonical :
      CanonicalBlock context.kindSchema raw.kind)
    (canonicalExact : HEq sourceCanonical rawCanonical)
    (labels :
      CanonicalLabelMap
        source.sourceEntry.entry.candidate sourceCanonical) :
    CanonicalLabelMap raw.entry.candidate rawCanonical := by
  subst raw
  exact
    transportCanonicalLabelMap rfl
      (eq_of_heq canonicalExact) labels

def materializeRef
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (occurrence :
      RawExternalReferenceOccurrence source.candidate) :
    ExternalRef context.kindSchema :=
  let evidence := source.occurrenceEvidence occurrence
  let finalized :=
    env.lookup occurrence.ref evidence.target evidence.rawBound
      evidence.strictRank
  { kind := occurrence.ref.kind
    target :=
      { blockQ := finalized.derivedBlockQ
        canonicalLocalIndex :=
          (finalized.labelMap.forward
            ⟨occurrence.ref.rawTargetMemberIndex,
              evidence.rawBound⟩).val } }

theorem materialize_ref_total
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (occurrence :
      RawExternalReferenceOccurrence source.candidate) :
    ∃ finalized, materializeRef source env occurrence = finalized :=
  ⟨materializeRef source env occurrence, rfl⟩

theorem raw_block_nodes_length
    (candidate : RawBlockCandidate schema kind) :
    candidate.nodes.length = candidate.nodeCount := by
  cases candidate <;> rfl

def rawBlockNodeIndex
    (candidate : RawBlockCandidate schema kind)
    (index : Fin candidate.nodeCount) :
    Fin candidate.nodes.length :=
  ⟨index.val, by
    rw [raw_block_nodes_length candidate]
    exact index.isLt⟩

theorem relabel_raw_block_nodes_get?_forward
    (candidate : RawBlockCandidate schema kind)
    (bijection : LocalBijection candidate.nodeCount)
    (index : Fin candidate.nodeCount) :
    (relabelRawBlock candidate bijection).nodes[
        (bijection.forward index).val]? =
      some
        (relabelNode bijection
          (candidate.nodes.get
            (rawBlockNodeIndex candidate index))) := by
  cases candidate with
  | dagSingleton node =>
      have indexZero : index = ⟨0, by simp [RawBlockCandidate.nodeCount]⟩ :=
        Fin.ext (Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ index.isLt))
      subst index
      have forwardZero :
          bijection.forward
              ⟨0, by simp [RawBlockCandidate.nodeCount]⟩ =
            ⟨0, by simp [RawBlockCandidate.nodeCount]⟩ :=
        Fin.ext
          (Nat.eq_zero_of_le_zero
            (Nat.le_of_lt_succ
              (bijection.forward
                ⟨0, by
                  simp [RawBlockCandidate.nodeCount]⟩).isLt))
      simp [relabelRawBlock, RawBlockCandidate.nodes,
        rawBlockNodeIndex, forwardZero]
  | cyclic nodes certificate =>
      simpa [relabelRawBlock, RawBlockCandidate.nodes,
        rawBlockNodeIndex] using
        relabel_nodes_get?_forward nodes bijection index

theorem raw_external_reference_occurrence_source_bound
    (candidate : RawBlockCandidate schema kind)
    (bijection : LocalBijection candidate.nodeCount)
    (occurrence :
      RawExternalReferenceOccurrence
        (relabelRawBlock candidate bijection)) :
    occurrence.sourceNodeIndex < candidate.nodeCount := by
  rcases occurrence.occursExactly with
    ⟨_, _, nodeLookup, _, _, _⟩
  have relabeledNodeBound :
      occurrence.sourceNodeIndex <
        (relabelRawBlock candidate bijection).nodes.length :=
    (List.getElem?_eq_some_iff.mp nodeLookup).1
  rw [raw_block_nodes_length] at relabeledNodeBound
  rw [relabel_raw_block_node_count] at relabeledNodeBound
  exact relabeledNodeBound

def pullbackRawExternalReferenceOccurrence
    (candidate : RawBlockCandidate schema kind)
    (bijection : LocalBijection candidate.nodeCount)
    (occurrence :
      RawExternalReferenceOccurrence
        (relabelRawBlock candidate bijection)) :
    RawExternalReferenceOccurrence candidate :=
  let sourceNodeBound :=
    raw_external_reference_occurrence_source_bound
      candidate bijection occurrence
  let relabeledIndex : Fin candidate.nodeCount :=
    ⟨occurrence.sourceNodeIndex, sourceNodeBound⟩
  let sourceIndex : Fin candidate.nodeCount :=
    bijection.inverse relabeledIndex
  { sourceNodeIndex := sourceIndex.val
    owningCollectionIndex := occurrence.owningCollectionIndex
    expectedTargetKind := occurrence.expectedTargetKind
    ref := occurrence.ref
    targetPosition := occurrence.targetPosition
    occursExactly := by
      rcases occurrence.occursExactly with
        ⟨relabeledNode, relabeledCollection, nodeLookup,
          collectionLookup, kindExact, targetLookup⟩
      let sourceListIndex : Fin candidate.nodes.length :=
        rawBlockNodeIndex candidate sourceIndex
      let sourceNode := candidate.nodes.get sourceListIndex
      have forwardSourceIndex :
          (bijection.forward sourceIndex).val =
            occurrence.sourceNodeIndex := by
        exact congrArg Fin.val
          (bijection.rightInverse relabeledIndex)
      have expectedNodeLookup :
          (relabelRawBlock candidate bijection).nodes[
              occurrence.sourceNodeIndex]? =
            some (relabelNode bijection sourceNode) := by
        simpa [sourceNode, sourceListIndex, forwardSourceIndex] using
          relabel_raw_block_nodes_get?_forward
            candidate bijection sourceIndex
      have relabeledNodeExact :
          relabeledNode = relabelNode bijection sourceNode :=
        Option.some.inj (nodeLookup.symm.trans expectedNodeLookup)
      rw [relabeledNodeExact] at collectionLookup
      have collectionBound :
          occurrence.owningCollectionIndex <
            sourceNode.edgeCollections.length := by
        have relabeledBound :
            occurrence.owningCollectionIndex <
              (relabelNode bijection sourceNode).edgeCollections.length :=
          (List.getElem?_eq_some_iff.mp collectionLookup).1
        simpa [relabelNode] using relabeledBound
      let collectionIndex : Fin sourceNode.edgeCollections.length :=
        ⟨occurrence.owningCollectionIndex, collectionBound⟩
      let sourceCollection :=
        sourceNode.edgeCollections.get collectionIndex
      have expectedCollectionLookup :
          (relabelNode bijection sourceNode).edgeCollections[
              occurrence.owningCollectionIndex]? =
            some (relabelCollection bijection sourceCollection) := by
        rw [List.getElem?_eq_getElem (by
          simpa [relabelNode] using collectionBound)]
        simp [relabelNode, sourceCollection, collectionIndex]
      have relabeledCollectionExact :
          relabeledCollection =
            relabelCollection bijection sourceCollection :=
        Option.some.inj
          (collectionLookup.symm.trans expectedCollectionLookup)
      rw [relabeledCollectionExact] at targetLookup kindExact
      have targetBound :
          occurrence.targetPosition <
            sourceCollection.targets.length := by
        have relabeledBound :
            occurrence.targetPosition <
              (relabelCollection bijection
                sourceCollection).targets.length :=
          (List.getElem?_eq_some_iff.mp targetLookup).1
        simpa [relabel_collection_targets] using relabeledBound
      let targetIndex : Fin sourceCollection.targets.length :=
        ⟨occurrence.targetPosition, targetBound⟩
      let sourceTarget := sourceCollection.targets.get targetIndex
      have expectedTargetLookup :
          (relabelCollection bijection sourceCollection).targets[
              occurrence.targetPosition]? =
            some (relabelGraphRef bijection sourceTarget) := by
        rw [List.getElem?_eq_getElem (by
          simpa [relabel_collection_targets] using targetBound)]
        simp [relabel_collection_targets, sourceTarget, targetIndex]
      have relabeledTargetExact :
          relabelGraphRef bijection sourceTarget =
            .external occurrence.ref :=
        Option.some.inj
          (expectedTargetLookup.symm.trans targetLookup)
      have sourceTargetExact :
          sourceTarget = .external occurrence.ref :=
        (relabel_graph_ref_eq_external_iff
          bijection sourceTarget occurrence.ref).mp
            relabeledTargetExact
      refine ⟨sourceNode, sourceCollection, ?_, ?_, ?_, ?_⟩
      · exact List.getElem?_eq_getElem sourceListIndex.isLt
      · exact List.getElem?_eq_getElem collectionIndex.isLt
      · rw [relabel_collection_expected_target_kind] at kindExact
        exact kindExact
      · rw [List.getElem?_eq_getElem targetIndex.isLt]
        exact congrArg some sourceTargetExact }

theorem raw_source_occurrence_reference_occurs
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (source : SomeRawBlockEntry context.kindSchema)
    (sourceMember : source ∈ closed.rawGraph.blockRegistry)
    (occurrence :
      RawExternalReferenceOccurrence source.entry.candidate) :
    RawReferenceOccurs closed.rawGraph occurrence.ref := by
  rcases occurrence.occursExactly with
    ⟨node, collection, nodeLookup, collectionLookup,
      _, targetLookup⟩
  exact Closure.raw_reference_occurs_of_exact_position
    closed.rawGraph source sourceMember occurrence.sourceNodeIndex
    occurrence.owningCollectionIndex occurrence.targetPosition
    node collection occurrence.ref nodeLookup collectionLookup
    targetLookup

theorem raw_source_occurrence_resolved_strict
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (source : SomeRawBlockEntry context.kindSchema)
    (sourceMember : source ∈ closed.rawGraph.blockRegistry)
    (occurrence :
      RawExternalReferenceOccurrence source.entry.candidate) :
    let occurs :=
      raw_source_occurrence_reference_occurs
        closed source sourceMember occurrence
    (closed.resolvedTarget occurrence.ref
        occurs).target.targetEntry.dependencyRank <
      source.entry.dependencyRank := by
  rcases occurrence.occursExactly with
    ⟨node, collection, nodeLookup, collectionLookup,
      _, targetLookup⟩
  let globalOccurrence : RawExternalOccurrence context.kindSchema :=
    { ownerKind := source.kind
      ownerKey := ⟨source.entry.claimedBlockQ⟩
      ownerRank := source.entry.dependencyRank
      expectedTargetKind := collection.expectedTargetKind
      ref := occurrence.ref }
  have globalMember :
      globalOccurrence ∈
        Closure.rawExternalOccurrences closed.rawGraph :=
    Closure.raw_external_occurrence_mem_of_exact_position
      closed.rawGraph source sourceMember occurrence.sourceNodeIndex
      occurrence.owningCollectionIndex occurrence.targetPosition
      node collection occurrence.ref nodeLookup collectionLookup
      targetLookup
  let expectedOccurs :=
    raw_source_occurrence_reference_occurs
      closed source sourceMember occurrence
  let globalOccurs :=
    Closure.raw_reference_occurs_of_occurrence_member
      closed.rawGraph globalOccurrence globalMember
  have occursExact : expectedOccurs = globalOccurs :=
    Subsingleton.elim expectedOccurs globalOccurs
  have targetExact :
      closed.resolvedTarget occurrence.ref expectedOccurs =
        closed.resolvedTarget occurrence.ref globalOccurs :=
    congrArg (closed.resolvedTarget occurrence.ref) occursExact
  have strict :=
    closed.resolvedStrictRank globalOccurrence globalMember
  dsimp [globalOccurrence, globalOccurs] at strict
  dsimp only
  rw [targetExact]
  exact strict

def validatedRawSourceBlockOfMember
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (source : SomeRawBlockEntry context.kindSchema)
    (sourceMember : source ∈ closed.rawGraph.blockRegistry) :
    ValidatedRawSourceBlock closed where
  sourceEntry := source
  sourceEntryMember := sourceMember
  sourceLocalEvidence :=
    Closure.candidate_local_evidence_of_member
      closed.localWitness source sourceMember
  candidate :=
    relabelRawBlock source.entry.candidate
      (identityLocalBijection source.entry.candidate.nodeCount)
  candidateRelabeling :=
    identityLocalBijection source.entry.candidate.nodeCount
  candidateDerivedFromMember := rfl
  occurrenceEvidence := by
    intro occurrence
    let pulled :=
      pullbackRawExternalReferenceOccurrence
        source.entry.candidate
        (identityLocalBijection source.entry.candidate.nodeCount)
        occurrence
    let occurs :=
      raw_source_occurrence_reference_occurs
        closed source sourceMember pulled
    let resolved :=
      closed.resolvedTarget pulled.ref occurs
    refine
      { target := resolved.target
        rawBound := resolved.rawBound
        strictRank := ?_
        retainedResolvedTarget := resolved.resolved
        retainedFromClosure := ?_ }
    · exact raw_source_occurrence_resolved_strict
        closed source sourceMember pulled
    · exact ⟨occurs, rfl⟩

def composeValidatedSourceRelabeling
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount) :
    LocalBijection
      source.sourceEntry.entry.candidate.nodeCount :=
  let originCandidate :=
    relabelRawBlock source.sourceEntry.entry.candidate
      source.candidateRelabeling
  let nodeCountExact :
      source.candidate.nodeCount = originCandidate.nodeCount :=
    congrArg RawBlockCandidate.nodeCount
      source.candidateDerivedFromMember
  let transportedBijection :=
    transportLocalBijection nodeCountExact bijection
  composeRelabeledLocalBijection
    source.candidateRelabeling transportedBijection
    (relabel_raw_block_node_count
      source.sourceEntry.entry.candidate
      source.candidateRelabeling)

def relabelValidatedSource
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount) :
    ValidatedRawSourceBlock closed where
  sourceEntry := source.sourceEntry
  sourceEntryMember := source.sourceEntryMember
  sourceLocalEvidence := source.sourceLocalEvidence
  candidate := relabelRawBlock source.candidate bijection
  candidateRelabeling :=
    composeValidatedSourceRelabeling source bijection
  candidateDerivedFromMember := by
    rcases source.sourceLocalEvidence with ⟨sourceLocalEvidence⟩
    let originBijection := source.candidateRelabeling
    have originExact :
        source.candidate =
          relabelRawBlock source.sourceEntry.entry.candidate
            originBijection :=
      source.candidateDerivedFromMember
    let originCandidate :=
      relabelRawBlock source.sourceEntry.entry.candidate
        originBijection
    have nodeCountExact :
        source.candidate.nodeCount = originCandidate.nodeCount :=
      congrArg RawBlockCandidate.nodeCount originExact
    let transportedBijection :=
      transportLocalBijection nodeCountExact bijection
    have transportedBijectionExact :
        HEq bijection transportedBijection := by
      simpa [transportedBijection, transportLocalBijection] using
        (eqRec_heq nodeCountExact bijection).symm
    let combined :=
      composeRelabeledLocalBijection
        originBijection transportedBijection
        (relabel_raw_block_node_count
          source.sourceEntry.entry.candidate originBijection)
    change
      relabelRawBlock source.candidate bijection =
        relabelRawBlock source.sourceEntry.entry.candidate
          (composeValidatedSourceRelabeling source bijection)
    have sourceCongruence :=
      relabel_raw_block_congr originExact bijection
        transportedBijection transportedBijectionExact
    have combinedExact :=
      sourceCongruence.trans
      (relabel_raw_block_compose
        source.sourceEntry.entry.candidate
        sourceLocalEvidence originBijection
        transportedBijection)
    simpa
      [composeValidatedSourceRelabeling, originBijection,
        originCandidate, nodeCountExact, transportedBijection,
        combined]
      using combinedExact
  occurrenceEvidence := by
    intro occurrence
    let pulled :=
      pullbackRawExternalReferenceOccurrence
        source.candidate bijection occurrence
    let prior := source.occurrenceEvidence pulled
    exact
      { target := prior.target
        rawBound := prior.rawBound
        strictRank := prior.strictRank
        retainedResolvedTarget := prior.retainedResolvedTarget
        retainedFromClosure := prior.retainedFromClosure }

def transportPermutation
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {source : ValidatedRawSourceBlock closed}
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    PermutationWitness
      (relabelValidatedSource source bijection).candidate.nodeCount :=
  (relabel_raw_block_node_count source.candidate bijection).symm ▸
    transportPermutationSameCount bijection permutation

theorem permutation_bijection_cast_inverse
    {left right : Nat}
    (exact : left = right)
    (permutation : PermutationWitness right)
    (index : Fin right) :
    (permutationBijection (exact.symm ▸ permutation)).inverse
        (Fin.cast exact.symm index) =
      Fin.cast exact.symm
        ((permutationBijection permutation).inverse index) := by
  subst left
  rfl

theorem permutation_bijection_cast_forward
    {left right : Nat}
    (exact : left = right)
    (permutation : PermutationWitness right)
    (index : Fin right) :
    (permutationBijection (exact.symm ▸ permutation)).forward
        (Fin.cast exact.symm index) =
      Fin.cast exact.symm
        ((permutationBijection permutation).forward index) := by
  subst left
  rfl

theorem transport_permutation_inverse
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {source : ValidatedRawSourceBlock closed}
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount)
    (index : Fin source.candidate.nodeCount) :
    (permutationBijection
        (transportPermutation bijection permutation)).inverse
        (Fin.cast
          (relabel_raw_block_node_count
            source.candidate bijection).symm
          index) =
      Fin.cast
        (relabel_raw_block_node_count source.candidate bijection).symm
        (bijection.forward
          ((permutationBijection permutation).inverse index)) := by
  let countExact :=
    relabel_raw_block_node_count source.candidate bijection
  calc
    (permutationBijection
        (transportPermutation bijection permutation)).inverse
        (Fin.cast countExact.symm index) =
      Fin.cast countExact.symm
        ((permutationBijection
          (transportPermutationSameCount bijection permutation)).inverse
          index) := by
        exact permutation_bijection_cast_inverse
          countExact
          (transportPermutationSameCount bijection permutation)
          index
    _ = Fin.cast countExact.symm
        (bijection.forward
          ((permutationBijection permutation).inverse index)) :=
      congrArg (Fin.cast countExact.symm)
        (transport_permutation_inverse_same_count
          bijection permutation index)

theorem transport_permutation_forward
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {source : ValidatedRawSourceBlock closed}
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount)
    (index : Fin source.candidate.nodeCount) :
    (permutationBijection
        (transportPermutation bijection permutation)).forward
        (Fin.cast
          (relabel_raw_block_node_count source.candidate bijection).symm
          (bijection.forward index)) =
      Fin.cast
        (relabel_raw_block_node_count source.candidate bijection).symm
        ((permutationBijection permutation).forward index) := by
  let countExact :=
    relabel_raw_block_node_count source.candidate bijection
  calc
    (permutationBijection
        (transportPermutation bijection permutation)).forward
        (Fin.cast countExact.symm (bijection.forward index)) =
      Fin.cast countExact.symm
        ((permutationBijection
          (transportPermutationSameCount bijection permutation)).forward
          (bijection.forward index)) := by
        exact permutation_bijection_cast_forward
          countExact
          (transportPermutationSameCount bijection permutation)
          (bijection.forward index)
    _ = Fin.cast countExact.symm
        ((permutationBijection permutation).forward index) :=
      congrArg (Fin.cast countExact.symm)
        (transport_permutation_forward_same_count
          bijection permutation index)

theorem transport_permutation_composes
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {source : ValidatedRawSourceBlock closed}
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    composeRelabeledLocalBijection
        bijection
        (permutationBijection
          (transportPermutation bijection permutation))
        (relabel_raw_block_node_count source.candidate bijection) =
      permutationBijection permutation := by
  apply local_bijection_ext
  intro index
  change
    Fin.cast
        (relabel_raw_block_node_count source.candidate bijection)
        ((permutationBijection
          (transportPermutation bijection permutation)).forward
          (Fin.cast
            (relabel_raw_block_node_count
              source.candidate bijection).symm
            (bijection.forward index))) =
      (permutationBijection permutation).forward index
  rw [transport_permutation_forward]
  apply Fin.ext
  rfl

def materializeTargetAt
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (sourceNodeIndex : Fin source.candidate.nodes.length)
    (owningCollectionIndex :
      Fin
        (source.candidate.nodes.get sourceNodeIndex).edgeCollections.length)
    (targetPosition :
      Fin
        (((source.candidate.nodes.get sourceNodeIndex).edgeCollections.get
          owningCollectionIndex).targets.length)) :
    GraphRef (ExternalRef context.kindSchema) :=
  let node := source.candidate.nodes.get sourceNodeIndex
  let collection := node.edgeCollections.get owningCollectionIndex
  match targetExact :
      collection.targets.get targetPosition with
  | .local index => .local index
  | .external ref =>
      let occurrence :
          RawExternalReferenceOccurrence source.candidate :=
        { sourceNodeIndex := sourceNodeIndex.val
          owningCollectionIndex := owningCollectionIndex.val
          expectedTargetKind := collection.expectedTargetKind
          ref := ref
          targetPosition := targetPosition.val
          occursExactly := by
            refine ⟨node, collection, ?_, ?_, rfl, ?_⟩
            · exact List.getElem?_eq_getElem sourceNodeIndex.isLt
            · exact
                List.getElem?_eq_getElem owningCollectionIndex.isLt
            · rw [List.getElem?_eq_getElem targetPosition.isLt]
              exact congrArg some targetExact }
      .external (materializeRef source env occurrence)

def materializeCollectionAt
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (sourceNodeIndex : Fin source.candidate.nodes.length)
    (owningCollectionIndex :
      Fin
        (source.candidate.nodes.get sourceNodeIndex).edgeCollections.length) :
    EdgeCollection context.kindSchema (ExternalRef context.kindSchema) :=
  let node := source.candidate.nodes.get sourceNodeIndex
  let collection := node.edgeCollections.get owningCollectionIndex
  let materializedTargets :=
    (finiteIndices collection.targets.length).map fun targetPosition =>
      materializeTargetAt source env sourceNodeIndex
        owningCollectionIndex targetPosition
  collectionWithTargets collection materializedTargets

def materializeNodeAt
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (sourceNodeIndex : Fin source.candidate.nodes.length) :
    CanonicalNode context.kindSchema :=
  let node := source.candidate.nodes.get sourceNodeIndex
  let collections :=
    (finiteIndices node.edgeCollections.length).map fun collectionIndex =>
      materializeCollectionAt source env sourceNodeIndex collectionIndex
  { payload := node.payload
    edgeCollections := collections }

def normalizeMaterializedNode
    (node : CanonicalNode schema) :
    CanonicalNode schema :=
  let normalizedCollections :=
    node.edgeCollections.map fun collection =>
      collectionWithTargets collection
        (normalizeTargetList collection)
  { payload := node.payload
    edgeCollections :=
      normalizeOuterCollections normalizedCollections }

def materializePermutedNodes
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    List (CanonicalNode context.kindSchema) :=
  let bijection := permutationBijection permutation
  (finiteIndices source.candidate.nodeCount).map fun newIndex =>
    let oldIndex := bijection.inverse newIndex
    let sourceNodeIndex : Fin source.candidate.nodes.length :=
      ⟨oldIndex.val, by
        rw [raw_block_nodes_length source.candidate]
        exact oldIndex.isLt⟩
    normalizeMaterializedNode
      (relabelNode bijection
        (materializeNodeAt source env sourceNodeIndex))

theorem materialize_permuted_nodes_length
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    (materializePermutedNodes source env permutation).length =
      source.candidate.nodeCount := by
  simp [materializePermutedNodes, finite_indices_length]

def assembleMaterializedCandidate
    (candidate : RawBlockCandidate schema kind)
    (nodes : List (CanonicalNode schema))
    (nodesLength : nodes.length = candidate.nodeCount) :
    CanonicalBlock schema kind :=
  match candidateExact : candidate with
  | .dagSingleton _ =>
      .dagSingleton
        (nodes.get
          ⟨0, by
            rw [nodesLength]
            simp [RawBlockCandidate.nodeCount]⟩)
  | .cyclic _ _ => .cyclic nodes

theorem assemble_materialized_candidate_nodes_length
    (candidate : RawBlockCandidate schema kind)
    (nodes : List (CanonicalNode schema))
    (nodesLength : nodes.length = candidate.nodeCount) :
    (assembleMaterializedCandidate candidate nodes nodesLength).nodes.length =
      candidate.nodeCount := by
  cases candidate with
  | dagSingleton node =>
      rfl
  | cyclic sourceNodes certificate =>
      exact nodesLength

theorem assemble_materialized_candidate_relabel
    (candidate : RawBlockCandidate schema kind)
    (bijection : LocalBijection candidate.nodeCount)
    (nodes : List (CanonicalNode schema))
    (relabeledLength :
      nodes.length = (relabelRawBlock candidate bijection).nodeCount)
    (sourceLength : nodes.length = candidate.nodeCount) :
    assembleMaterializedCandidate
        (relabelRawBlock candidate bijection) nodes relabeledLength =
      assembleMaterializedCandidate candidate nodes sourceLength := by
  cases candidate <;> rfl

theorem assemble_materialized_candidate_nodes_congr
    (candidate : RawBlockCandidate schema kind)
    (left right : List (CanonicalNode schema))
    (leftLength : left.length = candidate.nodeCount)
    (rightLength : right.length = candidate.nodeCount)
    (nodesExact : left = right) :
    assembleMaterializedCandidate candidate left leftLength =
      assembleMaterializedCandidate candidate right rightLength := by
  subst right
  rfl

def materializeCandidate
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    CanonicalBlock context.kindSchema source.sourceEntry.kind :=
  let nodes := materializePermutedNodes source env permutation
  assembleMaterializedCandidate source.candidate nodes
    (materialize_permuted_nodes_length source env permutation)

theorem materialize_candidate_nodes_length
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    (materializeCandidate source env permutation).nodes.length =
      source.candidate.nodeCount := by
  exact assemble_materialized_candidate_nodes_length
    source.candidate
    (materializePermutedNodes source env permutation)
    (materialize_permuted_nodes_length source env permutation)

def materializedCanonicalLabelMap
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    CanonicalLabelMap source.candidate
      (materializeCandidate source env permutation) :=
  let nodeCountExact :=
    materialize_candidate_nodes_length source env permutation
  let labels := permutationBijection permutation
  { forward := fun index =>
      Fin.cast nodeCountExact.symm (labels.forward index)
    inverse := fun index =>
      labels.inverse (Fin.cast nodeCountExact index)
    leftInverse := by
      intro index
      change
        labels.inverse
            (Fin.cast nodeCountExact
              (Fin.cast nodeCountExact.symm
                (labels.forward index))) =
          index
      rw [Fin.cast_trans]
      exact labels.leftInverse index
    rightInverse := by
      intro index
      change
        Fin.cast nodeCountExact.symm
            (labels.forward
              (labels.inverse (Fin.cast nodeCountExact index))) =
          index
      rw [labels.rightInverse]
      rw [Fin.cast_trans]
      apply Fin.ext
      rfl }

def candidateEncoding
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    GraphBytes :=
  encodeCanonicalBlock
    (materializeCandidate source env permutation)

theorem materialize_ref_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (occurrence :
      RawExternalReferenceOccurrence
        (relabelValidatedSource source bijection).candidate) :
    materializeRef
        (relabelValidatedSource source bijection) env occurrence =
      materializeRef source env
        (pullbackRawExternalReferenceOccurrence
          source.candidate bijection occurrence) := by
  rfl

theorem relabeled_raw_block_node_get
    (candidate : RawBlockCandidate schema kind)
    (bijection : LocalBijection candidate.nodeCount)
    (index : Fin candidate.nodeCount) :
    (relabelRawBlock candidate bijection).nodes.get
        (rawBlockNodeIndex (relabelRawBlock candidate bijection)
          (Fin.cast
            (relabel_raw_block_node_count candidate bijection).symm
            (bijection.forward index))) =
      relabelNode bijection
        (candidate.nodes.get (rawBlockNodeIndex candidate index)) := by
  have lookup :=
    relabel_raw_block_nodes_get?_forward candidate bijection index
  rw [List.getElem?_eq_getElem (by
    rw [raw_block_nodes_length]
    rw [relabel_raw_block_node_count]
    exact (bijection.forward index).isLt)] at lookup
  exact Option.some.inj (by
    simpa [rawBlockNodeIndex] using lookup)

theorem relabel_node_edge_collections_length
    (bijection : LocalBijection n)
    (node : GraphNode schema External) :
    (relabelNode bijection node).edgeCollections.length =
      node.edgeCollections.length := by
  simp [relabelNode]

theorem relabel_node_edge_collection_get
    (bijection : LocalBijection n)
    (node : GraphNode schema External)
    (index : Fin node.edgeCollections.length) :
    (relabelNode bijection node).edgeCollections.get
        (Fin.cast
          (relabel_node_edge_collections_length bijection node).symm
          index) =
      relabelCollection bijection
        (node.edgeCollections.get index) := by
  simp [relabelNode]

theorem relabel_collection_targets_length
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).targets.length =
      collection.targets.length := by
  simp [relabel_collection_targets]

theorem relabel_collection_target_get
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External)
    (index : Fin collection.targets.length) :
    (relabelCollection bijection collection).targets.get
        (Fin.cast
          (relabel_collection_targets_length
            bijection collection).symm
          index) =
      relabelGraphRef bijection
        (collection.targets.get index) := by
  simp [relabel_collection_targets]

def relabeledSourceNodeIndex
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (index : Fin source.candidate.nodeCount) :
    Fin
      (relabelValidatedSource source bijection).candidate.nodes.length :=
  rawBlockNodeIndex
    (relabelValidatedSource source bijection).candidate
    (Fin.cast
      (relabel_raw_block_node_count source.candidate bijection).symm
      (bijection.forward index))

theorem relabeled_validated_source_node_get
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (index : Fin source.candidate.nodeCount) :
    (relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection index) =
      relabelNode bijection
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate index)) := by
  exact relabeled_raw_block_node_get source.candidate bijection index

theorem relabeled_source_node_collections_length
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (index : Fin source.candidate.nodeCount) :
    ((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection index)).edgeCollections.length =
      (source.candidate.nodes.get
        (rawBlockNodeIndex source.candidate index)).edgeCollections.length := by
  rw [relabeled_validated_source_node_get]
  exact relabel_node_edge_collections_length bijection _

def relabeledSourceCollectionIndex
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length) :
    Fin
      (((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.length) :=
  Fin.cast
    (relabeled_source_node_collections_length
      source bijection sourceIndex).symm
    collectionIndex

theorem relabeled_validated_source_collection_get
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length) :
    ((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex) =
      relabelCollection bijection
        ((source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
          collectionIndex) := by
  let relabeledNode :=
    (relabelValidatedSource source bijection).candidate.nodes.get
      (relabeledSourceNodeIndex source bijection sourceIndex)
  let sourceNode :=
    source.candidate.nodes.get
      (rawBlockNodeIndex source.candidate sourceIndex)
  have nodeExact :
      relabeledNode = relabelNode bijection sourceNode := by
    exact relabeled_validated_source_node_get
      source bijection sourceIndex
  have collectionsExact :
      relabeledNode.edgeCollections =
        sourceNode.edgeCollections.map (relabelCollection bijection) := by
    simpa [relabelNode] using
      congrArg GraphNode.edgeCollections nodeExact
  have lookup :
      relabeledNode.edgeCollections[collectionIndex.val]? =
        some
          (relabelCollection bijection
            (sourceNode.edgeCollections.get collectionIndex)) := by
    rw [collectionsExact]
    have mappedBound :
        collectionIndex.val <
          (sourceNode.edgeCollections.map
            (relabelCollection bijection)).length := by
      rw [List.length_map]
      exact collectionIndex.isLt
    rw [List.getElem?_eq_getElem mappedBound]
    simp
  apply Option.some.inj
  calc
    some
        (relabeledNode.edgeCollections.get
          (relabeledSourceCollectionIndex source bijection sourceIndex
            collectionIndex)) =
        relabeledNode.edgeCollections[
          (relabeledSourceCollectionIndex source bijection sourceIndex
            collectionIndex).val]? := by
      exact
        (List.getElem?_eq_getElem
          (relabeledSourceCollectionIndex source bijection sourceIndex
            collectionIndex).isLt).symm
    _ = relabeledNode.edgeCollections[collectionIndex.val]? := by
      rfl
    _ = some
        (relabelCollection bijection
          (sourceNode.edgeCollections.get collectionIndex)) :=
      lookup

theorem relabeled_source_collection_targets_length
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length) :
    (((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex)).targets.length =
      ((source.candidate.nodes.get
        (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
        collectionIndex).targets.length := by
  rw [relabeled_validated_source_collection_get]
  exact relabel_collection_targets_length bijection _

def relabeledSourceTargetIndex
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length)
    (targetIndex :
      Fin
        (((source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
          collectionIndex).targets.length)) :
    Fin
      ((((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex)).targets.length) :=
  Fin.cast
    (relabeled_source_collection_targets_length
      source bijection sourceIndex collectionIndex).symm
    targetIndex

theorem relabeled_validated_source_target_get
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length)
    (targetIndex :
      Fin
        (((source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
          collectionIndex).targets.length)) :
    (((relabelValidatedSource source bijection).candidate.nodes.get
        (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex)).targets.get
        (relabeledSourceTargetIndex source bijection sourceIndex
          collectionIndex targetIndex) =
      relabelGraphRef bijection
        (((source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
          collectionIndex).targets.get targetIndex) := by
  let relabeledCollection :=
    ((relabelValidatedSource source bijection).candidate.nodes.get
      (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
      (relabeledSourceCollectionIndex source bijection sourceIndex
        collectionIndex)
  let sourceCollection :=
    (source.candidate.nodes.get
      (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
      collectionIndex
  have collectionExact :
      relabeledCollection =
        relabelCollection bijection sourceCollection := by
    exact relabeled_validated_source_collection_get
      source bijection sourceIndex collectionIndex
  have targetsExact :
      relabeledCollection.targets =
        sourceCollection.targets.map (relabelGraphRef bijection) := by
    simpa [relabel_collection_targets] using
      congrArg EdgeCollection.targets collectionExact
  have lookup :
      relabeledCollection.targets[targetIndex.val]? =
        some
          (relabelGraphRef bijection
            (sourceCollection.targets.get targetIndex)) := by
    rw [targetsExact]
    have mappedBound :
        targetIndex.val <
          (sourceCollection.targets.map
            (relabelGraphRef bijection)).length := by
      rw [List.length_map]
      exact targetIndex.isLt
    rw [List.getElem?_eq_getElem mappedBound]
    simp
  apply Option.some.inj
  calc
    some
        (relabeledCollection.targets.get
          (relabeledSourceTargetIndex source bijection sourceIndex
            collectionIndex targetIndex)) =
        relabeledCollection.targets[
          (relabeledSourceTargetIndex source bijection sourceIndex
            collectionIndex targetIndex).val]? := by
      exact
        (List.getElem?_eq_getElem
          (relabeledSourceTargetIndex source bijection sourceIndex
            collectionIndex targetIndex).isLt).symm
    _ = relabeledCollection.targets[targetIndex.val]? := by
      rfl
    _ = some
        (relabelGraphRef bijection
          (sourceCollection.targets.get targetIndex)) :=
      lookup

theorem materialize_target_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length)
    (targetIndex :
      Fin
        (((source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
          collectionIndex).targets.length)) :
    materializeTargetAt
        (relabelValidatedSource source bijection) env
        (relabeledSourceNodeIndex source bijection sourceIndex)
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex)
        (relabeledSourceTargetIndex source bijection sourceIndex
          collectionIndex targetIndex) =
      relabelGraphRef bijection
        (materializeTargetAt source env
          (rawBlockNodeIndex source.candidate sourceIndex)
          collectionIndex targetIndex) := by
  dsimp only [materializeTargetAt]
  have targetRelabel :=
    relabeled_validated_source_target_get
      source bijection sourceIndex collectionIndex targetIndex
  symm
  split
  · rename_i index sourceTargetExact
    rw [sourceTargetExact] at targetRelabel
    split
    · rename_i relabeledIndex relabeledTargetExact
      have rawExact :=
        targetRelabel.symm.trans relabeledTargetExact
      by_cases bounded : index < source.candidate.nodeCount
      · have indexExact :
            (bijection.forward ⟨index, bounded⟩).val =
              relabeledIndex := by
          have localExact :
              (GraphRef.local
                (bijection.forward ⟨index, bounded⟩).val :
                GraphRef (RawInRegistryRef context.kindSchema)) =
                .local relabeledIndex := by
            simpa [relabelGraphRef, bounded] using rawExact
          exact GraphRef.local.inj localExact
        simpa [relabelGraphRef, bounded] using
          congrArg
            (fun target =>
              (GraphRef.local target :
                GraphRef (ExternalRef context.kindSchema)))
            indexExact
      · have indexExact : index = relabeledIndex :=
          by
            have localExact :
                (GraphRef.local index :
                  GraphRef (RawInRegistryRef context.kindSchema)) =
                  .local relabeledIndex := by
              simpa [relabelGraphRef, bounded] using rawExact
            exact GraphRef.local.inj localExact
        simpa [relabelGraphRef, bounded] using
          congrArg
            (fun target =>
              (GraphRef.local target :
                GraphRef (ExternalRef context.kindSchema)))
            indexExact
    · rename_i relabeledRef relabeledTargetExact
      have impossible :
          (GraphRef.local index :
            GraphRef (RawInRegistryRef context.kindSchema)) =
            .external relabeledRef :=
        (relabel_graph_ref_eq_external_iff
          bijection (.local index) relabeledRef).mp
            (targetRelabel.symm.trans relabeledTargetExact)
      cases impossible
  · rename_i ref sourceTargetExact
    rw [sourceTargetExact] at targetRelabel
    split
    · rename_i relabeledIndex relabeledTargetExact
      have impossible :
          (GraphRef.local relabeledIndex :
            GraphRef (RawInRegistryRef context.kindSchema)) =
            .external ref := by
        exact relabeledTargetExact.symm.trans
          (by simpa [relabelGraphRef] using targetRelabel)
      cases impossible
    · rename_i relabeledRef relabeledTargetExact
      have refExact : relabeledRef = ref := by
        exact GraphRef.external.inj
          (relabeledTargetExact.symm.trans
            (by simpa [relabelGraphRef] using targetRelabel))
      subst relabeledRef
      rw [relabel_graph_ref_external]
      congr 1
      rw [materialize_ref_relabel]
      apply congrArg (materializeRef source env)
      simp only [RawExternalReferenceOccurrence.mk.injEq,
        pullbackRawExternalReferenceOccurrence,
        relabeledSourceNodeIndex,
        relabeledSourceCollectionIndex,
        relabeledSourceTargetIndex]
      constructor
      · change
          sourceIndex.val =
            (bijection.inverse (bijection.forward sourceIndex)).val
        exact congrArg Fin.val (bijection.leftInverse sourceIndex).symm
      · have collectionExact :=
          relabeled_validated_source_collection_get
            source bijection sourceIndex collectionIndex
        have kindExact :=
          congrArg EdgeCollection.expectedTargetKind collectionExact
        rw [relabel_collection_expected_target_kind] at kindExact
        constructor
        · rfl
        constructor
        · exact kindExact.symm
        constructor
        · trivial
        · rfl

theorem collection_with_targets_relabel
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    collectionWithTargets
        (relabelCollection bijection collection)
        (targets.map (relabelGraphRef bijection)) =
      relabelCollection bijection
        (collectionWithTargets collection targets) := by
  cases collection <;> rfl

theorem materialize_collection_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount)
    (collectionIndex :
      Fin
        (source.candidate.nodes.get
          (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.length) :
    materializeCollectionAt
        (relabelValidatedSource source bijection) env
        (relabeledSourceNodeIndex source bijection sourceIndex)
        (relabeledSourceCollectionIndex source bijection sourceIndex
          collectionIndex) =
      relabelCollection bijection
        (materializeCollectionAt source env
          (rawBlockNodeIndex source.candidate sourceIndex)
          collectionIndex) := by
  let sourceCollection :=
    (source.candidate.nodes.get
      (rawBlockNodeIndex source.candidate sourceIndex)).edgeCollections.get
      collectionIndex
  let relabeledCollection :=
    ((relabelValidatedSource source bijection).candidate.nodes.get
      (relabeledSourceNodeIndex source bijection sourceIndex)).edgeCollections.get
      (relabeledSourceCollectionIndex source bijection sourceIndex
        collectionIndex)
  have collectionExact :
      relabeledCollection =
        relabelCollection bijection sourceCollection :=
    relabeled_validated_source_collection_get
      source bijection sourceIndex collectionIndex
  have targetIndicesExact :
      finiteIndices relabeledCollection.targets.length =
        (finiteIndices sourceCollection.targets.length).map
          (relabeledSourceTargetIndex source bijection sourceIndex
            collectionIndex) := by
    exact finite_indices_cast
      (relabeled_source_collection_targets_length
        source bijection sourceIndex collectionIndex)
  let sourceTargets :=
    (finiteIndices sourceCollection.targets.length).map
      (fun targetPosition =>
        materializeTargetAt source env
          (rawBlockNodeIndex source.candidate sourceIndex)
          collectionIndex targetPosition)
  let relabeledTargets :=
    (finiteIndices relabeledCollection.targets.length).map
      (fun targetPosition =>
        materializeTargetAt
          (relabelValidatedSource source bijection) env
          (relabeledSourceNodeIndex source bijection sourceIndex)
          (relabeledSourceCollectionIndex source bijection sourceIndex
            collectionIndex)
          targetPosition)
  have targetsExact :
      relabeledTargets =
        sourceTargets.map (relabelGraphRef bijection) := by
    simp only [sourceTargets, relabeledTargets]
    rw [targetIndicesExact]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro targetPosition _
    exact materialize_target_relabel
      source env bijection sourceIndex collectionIndex targetPosition
  unfold materializeCollectionAt
  change
    collectionWithTargets relabeledCollection relabeledTargets =
      relabelCollection bijection
        (collectionWithTargets sourceCollection sourceTargets)
  rw [collectionExact, targetsExact]
  exact collection_with_targets_relabel
    bijection sourceCollection sourceTargets

theorem materialize_node_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (sourceIndex : Fin source.candidate.nodeCount) :
    materializeNodeAt
        (relabelValidatedSource source bijection) env
        (relabeledSourceNodeIndex source bijection sourceIndex) =
      relabelNode bijection
        (materializeNodeAt source env
          (rawBlockNodeIndex source.candidate sourceIndex)) := by
  let sourceNode :=
    source.candidate.nodes.get
      (rawBlockNodeIndex source.candidate sourceIndex)
  let relabeledNode :=
    (relabelValidatedSource source bijection).candidate.nodes.get
      (relabeledSourceNodeIndex source bijection sourceIndex)
  have nodeExact :
      relabeledNode = relabelNode bijection sourceNode :=
    relabeled_validated_source_node_get
      source bijection sourceIndex
  have payloadExact :
      relabeledNode.payload = sourceNode.payload := by
    have exact := congrArg GraphNode.payload nodeExact
    simpa [relabelNode] using exact
  have collectionIndicesExact :
      finiteIndices relabeledNode.edgeCollections.length =
        (finiteIndices sourceNode.edgeCollections.length).map
          (relabeledSourceCollectionIndex source bijection sourceIndex) := by
    exact finite_indices_cast
      (relabeled_source_node_collections_length
        source bijection sourceIndex)
  let sourceCollections :=
    (finiteIndices sourceNode.edgeCollections.length).map
      (fun collectionIndex =>
        materializeCollectionAt source env
          (rawBlockNodeIndex source.candidate sourceIndex)
          collectionIndex)
  let relabeledCollections :=
    (finiteIndices relabeledNode.edgeCollections.length).map
      (fun collectionIndex =>
        materializeCollectionAt
          (relabelValidatedSource source bijection) env
          (relabeledSourceNodeIndex source bijection sourceIndex)
          collectionIndex)
  have collectionsExact :
      relabeledCollections =
        sourceCollections.map (relabelCollection bijection) := by
    simp only [sourceCollections, relabeledCollections]
    rw [collectionIndicesExact]
    rw [List.map_map, List.map_map]
    apply List.map_congr_left
    intro collectionIndex _
    exact materialize_collection_relabel
      source env bijection sourceIndex collectionIndex
  unfold materializeNodeAt
  change
    ({ payload := relabeledNode.payload
       edgeCollections := relabeledCollections } :
      CanonicalNode context.kindSchema) =
      relabelNode bijection
        ({ payload := sourceNode.payload
           edgeCollections := sourceCollections } :
          CanonicalNode context.kindSchema)
  simp only [relabelNode, GraphNode.mk.injEq]
  exact ⟨payloadExact, collectionsExact⟩

theorem materialize_permuted_nodes_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    materializePermutedNodes
        (relabelValidatedSource source bijection) env
        (transportPermutation bijection permutation) =
      materializePermutedNodes source env permutation := by
  let countExact :=
    relabel_raw_block_node_count source.candidate bijection
  have canonicalIndicesExact :
      finiteIndices
          (relabelValidatedSource source bijection).candidate.nodeCount =
        (finiteIndices source.candidate.nodeCount).map
          (Fin.cast countExact.symm) :=
    finite_indices_cast countExact
  let relabeledMaterialize :=
    fun newIndex :
      Fin
        (relabelValidatedSource source
          bijection).candidate.nodeCount =>
      let relabeledBijection :=
        permutationBijection
          (transportPermutation bijection permutation)
      let oldIndex := relabeledBijection.inverse newIndex
      let sourceNodeIndex :
          Fin
            (relabelValidatedSource source
              bijection).candidate.nodes.length :=
        ⟨oldIndex.val, by
          rw [raw_block_nodes_length]
          exact oldIndex.isLt⟩
      normalizeMaterializedNode
        (relabelNode relabeledBijection
          (materializeNodeAt
            (relabelValidatedSource source bijection) env
            sourceNodeIndex))
  let sourceMaterialize :=
    fun newIndex : Fin source.candidate.nodeCount =>
      let sourceBijection := permutationBijection permutation
      let oldIndex := sourceBijection.inverse newIndex
      let sourceNodeIndex : Fin source.candidate.nodes.length :=
        ⟨oldIndex.val, by
          rw [raw_block_nodes_length]
          exact oldIndex.isLt⟩
      normalizeMaterializedNode
        (relabelNode sourceBijection
          (materializeNodeAt source env sourceNodeIndex))
  change
    (finiteIndices
      (relabelValidatedSource source bijection).candidate.nodeCount).map
        relabeledMaterialize =
      (finiteIndices source.candidate.nodeCount).map
        sourceMaterialize
  rw [canonicalIndicesExact]
  calc
    ((finiteIndices source.candidate.nodeCount).map
        (Fin.cast countExact.symm)).map relabeledMaterialize =
      (finiteIndices source.candidate.nodeCount).map
        (fun canonicalIndex =>
          relabeledMaterialize
            (Fin.cast countExact.symm canonicalIndex)) :=
      list_map_map_apply
        (finiteIndices source.candidate.nodeCount)
        (Fin.cast countExact.symm)
        relabeledMaterialize
    _ = (finiteIndices source.candidate.nodeCount).map
        sourceMaterialize := by
      apply List.map_congr_left
      intro canonicalIndex _
      dsimp only [relabeledMaterialize, sourceMaterialize]
      let sourceBijection := permutationBijection permutation
      let relabeledBijection :=
        permutationBijection
          (transportPermutation bijection permutation)
      let sourceIndex := sourceBijection.inverse canonicalIndex
      let relabeledIndex :=
        relabeledBijection.inverse
          (Fin.cast countExact.symm canonicalIndex)
      have relabeledIndexExact :
          relabeledIndex =
            Fin.cast countExact.symm (bijection.forward sourceIndex) := by
        exact transport_permutation_inverse
          bijection permutation canonicalIndex
      have sourceNodeIndexExact :
          (⟨relabeledIndex.val, by
              rw [raw_block_nodes_length]
              exact relabeledIndex.isLt⟩ :
            Fin
              (relabelValidatedSource source
                bijection).candidate.nodes.length) =
            relabeledSourceNodeIndex source bijection sourceIndex := by
        apply Fin.ext
        simpa [relabeledSourceNodeIndex, rawBlockNodeIndex] using
          congrArg Fin.val relabeledIndexExact
      have originalSourceNodeIndexExact :
          (⟨sourceIndex.val, by
              rw [raw_block_nodes_length]
              exact sourceIndex.isLt⟩ :
            Fin source.candidate.nodes.length) =
            rawBlockNodeIndex source.candidate sourceIndex := by
        apply Fin.ext
        rfl
      rw [sourceNodeIndexExact]
      rw [materialize_node_relabel]
      rw [relabel_node_compose_relabeled
        bijection relabeledBijection countExact]
      rw [transport_permutation_composes]
      rw [originalSourceNodeIndexExact]

theorem materialize_candidate_relabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    materializeCandidate
        (relabelValidatedSource source bijection) env
        (transportPermutation bijection permutation) =
      materializeCandidate source env permutation := by
  have nodesExact :=
    materialize_permuted_nodes_relabel
      source env bijection permutation
  let relabeledNodes :=
    materializePermutedNodes
      (relabelValidatedSource source bijection) env
      (transportPermutation bijection permutation)
  let sourceNodes :=
    materializePermutedNodes source env permutation
  have relabeledLength :
      relabeledNodes.length =
        (relabelRawBlock source.candidate bijection).nodeCount :=
    materialize_permuted_nodes_length
      (relabelValidatedSource source bijection) env
      (transportPermutation bijection permutation)
  have relabeledSourceLength :
      relabeledNodes.length = source.candidate.nodeCount :=
    relabeledLength.trans
      (relabel_raw_block_node_count source.candidate bijection)
  have sourceLength :
      sourceNodes.length = source.candidate.nodeCount :=
    materialize_permuted_nodes_length source env permutation
  change
    assembleMaterializedCandidate
        (relabelRawBlock source.candidate bijection)
        relabeledNodes relabeledLength =
      assembleMaterializedCandidate source.candidate
        sourceNodes sourceLength
  calc
    assembleMaterializedCandidate
        (relabelRawBlock source.candidate bijection)
        relabeledNodes relabeledLength =
      assembleMaterializedCandidate source.candidate
        relabeledNodes relabeledSourceLength :=
      assemble_materialized_candidate_relabel
        source.candidate bijection relabeledNodes
        relabeledLength relabeledSourceLength
    _ = assembleMaterializedCandidate source.candidate
        sourceNodes sourceLength :=
      assemble_materialized_candidate_nodes_congr
        source.candidate relabeledNodes sourceNodes
        relabeledSourceLength sourceLength nodesExact

theorem materialize_candidate_commutes_with_source_relabeling
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    materializeCandidate
        (relabelValidatedSource source bijection) env
        (transportPermutation bijection permutation) =
      materializeCandidate source env permutation :=
  materialize_candidate_relabel
    source env bijection permutation

theorem candidate_encoding_equivariant
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    candidateEncoding
        (relabelValidatedSource source bijection) env
        (transportPermutation bijection permutation) =
      candidateEncoding source env permutation :=
  congrArg encodeCanonicalBlock
    (materialize_candidate_relabel
      source env bijection permutation)

def allCandidateBytes
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) :
    List GraphBytes :=
  (permutationWitnesses source.candidate.nodeCount).map
    (candidateEncoding source env)

theorem all_candidate_bytes_nonempty
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) :
    allCandidateBytes source env ≠ [] := by
  intro empty
  cases witnessExact :
      permutationWitnesses source.candidate.nodeCount with
  | nil =>
      exact
        (permutation_witnesses_nonempty source.candidate.nodeCount)
          witnessExact
  | cons head tail =>
      simp [allCandidateBytes, witnessExact] at empty

def minimumCandidateBytes
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) :
    GraphBytes :=
  lexicographicMinimum
    (allCandidateBytes source env)
    (all_candidate_bytes_nonempty source env)

def minimizingPermutations
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) :
    List (PermutationWitness source.candidate.nodeCount) :=
  (permutationWitnesses source.candidate.nodeCount).filter fun permutation =>
    decide
      (candidateEncoding source env permutation =
        minimumCandidateBytes source env)

theorem minimizing_permutation_mem_iff
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    permutation ∈ minimizingPermutations source env ↔
      permutation ∈ permutationWitnesses source.candidate.nodeCount ∧
        candidateEncoding source env permutation =
          minimumCandidateBytes source env := by
  simp [minimizingPermutations]

def graphMinimizerCount
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) : Nat :=
  minimizerCount
    (candidateEncoding source env)
    (permutationWitnesses source.candidate.nodeCount)

theorem minimizer_count_invariant
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount) :
    graphMinimizerCount (relabelValidatedSource source bijection) env =
      graphMinimizerCount source env := by
  let countExact :=
    relabel_raw_block_node_count source.candidate bijection
  let relabeledEncode :
      PermutationWitness source.candidate.nodeCount → GraphBytes :=
    fun permutation =>
      candidateEncoding (relabelValidatedSource source bijection) env
        (countExact.symm ▸ permutation)
  let inverseBijection := inverseLocalBijection bijection
  let candidateBijection :
      CandidateEncodingBijection
        (permutationWitnesses source.candidate.nodeCount)
        (permutationWitnesses source.candidate.nodeCount)
        (candidateEncoding source env)
        relabeledEncode := {
    leftNoDuplicates :=
      permutation_witnesses_no_duplicates _
    rightNoDuplicates :=
      permutation_witnesses_no_duplicates _
    forward :=
      transportPermutationSameCount bijection
    inverse :=
      transportPermutationSameCount inverseBijection
    forwardMember := by
      intro permutation _
      exact permutation_witnesses_complete _
    inverseMember := by
      intro permutation _
      exact permutation_witnesses_complete _
    leftInverse := by
      intro permutation _
      exact transport_permutation_same_count_inverse
        bijection permutation
    rightInverse := by
      intro permutation _
      exact transport_permutation_same_count_forward
        bijection permutation
    encodingPreserved := by
      intro permutation _
      exact candidate_encoding_equivariant
        source env bijection permutation }
  calc
    graphMinimizerCount
        (relabelValidatedSource source bijection) env =
      minimizerCount relabeledEncode
        (permutationWitnesses source.candidate.nodeCount) := by
          unfold graphMinimizerCount
          exact
            minimizer_count_permutation_witness_cast
              countExact
              (candidateEncoding
                (relabelValidatedSource source bijection) env)
    _ = minimizerCount
        (candidateEncoding source env)
        (permutationWitnesses source.candidate.nodeCount) :=
      (minimizer_count_preserved_by_candidate_bijection
        candidateBijection).symm
    _ = graphMinimizerCount source env :=
      rfl

structure SelectedCanonicalLabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (source : ValidatedRawSourceBlock closed) where
  env :
    TargetFinalizationEnv
      closed source.sourceEntry.entry.dependencyRank
  permutation :
    PermutationWitness source.candidate.nodeCount
  selectedCandidateBytes : GraphBytes
  selectedCandidateBytesExact :
    selectedCandidateBytes =
      candidateEncoding source env permutation
  selectedBytesAreMinimum :
    selectedCandidateBytes =
      lexicographicMinimum
        (allCandidateBytes source env)
        (all_candidate_bytes_nonempty source env)
  selectedPermutationUniqueProducer :
    ∀ other,
      candidateEncoding source env other =
          selectedCandidateBytes →
        other = permutation
  canonicalBlock :
    CanonicalBlock
      context.kindSchema source.sourceEntry.kind
  storedEqualsSelectedMaterialization :
    canonicalBlock =
      materializeCandidate source env permutation
  labelMap :
    CanonicalLabelMap source.candidate canonicalBlock

def derivedBlockQ
    (context : GraphCodecContext)
    (kind : context.kindSchema.Kind)
    (block : CanonicalBlock context.kindSchema kind) :
    GraphWireAddress (context.kindSchema.toAddressKind kind) :=
  context.blockWireAddress kind (encodeCanonicalBlock block)

structure FinalizedBlockProvenance
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (raw : SomeRawBlockEntry context.kindSchema) where
  source : ValidatedRawSourceBlock closed
  sourceEntryExact : source.sourceEntry = raw
  selected : SelectedCanonicalLabel closed source
  selectedBlock :
    CanonicalBlock context.kindSchema raw.kind
  selectedBlockExact :
    HEq selectedBlock selected.canonicalBlock
  resolvedBlock :
    CanonicalBlock context.kindSchema raw.kind
  resolvedByAK5 :
    resolveAddressed
        (context.blockBinding raw.kind)
        (ingest.blockRuntimeCodec raw.kind)
        (ingest.blockStore raw.kind)
        raw.entry.claimedBlockQ.toAddress =
      .resolved resolvedBlock
  selectedEqualsResolved :
    selectedBlock = resolvedBlock
  claimedAddressDerived :
    raw.entry.claimedBlockQ =
      derivedBlockQ context raw.kind selectedBlock

def FinalizedBlockProvenance.toFinalizedTarget
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : RawInRegistryRef context.kindSchema}
    {target : RawTargetMember closed.rawGraph raw}
    {sourceRank : Nat}
    (provenance :
      FinalizedBlockProvenance closed
        (Closure.normalizedTypedRegistryEntry
          target.targetEntry))
    (rankLower :
      target.targetEntry.dependencyRank < sourceRank) :
    FinalizedTarget closed raw target sourceRank :=
    { targetRankLower := rankLower
      canonicalBlock := provenance.selectedBlock
      labelMap :=
        transportValidatedSourceCanonicalLabelMap
          provenance.source
          (Closure.normalizedTypedRegistryEntry
            target.targetEntry)
          provenance.sourceEntryExact
          provenance.selected.canonicalBlock
          provenance.selectedBlock
          provenance.selectedBlockExact.symm
          (canonicalLabelMapFromValidatedSource
            provenance.source
            provenance.selected.canonicalBlock
            provenance.selected.labelMap)
      derivedBlockQ :=
        derivedBlockQ context raw.kind provenance.selectedBlock
      derivedBlockQExact :=
        context.blockWireAddressRefines raw.kind
          (encodeCanonicalBlock provenance.selectedBlock)
      claimedAddressAgreement :=
        target.targetEntryMember.keyEq.symm.trans
          provenance.claimedAddressDerived }

def transportFinalizedBlockProvenance
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {left right : SomeRawBlockEntry context.kindSchema}
    (rawExact : left = right)
    (provenance : FinalizedBlockProvenance closed left) :
    FinalizedBlockProvenance closed right := by
  subst right
  exact provenance

structure FinalizedRegistryEntry
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) where
  raw : SomeRawBlockEntry context.kindSchema
  rawMember : raw ∈ closed.rawGraph.blockRegistry
  provenance : FinalizedBlockProvenance closed raw

def findFinalizedTarget
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : RawInRegistryRef context.kindSchema}
    {target : RawTargetMember closed.rawGraph raw}
    {sourceRank : Nat}
    (rankLower :
      target.targetEntry.dependencyRank < sourceRank) :
    List (FinalizedRegistryEntry closed) →
      Option (FinalizedTarget closed raw target sourceRank)
  | [] => none
  | head :: tail =>
      if keyExact :
          Closure.registryEntryKeyIdentity
              context.kindSchema head.raw =
            Closure.rawKeyIdentity context.kindSchema raw.kind
              raw.targetKey then
        let rawExact :
            head.raw =
              Closure.normalizedTypedRegistryEntry
                target.targetEntry :=
          Closure.registry_member_eq_normalized_typed
            closed.uniqueKeys head.raw head.rawMember
            target.targetEntryMember keyExact
        let normalizedProvenance :=
          transportFinalizedBlockProvenance
            rawExact head.provenance
        some
          (normalizedProvenance.toFinalizedTarget rankLower)
      else
        findFinalizedTarget rankLower tail

def FinalizationTableContainsKey
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (table : List (FinalizedRegistryEntry closed))
    (key : Closure.RawKeyIdentity) : Prop :=
  ∃ finalized ∈ table,
    Closure.registryEntryKeyIdentity
      context.kindSchema finalized.raw = key

def findFinalizedProvenance
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (raw : SomeRawBlockEntry context.kindSchema)
    (rawMember : raw ∈ closed.rawGraph.blockRegistry) :
    List (FinalizedRegistryEntry closed) →
      Option (FinalizedBlockProvenance closed raw)
  | [] =>
      none
  | head :: tail =>
      if keyExact :
          Closure.registryEntryKeyIdentity
              context.kindSchema head.raw =
            Closure.registryEntryKeyIdentity
              context.kindSchema raw then
        let rawExact : head.raw = raw :=
          Closure.registry_member_eq_of_key_identity
            closed.uniqueKeys head.raw raw
            head.rawMember rawMember keyExact
        some
          (transportFinalizedBlockProvenance
            rawExact head.provenance)
      else
        findFinalizedProvenance raw rawMember tail

theorem find_finalized_provenance_ne_none_of_contains_key
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (raw : SomeRawBlockEntry context.kindSchema)
    (rawMember : raw ∈ closed.rawGraph.blockRegistry)
    (table : List (FinalizedRegistryEntry closed))
    (contains :
      FinalizationTableContainsKey table
        (Closure.registryEntryKeyIdentity
          context.kindSchema raw)) :
    findFinalizedProvenance raw rawMember table ≠ none := by
  induction table with
  | nil =>
      rcases contains with ⟨finalized, member, keyExact⟩
      simp at member
  | cons head tail ih =>
      unfold findFinalizedProvenance
      split
      · simp
      · rename_i headDifferent
        apply ih
        rcases contains with
          ⟨finalized, member, keyExact⟩
        rcases List.mem_cons.mp member with
          headExact | tailMember
        · subst finalized
          exact False.elim (headDifferent keyExact)
        · exact ⟨finalized, tailMember, keyExact⟩

theorem find_finalized_target_ne_none_of_contains_key
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : RawInRegistryRef context.kindSchema}
    {target : RawTargetMember closed.rawGraph raw}
    {sourceRank : Nat}
    (rankLower :
      target.targetEntry.dependencyRank < sourceRank)
    (table : List (FinalizedRegistryEntry closed))
    (contains :
      FinalizationTableContainsKey table
        (Closure.rawKeyIdentity context.kindSchema raw.kind
          raw.targetKey)) :
    findFinalizedTarget rankLower table ≠ none := by
  induction table with
  | nil =>
      rcases contains with ⟨finalized, member, keyExact⟩
      simp at member
  | cons head tail ih =>
      unfold findFinalizedTarget
      split
      · simp
      · rename_i headDifferent
        apply ih
        rcases contains with
          ⟨finalized, member, keyExact⟩
        rcases List.mem_cons.mp member with
          headExact | tailMember
        · subst finalized
          exact False.elim (headDifferent keyExact)
        · exact ⟨finalized, tailMember, keyExact⟩

def FinalizationTableContainsAllBelow
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (sourceRank : Nat)
    (table : List (FinalizedRegistryEntry closed)) : Prop :=
  ∀ raw,
    raw ∈ closed.rawGraph.blockRegistry →
    raw.entry.dependencyRank < sourceRank →
    FinalizationTableContainsKey table
      (Closure.registryEntryKeyIdentity
        context.kindSchema raw)

def FinalizationTableCoversBelow
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (sourceRank : Nat)
    (table : List (FinalizedRegistryEntry closed)) : Prop :=
  ∀ (raw : RawInRegistryRef context.kindSchema)
    (target : RawTargetMember closed.rawGraph raw)
    (_rawBound : RawTargetMemberBound target)
    (rankLower :
      target.targetEntry.dependencyRank < sourceRank),
    findFinalizedTarget rankLower table ≠ none

theorem finalization_table_covers_below_of_contains_all
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {sourceRank : Nat}
    {table : List (FinalizedRegistryEntry closed)}
    (containsAll :
      FinalizationTableContainsAllBelow
        closed sourceRank table) :
    FinalizationTableCoversBelow closed sourceRank table := by
  intro raw target rawBound rankLower
  let normalized :=
    Closure.normalizedTypedRegistryEntry
      target.targetEntry
  have normalizedMember :
      normalized ∈ closed.rawGraph.blockRegistry :=
    Closure.normalized_typed_registry_entry_mem
      target.targetEntryMember
  have containsNormalized :=
    containsAll normalized normalizedMember rankLower
  have keyExact :
      Closure.registryEntryKeyIdentity
          context.kindSchema normalized =
        Closure.rawKeyIdentity context.kindSchema raw.kind
          raw.targetKey := by
    calc
      Closure.registryEntryKeyIdentity
          context.kindSchema normalized =
          Closure.registryEntryKeyIdentity context.kindSchema
            target.targetEntryMember.wrapped :=
        congrArg
          (Closure.registryEntryKeyIdentity context.kindSchema)
          (Closure.typed_registry_member_wrapped_eq_normalized
            target.targetEntryMember).symm
      _ =
          Closure.rawKeyIdentity context.kindSchema raw.kind
            raw.targetKey :=
        Closure.typed_registry_member_key_identity
          target.targetEntryMember
  rw [keyExact] at containsNormalized
  exact
    find_finalized_target_ne_none_of_contains_key
      rankLower table containsNormalized

def targetFinalizationEnvOfTable
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {sourceRank : Nat}
    (table : List (FinalizedRegistryEntry closed))
    (coverage :
      FinalizationTableCoversBelow closed sourceRank table) :
    TargetFinalizationEnv closed sourceRank where
  lookup := fun raw target rawBound rankLower =>
    match found :
        findFinalizedTarget rankLower table with
    | some finalized =>
        finalized
    | none =>
        False.elim
          (coverage raw target rawBound rankLower found)

def FinalizedBlockProvenance.finalized
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : SomeRawBlockEntry context.kindSchema}
    (provenance : FinalizedBlockProvenance closed raw) :
    SomeCanonicalBlock context :=
  { kind := raw.kind
    blockQ :=
      derivedBlockQ context raw.kind provenance.selectedBlock
    block := provenance.selectedBlock }

theorem finalized_blockQ_derived
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : SomeRawBlockEntry context.kindSchema}
    (provenance : FinalizedBlockProvenance closed raw) :
    provenance.finalized.blockQ =
      derivedBlockQ context raw.kind provenance.selectedBlock :=
  rfl

theorem finalized_blockQ_claimed
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {raw : SomeRawBlockEntry context.kindSchema}
    (provenance : FinalizedBlockProvenance closed raw) :
    provenance.finalized.blockQ = raw.entry.claimedBlockQ :=
  provenance.claimedAddressDerived.symm

structure CanonicalizedRootedRegistry
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) where
  canonicalRegistry : List (SomeCanonicalBlock context)
  canonicalRoot : ExternalRef context.kindSchema
  provenance :
    ∀ raw, raw ∈ closed.rawGraph.blockRegistry →
      FinalizedBlockProvenance closed raw
  registryExactlyFinalized :
    ∀ entry,
      entry ∈ canonicalRegistry ↔
        ∃ raw rawMember,
          entry = (provenance raw rawMember).finalized
  registryKeysNoDup :
    CanonicalRegistryKeysNoDup context canonicalRegistry

theorem graph_wire_address_to_address_injective
    {left right : GraphWireAddress kind}
    (equal : left.toAddress = right.toAddress) :
    left = right := by
  rcases left with
    ⟨⟨leftAlgorithm⟩, ⟨leftDomain⟩,
      ⟨leftSchema⟩, ⟨leftDigest⟩⟩
  rcases right with
    ⟨⟨rightAlgorithm⟩, ⟨rightDomain⟩,
      ⟨rightSchema⟩, ⟨rightDigest⟩⟩
  simp [GraphWireAddress.toAddress, GraphText.value] at equal ⊢
  rcases equal with
    ⟨algorithmExact, domainExact, schemaExact, digestExact⟩
  have stringMkInjective :
      ∀ {left right : List Char},
        String.mk left = String.mk right → left = right := by
    intro left right textExact
    change left.asString = right.asString at textExact
    have listsExact := congrArg String.toList textExact
    simpa [List.asString] using listsExact
  exact
    ⟨stringMkInjective algorithmExact,
      stringMkInjective domainExact,
      stringMkInjective schemaExact,
      stringMkInjective digestExact⟩

theorem claimed_block_address_mismatch_unreachable
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {kind : context.kindSchema.Kind}
    {claimed :
      GraphWireAddress (context.kindSchema.toAddressKind kind)}
    {selectedBlock resolvedBlock :
      CanonicalBlock context.kindSchema kind}
    (resolvedByAK5 :
      resolveAddressed
          (context.blockBinding kind)
          (ingest.blockRuntimeCodec kind)
          (ingest.blockStore kind)
          claimed.toAddress =
        .resolved resolvedBlock)
    (selectedEqualsResolved : selectedBlock = resolvedBlock) :
    claimed =
      context.blockWireAddress kind
        (encodeCanonicalBlock selectedBlock) := by
  rcases
      (resolve_addressed_eq_resolved_iff
        (context.blockBinding kind)
        (ingest.blockRuntimeCodec kind)
        (ingest.blockStore kind)
        claimed.toAddress resolvedBlock).1 resolvedByAK5 with
    ⟨bytes, _found, rehashed, _decoded, reencoded⟩
  have runtimeEncodingExact :
      (ingest.blockRuntimeCodec kind).encode resolvedBlock =
        encodeCanonicalBlock resolvedBlock := by
    exact congrFun
      (ingest.blockRuntimeRefines kind).encode_eq resolvedBlock
  have bytesExact :
      bytes = encodeCanonicalBlock resolvedBlock :=
    reencoded.symm.trans runtimeEncodingExact
  apply graph_wire_address_to_address_injective
  calc
    claimed.toAddress =
        (context.blockBinding kind).address bytes :=
      rehashed.symm
    _ = (context.blockBinding kind).address
        (encodeCanonicalBlock resolvedBlock) :=
      congrArg (context.blockBinding kind).address bytesExact
    _ = (context.blockBinding kind).address
        (encodeCanonicalBlock selectedBlock) := by
      rw [selectedEqualsResolved]
    _ = (context.blockWireAddress kind
        (encodeCanonicalBlock selectedBlock)).toAddress :=
      (context.blockWireAddressRefines kind
        (encodeCanonicalBlock selectedBlock)).symm

inductive GraphCanonicalizationResidue
  | resolvedBlockRegistryMismatch
  | claimedBlockAddressMismatch
  | ambiguousCanonicalLabel
  deriving DecidableEq, Repr

def selectedCanonicalLabelOfUniqueMinimizer
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount)
    (unique :
      minimizingPermutations source env = [permutation]) :
    SelectedCanonicalLabel closed source := by
  have selectedMember :
      permutation ∈ minimizingPermutations source env := by
    rw [unique]
    simp
  have selectedMinimum :
      candidateEncoding source env permutation =
        minimumCandidateBytes source env :=
    (minimizing_permutation_mem_iff source env permutation).mp
      selectedMember |>.2
  exact
    { env := env
      permutation := permutation
      selectedCandidateBytes :=
        candidateEncoding source env permutation
      selectedCandidateBytesExact := rfl
      selectedBytesAreMinimum := selectedMinimum
      selectedPermutationUniqueProducer := by
        intro other otherExact
        have otherMember :
            other ∈ minimizingPermutations source env := by
          apply
            (minimizing_permutation_mem_iff source env other).mpr
          constructor
          · exact permutation_witnesses_complete other
          · exact otherExact.trans selectedMinimum
        rw [unique] at otherMember
        simpa using otherMember
      canonicalBlock :=
        materializeCandidate source env permutation
      storedEqualsSelectedMaterialization := rfl
      labelMap :=
        materializedCanonicalLabelMap source env permutation }

def selectCanonicalLabel
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank) :
    Except GraphCanonicalizationResidue
      (SelectedCanonicalLabel closed source) :=
  match exact : minimizingPermutations source env with
  | [permutation] =>
      .ok
        (selectedCanonicalLabelOfUniqueMinimizer
          source env permutation exact)
  | _ =>
      .error .ambiguousCanonicalLabel

def finalizeRawBlock
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (raw : SomeRawBlockEntry context.kindSchema)
    (rawMember : raw ∈ closed.rawGraph.blockRegistry)
    (env :
      TargetFinalizationEnv
        closed raw.entry.dependencyRank) :
    Except GraphCanonicalizationResidue
      (FinalizedBlockProvenance closed raw) :=
  let source :=
    validatedRawSourceBlockOfMember closed raw rawMember
  match selectCanonicalLabel source env with
  | .error residue =>
      .error residue
  | .ok selected =>
      match resolvedResult :
          resolveAddressed
            (context.blockBinding raw.kind)
            (ingest.blockRuntimeCodec raw.kind)
            (ingest.blockStore raw.kind)
            raw.entry.claimedBlockQ.toAddress with
      | .resolved resolvedBlock =>
          if encodingExact :
              encodeCanonicalBlock selected.canonicalBlock =
                encodeCanonicalBlock resolvedBlock then
            have selectedEqualsResolved :
                selected.canonicalBlock = resolvedBlock :=
              canonical_encode_injective
                (constructiveBlockCodec context.kindSchema raw.kind)
                encodingExact
            .ok
              { source := source
                sourceEntryExact := rfl
                selected := selected
                selectedBlock := selected.canonicalBlock
                selectedBlockExact := HEq.rfl
                resolvedBlock := resolvedBlock
                resolvedByAK5 := resolvedResult
                selectedEqualsResolved := selectedEqualsResolved
                claimedAddressDerived :=
                  claimed_block_address_mismatch_unreachable
                    resolvedResult selectedEqualsResolved }
          else
            .error .resolvedBlockRegistryMismatch
      | _ =>
          .error .resolvedBlockRegistryMismatch

structure FinalizedRankBatch
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (rank : Nat)
    (scope :
      List (SomeRawBlockEntry context.kindSchema)) where
  entries : List (FinalizedRegistryEntry closed)
  complete :
    ∀ raw, raw ∈ scope →
      raw.entry.dependencyRank = rank →
      FinalizationTableContainsKey entries
        (Closure.registryEntryKeyIdentity
          context.kindSchema raw)

def extendFinalizationTable
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {rank : Nat}
    {scope :
      List (SomeRawBlockEntry context.kindSchema)}
    (table : List (FinalizedRegistryEntry closed))
    (batch : FinalizedRankBatch closed rank scope) :
    List (FinalizedRegistryEntry closed) :=
  table ++ batch.entries

theorem extend_finalization_table_contains_all_below_succ
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {rank : Nat}
    {table : List (FinalizedRegistryEntry closed)}
    (containsAll :
      FinalizationTableContainsAllBelow closed rank table)
    (batch :
      FinalizedRankBatch closed rank
        closed.rawGraph.blockRegistry) :
    FinalizationTableContainsAllBelow
      closed rank.succ
      (extendFinalizationTable table batch) := by
  intro raw rawMember rankLower
  rcases (Nat.lt_succ_iff_lt_or_eq.mp rankLower) with
    lower | exactRank
  · rcases containsAll raw rawMember lower with
      ⟨finalized, finalizedMember, keyExact⟩
    exact
      ⟨finalized,
        List.mem_append_left batch.entries finalizedMember,
        keyExact⟩
  · rcases batch.complete raw rawMember exactRank with
      ⟨finalized, finalizedMember, keyExact⟩
    exact
      ⟨finalized,
        List.mem_append_right table finalizedMember,
        keyExact⟩

structure FinalizationAccumulator
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (rank : Nat) where
  table : List (FinalizedRegistryEntry closed)
  containsAll :
    FinalizationTableContainsAllBelow closed rank table

def emptyFinalizationAccumulator
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    FinalizationAccumulator closed 0 where
  table := []
  containsAll := by
    intro raw rawMember rankLower
    exact False.elim (Nat.not_lt_zero _ rankLower)

private def finalizeRawBlocksAtRankAux
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (rank : Nat)
    (env : TargetFinalizationEnv closed rank) :
    (remaining :
      List (SomeRawBlockEntry context.kindSchema)) →
    (∀ raw, raw ∈ remaining →
      raw ∈ closed.rawGraph.blockRegistry) →
    Except GraphCanonicalizationResidue
      (FinalizedRankBatch closed rank remaining)
  | [], _ =>
      .ok
        { entries := []
          complete := by
            intro raw rawMember rankExact
            simp at rawMember }
  | head :: tail, included =>
      let headMember :=
        included head (by simp)
      let tailIncluded :
          ∀ raw, raw ∈ tail →
            raw ∈ closed.rawGraph.blockRegistry :=
        fun raw rawMember =>
          included raw (List.mem_cons_of_mem head rawMember)
      if rankExact :
          head.entry.dependencyRank = rank then
        match
            finalizeRawBlock closed head headMember
              (rankExact.symm ▸ env) with
        | .error residue =>
            .error residue
        | .ok provenance =>
            match
                finalizeRawBlocksAtRankAux
                  closed rank env tail tailIncluded with
            | .error residue =>
                .error residue
            | .ok finalizedTail =>
                let finalizedHead :
                    FinalizedRegistryEntry closed :=
                  { raw := head
                    rawMember := headMember
                    provenance := provenance }
                .ok
                  { entries :=
                      finalizedHead :: finalizedTail.entries
                    complete := by
                      intro raw rawMember rawRank
                      rcases List.mem_cons.mp rawMember with
                        headExact | tailMember
                      · subst raw
                        exact
                          ⟨finalizedHead, by simp,
                            rfl⟩
                      · rcases
                          finalizedTail.complete
                            raw tailMember rawRank with
                          ⟨finalized, finalizedMember,
                            keyExact⟩
                        exact
                          ⟨finalized,
                            List.mem_cons_of_mem
                              finalizedHead finalizedMember,
                            keyExact⟩ }
      else
        match
            finalizeRawBlocksAtRankAux
              closed rank env tail tailIncluded with
        | .error residue =>
            .error residue
        | .ok finalizedTail =>
            .ok
              { entries := finalizedTail.entries
                complete := by
                  intro raw rawMember rawRank
                  rcases List.mem_cons.mp rawMember with
                    headExact | tailMember
                  · subst raw
                    exact False.elim (rankExact rawRank)
                  · exact
                      finalizedTail.complete
                        raw tailMember rawRank }

def finalizeRawBlocksAtRank
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest)
    (rank : Nat)
    (table : List (FinalizedRegistryEntry closed))
    (containsAll :
      FinalizationTableContainsAllBelow closed rank table) :
    Except GraphCanonicalizationResidue
      (FinalizedRankBatch closed rank
        closed.rawGraph.blockRegistry) :=
  finalizeRawBlocksAtRankAux closed rank
    (targetFinalizationEnvOfTable table
      (finalization_table_covers_below_of_contains_all
        containsAll))
    closed.rawGraph.blockRegistry
    (fun _ member => member)

def advanceFinalizationAccumulator
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    {rank : Nat}
    (accumulator : FinalizationAccumulator closed rank) :
    Except GraphCanonicalizationResidue
      (FinalizationAccumulator closed rank.succ) :=
  match
      finalizeRawBlocksAtRank closed rank
        accumulator.table accumulator.containsAll with
  | .error residue =>
      .error residue
  | .ok batch =>
      .ok
        { table :=
            extendFinalizationTable accumulator.table batch
          containsAll :=
            extend_finalization_table_contains_all_below_succ
              accumulator.containsAll batch }

def finalizeRanks
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    (fuel : Nat) →
      Except GraphCanonicalizationResidue
        (FinalizationAccumulator closed fuel)
  | 0 =>
      .ok (emptyFinalizationAccumulator closed)
  | fuel + 1 =>
      match finalizeRanks closed fuel with
      | .error residue =>
          .error residue
      | .ok accumulator =>
          advanceFinalizationAccumulator accumulator

def maximumRegistryDependencyRank :
    List (SomeRawBlockEntry schema) → Nat
  | [] =>
      0
  | head :: tail =>
      Nat.max head.entry.dependencyRank
        (maximumRegistryDependencyRank tail)

theorem registry_dependency_rank_le_maximum
    (raw : SomeRawBlockEntry schema)
    (rawMember : raw ∈ registry) :
    raw.entry.dependencyRank ≤
      maximumRegistryDependencyRank registry := by
  induction registry with
  | nil =>
      simp at rawMember
  | cons head tail ih =>
      rcases List.mem_cons.mp rawMember with
        headExact | tailMember
      · subst raw
        exact
          Nat.le_max_left head.entry.dependencyRank
            (maximumRegistryDependencyRank tail)
      · exact
          Nat.le_trans (ih tailMember)
            (Nat.le_max_right head.entry.dependencyRank
              (maximumRegistryDependencyRank tail))

structure CompleteFinalizationTable
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) where
  table : List (FinalizedRegistryEntry closed)
  complete :
    ∀ raw, raw ∈ closed.rawGraph.blockRegistry →
      FinalizationTableContainsKey table
        (Closure.registryEntryKeyIdentity
          context.kindSchema raw)

def CompleteFinalizationTable.provenanceFor
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed)
    (raw : SomeRawBlockEntry context.kindSchema)
    (rawMember : raw ∈ closed.rawGraph.blockRegistry) :
    FinalizedBlockProvenance closed raw :=
  match found :
      findFinalizedProvenance raw rawMember complete.table with
  | some provenance =>
      provenance
  | none =>
      False.elim
        (find_finalized_provenance_ne_none_of_contains_key
          raw rawMember complete.table
          (complete.complete raw rawMember) found)

def CompleteFinalizationTable.rootProvenance
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    FinalizedBlockProvenance closed
      (Closure.normalizedTypedRegistryEntry
        closed.rootMember.targetEntry) :=
  complete.provenanceFor
    (Closure.normalizedTypedRegistryEntry
      closed.rootMember.targetEntry)
    (Closure.normalized_typed_registry_entry_mem
      closed.rootMember.targetEntryMember)

def CompleteFinalizationTable.rootCanonicalLabelMap
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    CanonicalLabelMap
      closed.rootMember.targetEntry.candidate
      complete.rootProvenance.selectedBlock :=
  transportValidatedSourceCanonicalLabelMap
    complete.rootProvenance.source
    (Closure.normalizedTypedRegistryEntry
      closed.rootMember.targetEntry)
    complete.rootProvenance.sourceEntryExact
    complete.rootProvenance.selected.canonicalBlock
    complete.rootProvenance.selectedBlock
    complete.rootProvenance.selectedBlockExact.symm
    (canonicalLabelMapFromValidatedSource
      complete.rootProvenance.source
      complete.rootProvenance.selected.canonicalBlock
      complete.rootProvenance.selected.labelMap)

def CompleteFinalizationTable.canonicalRoot
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    ExternalRef context.kindSchema :=
  { kind := closed.rawGraph.root.kind
    target :=
      { blockQ := complete.rootProvenance.finalized.blockQ
        canonicalLocalIndex :=
          complete.rootCanonicalLabelMap.forward
            ⟨closed.rawGraph.root.rawTargetMemberIndex,
              closed.rootRawBound⟩ } }

theorem canonical_root_blockQ_claimed
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    complete.canonicalRoot.target.blockQ =
      closed.rawGraph.root.targetKey.claimedBlockQ := by
  exact
    (finalized_blockQ_claimed
      complete.rootProvenance).trans
      closed.rootMember.targetEntryMember.keyEq

def canonicalRegistryFromComplete
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    List (SomeCanonicalBlock context) :=
  closed.rawGraph.blockRegistry.attach.map fun raw =>
    (complete.provenanceFor raw.1 raw.2).finalized

theorem canonical_registry_from_complete_exact
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed)
    (entry : SomeCanonicalBlock context) :
    entry ∈ canonicalRegistryFromComplete complete ↔
      ∃ raw rawMember,
        entry =
          (complete.provenanceFor raw rawMember).finalized := by
  constructor
  · intro entryMember
    rcases List.mem_map.mp entryMember with
      ⟨raw, rawMember, entryExact⟩
    exact
      ⟨raw.1, raw.2, entryExact.symm⟩
  · rintro ⟨raw, rawMember, entryExact⟩
    apply List.mem_map.mpr
    exact
      ⟨⟨raw, rawMember⟩,
        List.mem_attach
          closed.rawGraph.blockRegistry
          ⟨raw, rawMember⟩,
        entryExact.symm⟩

theorem finalized_registry_key_encoding_eq_raw
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed)
    (raw : SomeRawBlockEntry context.kindSchema)
    (rawMember : raw ∈ closed.rawGraph.blockRegistry) :
    encodeCanonicalRegistryKey context
        (complete.provenanceFor raw rawMember).finalized.key =
      encodeRawKeyIdentity
        (Closure.registryEntryKeyIdentity
          context.kindSchema raw) := by
  have blockQExact :=
    (complete.provenanceFor raw rawMember).claimedAddressDerived
  simp only [
    encodeCanonicalRegistryKey, SomeCanonicalBlock.key,
    FinalizedBlockProvenance.finalized,
    encodeRawKeyIdentity, Closure.registryEntryKeyIdentity,
    Closure.rawKeyIdentity
  ]
  rw [← blockQExact]

theorem canonical_registry_encoded_keys_eq_raw
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    (canonicalRegistryFromComplete complete).map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) =
      closed.rawGraph.blockRegistry.map
        (fun raw =>
          encodeRawKeyIdentity
            (Closure.registryEntryKeyIdentity
              context.kindSchema raw)) := by
  unfold canonicalRegistryFromComplete
  have attachAsPmap :
      closed.rawGraph.blockRegistry.attach.map
          (fun raw =>
            (complete.provenanceFor raw.1 raw.2).finalized) =
        List.pmap
          (fun raw rawMember =>
            (complete.provenanceFor raw rawMember).finalized)
          closed.rawGraph.blockRegistry
          (fun _ rawMember => rawMember) := by
    exact
      (List.pmap_eq_map_attach
        (f := fun raw rawMember =>
          (complete.provenanceFor raw rawMember).finalized)
        (l := closed.rawGraph.blockRegistry)
        (fun _ rawMember => rawMember)).symm
  rw [attachAsPmap]
  rw [List.map_pmap
    (g := fun (entry : SomeCanonicalBlock context) =>
      encodeCanonicalRegistryKey context entry.key)]
  have dependentFunctionExact :
      (fun raw
          (rawMember :
            raw ∈ closed.rawGraph.blockRegistry) =>
        encodeCanonicalRegistryKey context
          (complete.provenanceFor raw rawMember).finalized.key) =
        (fun raw
          (_rawMember :
            raw ∈ closed.rawGraph.blockRegistry) =>
          encodeRawKeyIdentity
            (Closure.registryEntryKeyIdentity
              context.kindSchema raw)) := by
    funext raw rawMember
    exact
      finalized_registry_key_encoding_eq_raw
        complete raw rawMember
  rw [dependentFunctionExact]
  calc
    List.pmap
        (fun raw
          (_rawMember :
            raw ∈ closed.rawGraph.blockRegistry) =>
          encodeRawKeyIdentity
            (Closure.registryEntryKeyIdentity
              context.kindSchema raw))
        closed.rawGraph.blockRegistry _ =
      closed.rawGraph.blockRegistry.map
        (fun raw =>
          encodeRawKeyIdentity
            (Closure.registryEntryKeyIdentity
              context.kindSchema raw)) :=
        List.pmap_eq_map
          (p := fun raw =>
            raw ∈ closed.rawGraph.blockRegistry)
          (f := fun raw =>
            encodeRawKeyIdentity
              (Closure.registryEntryKeyIdentity
                context.kindSchema raw))
          (l := closed.rawGraph.blockRegistry)
          (fun _ rawMember => rawMember)

theorem canonical_registry_from_complete_keys_no_dup
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    CanonicalRegistryKeysNoDup context
      (canonicalRegistryFromComplete complete) := by
  rw [
    CanonicalRegistryKeysNoDup,
    canonical_registry_encoded_keys_eq_raw
  ]
  have rawKeyNoDup :=
    Closure.registry_keys_unique_no_duplicates
      closed.uniqueKeys
  change
    (closed.rawGraph.blockRegistry.map
      (fun raw =>
        encodeRawKeyIdentity
          (Closure.registryEntryKeyIdentity
            context.kindSchema raw))).Nodup
  have encodedNoDup :
      ((closed.rawGraph.blockRegistry.map
        (Closure.registryEntryKeyIdentity
          context.kindSchema)).map encodeRawKeyIdentity).Nodup :=
    List.Pairwise.map encodeRawKeyIdentity (by
        intro left right different encodedExact
        exact
          different
            (encode_raw_key_identity_injective encodedExact))
      rawKeyNoDup
  simpa [List.map_map] using encodedNoDup

def canonicalizedRootedRegistryFromComplete
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {closed : StructurallyClosedRootedGraph context ingest}
    (complete : CompleteFinalizationTable closed) :
    CanonicalizedRootedRegistry closed where
  canonicalRegistry :=
    canonicalRegistryFromComplete complete
  canonicalRoot :=
    complete.canonicalRoot
  provenance :=
    complete.provenanceFor
  registryExactlyFinalized :=
    canonical_registry_from_complete_exact complete
  registryKeysNoDup :=
    canonical_registry_from_complete_keys_no_dup complete

def finalizeAllRawBlocks
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    Except GraphCanonicalizationResidue
      (CompleteFinalizationTable closed) :=
  let maximumRank :=
    maximumRegistryDependencyRank
      closed.rawGraph.blockRegistry
  match finalizeRanks closed maximumRank.succ with
  | .error residue =>
      .error residue
  | .ok accumulator =>
      .ok
        { table := accumulator.table
          complete := by
            intro raw rawMember
            apply accumulator.containsAll raw rawMember
            exact
              Nat.lt_succ_of_le
                (registry_dependency_rank_le_maximum
                  raw rawMember) }

def canonicalizeStructurallyClosed
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    (closed : StructurallyClosedRootedGraph context ingest) :
    Except GraphCanonicalizationResidue
      (CanonicalizedRootedRegistry closed) :=
  match finalizeAllRawBlocks closed with
  | .error residue =>
      .error residue
  | .ok complete =>
      .ok (canonicalizedRootedRegistryFromComplete complete)

end Residua.RCC.Addressing.AddressedGraph


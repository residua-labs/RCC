import RCC.AddressedGraphFoundation

/-!
# RCC addressed-graph local connectivity

This module computes address-free local paths and strong-connectivity
certificates for finite graph blocks.  Only node positions, local reference
occurrences, and edge direction affect incidence.
-/

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressedGraph.Closure

variable {schema : GraphKindSchema} {External : Type}

def EveryConsecutivePair
    (vertices : List Nat) (edge : Nat → Nat → Prop) : Prop :=
  match vertices with
  | [] => True
  | [_] => True
  | first :: second :: rest =>
      edge first second ∧
      EveryConsecutivePair (second :: rest) edge

private def hasLocalTarget
    (targets : List (GraphRef External)) (target : Nat) : Bool :=
  targets.any fun reference =>
    match reference with
    | .local index => decide (index = target)
    | .external _ => false

private def ownsLocalOccurrence
    (nodes : List (GraphNode schema External))
    (owner : Nat) (direction : EdgeDirection) (target : Nat) : Bool :=
  match nodes[owner]? with
  | none => false
  | some node =>
      node.edgeCollections.any fun collection =>
        decide (collection.direction = direction) &&
          hasLocalTarget collection.targets target

private def localEdgeBool
    (nodes : List (GraphNode schema External))
    (source target : Nat) : Bool :=
  decide (source < nodes.length) &&
    decide (target < nodes.length) &&
    (ownsLocalOccurrence nodes source .outgoing target ||
      ownsLocalOccurrence nodes target .incoming source)

/-
Both endpoints are required to denote nodes in this block.  Without these
bounds, an outgoing reference to an out-of-range selector followed by an
incoming occurrence of that selector can manufacture a path through a vertex
that no bounded witness can enumerate.
-/
def LocalEdge
    (nodes : List (GraphNode schema External))
    (source target : Nat) : Prop :=
  localEdgeBool nodes source target = true

/-!
`LocalEdgeCriterion` exposes the incidence semantics needed by later
source-local relabeling proofs without making the executable helpers part of
the public API.  The criterion is definitionally equal to `LocalEdge`.
-/

def HasLocalTarget
    (targets : List (GraphRef External)) (target : Nat) : Bool :=
  targets.any fun reference =>
    match reference with
    | .local index => decide (index = target)
    | .external _ => false

def OwnsLocalOccurrence
    (nodes : List (GraphNode schema External))
    (owner : Nat) (direction : EdgeDirection) (target : Nat) : Bool :=
  match nodes[owner]? with
  | none => false
  | some node =>
      node.edgeCollections.any fun collection =>
        decide (collection.direction = direction) &&
          HasLocalTarget collection.targets target

def LocalEdgeCriterion
    (nodes : List (GraphNode schema External))
    (source target : Nat) : Bool :=
  decide (source < nodes.length) &&
    decide (target < nodes.length) &&
    (OwnsLocalOccurrence nodes source .outgoing target ||
      OwnsLocalOccurrence nodes target .incoming source)

theorem local_edge_iff_criterion
    (nodes : List (GraphNode schema External))
    (source target : Nat) :
    LocalEdge nodes source target ↔
      LocalEdgeCriterion nodes source target = true := by
  rfl

private theorem local_edge_source_bounded
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (edge : LocalEdge nodes source target) :
    source < nodes.length := by
  simp only [LocalEdge, localEdgeBool, Bool.and_eq_true] at edge
  exact of_decide_eq_true edge.1.1

private theorem local_edge_target_bounded
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (edge : LocalEdge nodes source target) :
    target < nodes.length := by
  simp only [LocalEdge, localEdgeBool, Bool.and_eq_true] at edge
  exact of_decide_eq_true edge.1.2

theorem local_edge_source_lt
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (edge : LocalEdge nodes source target) :
    source < nodes.length :=
  local_edge_source_bounded edge

theorem local_edge_target_lt
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (edge : LocalEdge nodes source target) :
    target < nodes.length :=
  local_edge_target_bounded edge

inductive LocalPath
    (nodes : List (GraphNode schema External)) : Nat → Nat → Prop
  | refl {node} :
      node < nodes.length → LocalPath nodes node node
  | step {first second last} :
      LocalEdge nodes first second →
      LocalPath nodes second last →
      LocalPath nodes first last

def StronglyConnected
    (nodes : List (GraphNode schema External)) : Prop :=
  nodes ≠ [] ∧
    ∀ source target,
      source < nodes.length →
      target < nodes.length →
      LocalPath nodes source target

structure ConnectivityCertificate
    (nodes : List (GraphNode schema External)) : Type where
  stronglyConnected : StronglyConnected nodes

structure LocalPathWitness
    (nodes : List (GraphNode schema External))
    (source target : Nat) where
  vertices : List Nat
  startsAt : vertices.head? = some source
  endsAt : vertices.getLast? = some target
  allBounded : ∀ member ∈ vertices, member < nodes.length
  consecutiveEdges :
    EveryConsecutivePair vertices (LocalEdge nodes)

private def vertexListsOfLength (nodeCount : Nat) :
    Nat → List (List Nat)
  | 0 => [[]]
  | length + 1 =>
      (List.range nodeCount).flatMap fun vertex =>
        (vertexListsOfLength nodeCount length).map fun tail =>
          vertex :: tail

def boundedVertexLists (nodeCount pathLength : Nat) :
    List (List Nat) :=
  (List.range pathLength).flatMap fun priorLength =>
    vertexListsOfLength nodeCount (priorLength + 1)

private theorem vertex_lists_of_length_complete
    (values : List Nat)
    (bounded : ∀ value ∈ values, value < nodeCount) :
    values ∈ vertexListsOfLength nodeCount values.length := by
  induction values with
  | nil =>
      simp [vertexListsOfLength]
  | cons head tail inductionHypothesis =>
      simp only [List.length_cons, vertexListsOfLength, List.mem_flatMap,
        List.mem_range, List.mem_map]
      refine ⟨head, bounded head (by simp), tail, ?_, rfl⟩
      exact inductionHypothesis fun value member =>
        bounded value (List.mem_cons_of_mem head member)

private theorem bounded_vertex_lists_complete
    (values : List Nat)
    (nonempty : values ≠ [])
    (lengthBound : values.length ≤ pathLength)
    (bounded : ∀ value ∈ values, value < nodeCount) :
    values ∈ boundedVertexLists nodeCount pathLength := by
  cases values with
  | nil =>
      contradiction
  | cons head tail =>
      simp only [boundedVertexLists, List.mem_flatMap, List.mem_range]
      refine ⟨tail.length, by simpa using lengthBound, ?_⟩
      exact vertex_lists_of_length_complete (head :: tail) bounded

private theorem filter_sublist_local
    (predicate : Nat → Bool) :
    ∀ values : List Nat,
      (values.filter predicate).Sublist values
  | [] => .refl []
  | head :: tail => by
      have inductionHypothesis :=
        filter_sublist_local predicate tail
      cases selected : predicate head with
      | false =>
          simp only [List.filter, selected]
          exact .cons head inductionHypothesis
      | true =>
          simp only [List.filter, selected]
          exact .cons₂ head inductionHypothesis

private theorem length_le_filter_succ
    (values : List Nat) (bound : Nat)
    (nodup : values.Nodup)
    (bounded : ∀ value, value ∈ values → value < bound + 1) :
    values.length ≤
      (values.filter fun value => decide (value < bound)).length + 1 := by
  induction values with
  | nil =>
      simp
  | cons head tail inductionHypothesis =>
      have split := List.nodup_cons.mp nodup
      have headBound : head < bound + 1 :=
        bounded head (by simp)
      by_cases headLower : head < bound
      · have tailBounded :
            ∀ value, value ∈ tail → value < bound + 1 := by
          intro value member
          exact bounded value (by simp [member])
        have tailLength :=
          inductionHypothesis split.2 tailBounded
        simp [headLower]
        omega
      · have headEqual : head = bound := by omega
        have tailLower : ∀ value, value ∈ tail → value < bound := by
          intro value member
          have valueBound : value < bound + 1 :=
            bounded value (by simp [member])
          have valueNotHead : value ≠ head := by
            intro equal
            apply split.1
            simpa [equal] using member
          omega
        have tailFilter :
            tail.filter (fun value => decide (value < bound)) = tail :=
          List.filter_eq_self.mpr fun value member =>
            decide_eq_true (tailLower value member)
        simp [headLower, tailFilter]

private theorem nodup_bounded_length_le
    {values : List Nat} {bound : Nat}
    (nodup : values.Nodup)
    (bounded : ∀ value, value ∈ values → value < bound) :
    values.length ≤ bound := by
  induction bound generalizing values with
  | zero =>
      cases values with
      | nil => simp
      | cons head tail =>
          have impossible := bounded head (by simp)
          omega
  | succ prior inductionHypothesis =>
      let lower :=
        values.filter fun value => decide (value < prior)
      have lowerSublist : lower.Sublist values := by
        exact filter_sublist_local _ values
      have lowerNodup : lower.Nodup :=
        lowerSublist.nodup nodup
      have lowerBounded :
          ∀ value, value ∈ lower → value < prior := by
        intro value member
        exact of_decide_eq_true (List.mem_filter.mp member).2
      have lowerLength : lower.length ≤ prior :=
        inductionHypothesis lowerNodup lowerBounded
      have originalLength :
          values.length ≤ lower.length + 1 := by
        exact length_le_filter_succ values prior nodup (by
          intro value member
          simpa using bounded value member)
      omega

private def consecutiveLocalEdges
    (nodes : List (GraphNode schema External)) : List Nat → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      localEdgeBool nodes first second &&
        consecutiveLocalEdges nodes (second :: rest)

private theorem consecutive_local_edges_sound
    {nodes : List (GraphNode schema External)}
    {vertices : List Nat}
    (accepted : consecutiveLocalEdges nodes vertices = true) :
    EveryConsecutivePair vertices (LocalEdge nodes) := by
  induction vertices with
  | nil =>
      trivial
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          trivial
      | cons second tail =>
          simp only [consecutiveLocalEdges, Bool.and_eq_true] at accepted
          simp only [EveryConsecutivePair]
          exact ⟨accepted.1, inductionHypothesis accepted.2⟩

private theorem consecutive_local_edges_complete
    {nodes : List (GraphNode schema External)}
    {vertices : List Nat}
    (pairs : EveryConsecutivePair vertices (LocalEdge nodes)) :
    consecutiveLocalEdges nodes vertices = true := by
  induction vertices with
  | nil =>
      rfl
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          rfl
      | cons second tail =>
          simp only [EveryConsecutivePair] at pairs
          simp only [consecutiveLocalEdges, Bool.and_eq_true]
          exact ⟨pairs.1, inductionHypothesis pairs.2⟩

private def checkedPathWitness
    (nodes : List (GraphNode schema External))
    (source target : Nat) (vertices : List Nat) :
    Option (LocalPathWitness nodes source target) :=
  if startsAt : vertices.head? = some source then
    if endsAt : vertices.getLast? = some target then
      if bounded :
          vertices.all (fun member => decide (member < nodes.length)) = true then
        if consecutive :
            consecutiveLocalEdges nodes vertices = true then
          some
            { vertices
              startsAt
              endsAt
              allBounded := by
                intro member memberIn
                exact of_decide_eq_true
                  ((List.all_eq_true.mp bounded) member memberIn)
              consecutiveEdges :=
                consecutive_local_edges_sound consecutive }
        else none
      else none
    else none
  else none

private def firstCheckedPath
    (nodes : List (GraphNode schema External))
    (source target : Nat) :
    List (List Nat) → Option (LocalPathWitness nodes source target)
  | [] => none
  | vertices :: rest =>
      match checkedPathWitness nodes source target vertices with
      | some witness => some witness
      | none => firstCheckedPath nodes source target rest

private theorem checked_path_witness_complete
    {nodes : List (GraphNode schema External)}
    {source target : Nat} {vertices : List Nat}
    (startsAt : vertices.head? = some source)
    (endsAt : vertices.getLast? = some target)
    (bounded : ∀ member ∈ vertices, member < nodes.length)
    (pairs : EveryConsecutivePair vertices (LocalEdge nodes)) :
    ∃ witness,
      checkedPathWitness nodes source target vertices = some witness := by
  have boundedCheck :
      vertices.all
          (fun member => decide (member < nodes.length)) =
        true :=
    List.all_eq_true.mpr fun member membership =>
      decide_eq_true (bounded member membership)
  have consecutiveCheck :
      consecutiveLocalEdges nodes vertices = true :=
    consecutive_local_edges_complete pairs
  unfold checkedPathWitness
  rw [dif_pos startsAt, dif_pos endsAt, dif_pos boundedCheck,
    dif_pos consecutiveCheck]
  exact ⟨_, rfl⟩

private theorem first_checked_path_complete
    {nodes : List (GraphNode schema External)}
    {source target : Nat} {vertices : List Nat}
    {candidates : List (List Nat)}
    (member : vertices ∈ candidates)
    (accepted :
      ∃ witness,
        checkedPathWitness nodes source target vertices = some witness) :
    ∃ witness,
      firstCheckedPath nodes source target candidates = some witness := by
  induction candidates with
  | nil =>
      simp at member
  | cons candidate rest inductionHypothesis =>
      simp only [List.mem_cons] at member
      rcases member with equal | inRest
      · cases equal
        obtain ⟨witness, checked⟩ := accepted
        exact ⟨witness, by simp [firstCheckedPath, checked]⟩
      · cases checked :
          checkedPathWitness nodes source target candidate with
        | none =>
            obtain ⟨witness, found⟩ :=
              inductionHypothesis inRest
            exact ⟨witness, by simp [firstCheckedPath, checked, found]⟩
        | some witness =>
            exact ⟨witness, by simp [firstCheckedPath, checked]⟩

def findLocalPath
    (nodes : List (GraphNode schema External))
    (source target : Nat) :
    Option (LocalPathWitness nodes source target) :=
  firstCheckedPath nodes source target
    (boundedVertexLists nodes.length nodes.length)

private theorem local_path_of_vertices
    {nodes : List (GraphNode schema External)}
    {vertices : List Nat} {source target : Nat}
    (starts : vertices.head? = some source)
    (ends : vertices.getLast? = some target)
    (bounded : ∀ member ∈ vertices, member < nodes.length)
    (edges : EveryConsecutivePair vertices (LocalEdge nodes)) :
    LocalPath nodes source target := by
  induction vertices generalizing source with
  | nil =>
      simp at starts
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil =>
          simp only [List.head?_cons, Option.some.injEq] at starts
          simp only [List.getLast?_singleton, Option.some.injEq] at ends
          cases starts
          cases ends
          exact LocalPath.refl (bounded target (by simp))
      | cons second tail =>
          simp only [List.head?_cons, Option.some.injEq] at starts
          cases starts
          simp only [EveryConsecutivePair] at edges
          exact
            LocalPath.step edges.1
              (inductionHypothesis rfl ends
                (fun member memberIn =>
                  bounded member (List.mem_cons_of_mem first memberIn))
                edges.2)

theorem witness_to_local_path
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (witness : LocalPathWitness nodes source target) :
    LocalPath nodes source target :=
  local_path_of_vertices witness.startsAt witness.endsAt
    witness.allBounded witness.consecutiveEdges

private theorem first_checked_path_sound
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    {candidates : List (List Nat)}
    {witness : LocalPathWitness nodes source target}
    (found : firstCheckedPath nodes source target candidates = some witness) :
    LocalPath nodes source target := by
  induction candidates with
  | nil =>
      simp [firstCheckedPath] at found
  | cons vertices rest inductionHypothesis =>
      simp only [firstCheckedPath] at found
      cases checked : checkedPathWitness nodes source target vertices with
      | none =>
          rw [checked] at found
          exact inductionHypothesis found
      | some checkedWitness =>
          rw [checked] at found
          cases found
          exact witness_to_local_path witness

theorem find_local_path_sound
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    {witness : LocalPathWitness nodes source target}
    (found : findLocalPath nodes source target = some witness) :
    LocalPath nodes source target :=
  first_checked_path_sound found

private theorem every_consecutive_pair_tail
    {vertices : List Nat} {edge : Nat → Nat → Prop} {first : Nat}
    (pairs : EveryConsecutivePair (first :: vertices) edge) :
    EveryConsecutivePair vertices edge := by
  cases vertices with
  | nil =>
      trivial
  | cons second rest =>
      exact pairs.2

private theorem every_consecutive_pair_suffix
    {pre suffix : List Nat} {edge : Nat → Nat → Prop}
    (pairs : EveryConsecutivePair (pre ++ suffix) edge) :
    EveryConsecutivePair suffix edge := by
  induction pre with
  | nil =>
      exact pairs
  | cons first rest inductionHypothesis =>
      exact inductionHypothesis (every_consecutive_pair_tail pairs)

private theorem local_path_has_simple_vertices
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (path : LocalPath nodes source target) :
    ∃ vertices : List Nat,
      vertices.head? = some source ∧
      vertices.getLast? = some target ∧
      (∀ member, member ∈ vertices → member < nodes.length) ∧
      EveryConsecutivePair vertices (LocalEdge nodes) ∧
      vertices.Nodup := by
  induction path with
  | refl bounded =>
      exact ⟨[_], rfl, rfl, by simpa, by trivial, by simp⟩
  | @step first second last edge tail inductionHypothesis =>
      obtain
        ⟨vertices, startsAt, endsAt, allBounded, consecutive, nodup⟩ :=
          inductionHypothesis
      by_cases occurs : first ∈ vertices
      · obtain ⟨pre, suffix, decomposition⟩ :=
          List.append_of_mem occurs
        refine ⟨first :: suffix, rfl, ?_, ?_, ?_, ?_⟩
        · rw [decomposition] at endsAt
          simpa using endsAt
        · intro vertex vertexMember
          apply allBounded vertex
          rw [decomposition]
          simp only [List.mem_append, List.mem_cons]
          exact .inr (List.mem_cons.mp vertexMember)
        · apply every_consecutive_pair_suffix (pre := pre)
          simpa [decomposition] using consecutive
        · have suffixSublist :
              (first :: suffix).Sublist
                (pre ++ first :: suffix) :=
            List.sublist_append_right pre (first :: suffix)
          rw [decomposition] at nodup
          exact suffixSublist.nodup nodup
      · obtain ⟨rest, verticesShape⟩ :=
          List.head?_eq_some_iff.mp startsAt
        subst vertices
        refine ⟨first :: second :: rest, rfl, ?_, ?_, ?_, ?_⟩
        · simpa using endsAt
        · intro vertex vertexMember
          simp only [List.mem_cons] at vertexMember
          rcases vertexMember with rfl | vertexMember
          · exact local_edge_source_bounded edge
          · exact allBounded vertex (List.mem_cons.mpr vertexMember)
        · exact ⟨edge, consecutive⟩
        · exact List.nodup_cons.mpr ⟨occurs, nodup⟩

theorem find_local_path_complete
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (path : LocalPath nodes source target) :
    ∃ witness, findLocalPath nodes source target = some witness := by
  obtain
    ⟨vertices, startsAt, endsAt, allBounded, consecutive, nodup⟩ :=
      local_path_has_simple_vertices path
  have nonempty : vertices ≠ [] := by
    intro empty
    rw [empty] at startsAt
    simp at startsAt
  have lengthBound : vertices.length ≤ nodes.length :=
    nodup_bounded_length_le nodup allBounded
  have candidateMember :
      vertices ∈ boundedVertexLists nodes.length nodes.length :=
    bounded_vertex_lists_complete vertices nonempty lengthBound allBounded
  have accepted :
      ∃ witness,
        checkedPathWitness nodes source target vertices = some witness :=
    checked_path_witness_complete startsAt endsAt allBounded consecutive
  exact first_checked_path_complete candidateMember accepted

theorem find_local_path_none_iff
    {nodes : List (GraphNode schema External)}
    {source target : Nat} :
    findLocalPath nodes source target = none ↔
      ¬ LocalPath nodes source target := by
  constructor
  · intro none path
    obtain ⟨witness, found⟩ := find_local_path_complete path
    rw [none] at found
    contradiction
  · intro noPath
    cases found : findLocalPath nodes source target with
    | none =>
        rfl
    | some witness =>
        exact False.elim (noPath (find_local_path_sound found))

private def pairOrder (nodeCount : Nat) : List (Nat × Nat) :=
  (List.range nodeCount).flatMap fun source =>
    (List.range nodeCount).map fun target => (source, target)

private def firstMissingPair
    (nodes : List (GraphNode schema External)) :
    List (Nat × Nat) → Option (Nat × Nat)
  | [] => none
  | pair :: rest =>
      match findLocalPath nodes pair.1 pair.2 with
      | none => some pair
      | some _ => firstMissingPair nodes rest

private theorem first_missing_pair_none_find
    {nodes : List (GraphNode schema External)}
    {pairs : List (Nat × Nat)} {source target : Nat}
    (noneMissing : firstMissingPair nodes pairs = none)
    (member : (source, target) ∈ pairs) :
    ∃ witness, findLocalPath nodes source target = some witness := by
  induction pairs with
  | nil =>
      simp at member
  | cons pair rest inductionHypothesis =>
      simp only [firstMissingPair] at noneMissing
      cases found : findLocalPath nodes pair.1 pair.2 with
      | none =>
          simp [found] at noneMissing
      | some witness =>
          simp only [found] at noneMissing
          simp only [List.mem_cons] at member
          rcases member with equal | inRest
          · cases equal
            exact ⟨witness, found⟩
          · exact inductionHypothesis noneMissing inRest

private theorem first_missing_pair_none_of_complete
    {nodes : List (GraphNode schema External)}
    {pairs : List (Nat × Nat)}
    (complete :
      ∀ source target,
        (source, target) ∈ pairs →
        ∃ witness, findLocalPath nodes source target = some witness) :
    firstMissingPair nodes pairs = none := by
  induction pairs with
  | nil =>
      rfl
  | cons pair rest inductionHypothesis =>
      obtain ⟨witness, found⟩ :=
        complete pair.1 pair.2 (by simp)
      simp only [firstMissingPair, found]
      apply inductionHypothesis
      intro source target member
      exact complete source target (by simp [member])

inductive LocalConnectivityResidue
  | emptyBlock
  | noPath (source target : Nat)
  deriving DecidableEq, Repr

private theorem strongly_connected_of_no_missing
    {nodes : List (GraphNode schema External)}
    (nonempty : nodes ≠ [])
    (noneMissing :
      firstMissingPair nodes (pairOrder nodes.length) = none) :
    StronglyConnected nodes := by
  refine ⟨nonempty, ?_⟩
  intro source target sourceBound targetBound
  have member :
      (source, target) ∈ pairOrder nodes.length := by
    simp [pairOrder]
    exact ⟨sourceBound, targetBound⟩
  obtain ⟨witness, found⟩ :=
    first_missing_pair_none_find noneMissing member
  exact find_local_path_sound found

private def missingPairResidue
    (missing : Option (Nat × Nat))
    (notNone : missing ≠ none) :
    LocalConnectivityResidue :=
  match missing with
  | some pair => .noPath pair.1 pair.2
  | none => False.elim (notNone rfl)

def buildConnectivityCertificate
    (nodes : List (GraphNode schema External)) :
    Except LocalConnectivityResidue (ConnectivityCertificate nodes) :=
  match nodes with
  | [] => .error .emptyBlock
  | first :: rest =>
      let missing :=
        firstMissingPair (first :: rest)
          (pairOrder (first :: rest).length)
      if noneMissing : missing = none then
        .ok
          { stronglyConnected :=
              strongly_connected_of_no_missing (by simp) noneMissing }
      else
        .error (missingPairResidue missing noneMissing)

theorem build_connectivity_sound
    {nodes : List (GraphNode schema External)}
    {certificate : ConnectivityCertificate nodes}
    (_built : buildConnectivityCertificate nodes = .ok certificate) :
    StronglyConnected nodes :=
  certificate.stronglyConnected

theorem build_connectivity_complete
    {nodes : List (GraphNode schema External)}
    (connected : StronglyConnected nodes) :
    ∃ certificate,
      buildConnectivityCertificate nodes = .ok certificate := by
  cases nodes with
  | nil =>
      exact False.elim (connected.1 rfl)
  | cons first rest =>
      have noMissing :
          firstMissingPair (first :: rest)
              (pairOrder (rest.length + 1)) =
            none := by
        apply first_missing_pair_none_of_complete
        intro source target member
        have bounds :
            source < (first :: rest).length ∧
              target < (first :: rest).length := by
          simpa [pairOrder] using member
        exact find_local_path_complete
          (connected.2 source target bounds.1 bounds.2)
      have noMissingOriginal :
          firstMissingPair (first :: rest)
              (pairOrder (first :: rest).length) =
            none := by
        simpa using noMissing
      refine ⟨{ stronglyConnected := connected }, ?_⟩
      simp [buildConnectivityCertificate, noMissing]

theorem build_connectivity_refuses_iff
    {nodes : List (GraphNode schema External)} :
    (∃ residue,
      buildConnectivityCertificate nodes = .error residue) ↔
      ¬ StronglyConnected nodes := by
  constructor
  · rintro ⟨residue, refused⟩ connected
    obtain ⟨certificate, accepted⟩ :=
      build_connectivity_complete connected
    rw [refused] at accepted
    contradiction
  · intro notConnected
    cases built : buildConnectivityCertificate nodes with
    | error residue =>
        exact ⟨residue, rfl⟩
    | ok certificate =>
        exact False.elim
          (notConnected (build_connectivity_sound built))

end Residua.RCC.Addressing.AddressedGraph.Closure


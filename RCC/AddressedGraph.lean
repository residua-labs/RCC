import RCC.AddressedGraphCodec

/-!
# RCC addressed-graph quotient and root address

This module constructs the quotient-level graph codec and root address only
after the closed graph's canonical observation has been fixed explicitly.
-/

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph.Foundation
open Residua.RCC.Addressing.AddressedGraph.Closure

namespace Residua.RCC.Addressing.AddressedGraph

/-- The exact finite observation retained by the addressed-graph quotient. -/
def canonicalGraph
    (graph : ClosedRootedGraph context) :
    CanonicalRootedGraph context :=
  serializedCanonicalProjection graph

/--
The implementation-address domain identifies closed rooted graphs by concrete
graph isomorphism and observes their fully serialized canonical projection.
-/
def closedRootedGraphDomain
    (context : GraphCodecContext) :
    IdentityDomain .implementation where
  Object := ClosedRootedGraph context
  Context := Unit
  Observation := CanonicalRootedGraph context
  equivalent := fun _ left right => GraphIsomorphic left right
  observe := fun _ graph => canonicalGraph graph

/-- The typed root address commits to the complete canonical graph envelope. -/
def rootAddress
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context) :
    Address .implementation :=
  context.rootBinding.address (encodeCanonicalGraph context graph)

/--
A registry entry is determined by its typed key and exact canonical block
bytes.  The proof uses the already constructed exact block codec.
-/
theorem some_canonical_block_eq_of_key_eq_of_block_bytes_eq
    {context : GraphCodecContext}
    {left right : SomeCanonicalBlock context}
    (keyExact : left.key = right.key)
    (blockBytesExact :
      encodeCanonicalBlock left.block =
        encodeCanonicalBlock right.block) :
    left = right := by
  rcases left with ⟨leftKind, leftBlockQ, leftBlock⟩
  rcases right with ⟨rightKind, rightBlockQ, rightBlock⟩
  simp only [SomeCanonicalBlock.key] at keyExact
  cases keyExact
  have blockExact : leftBlock = rightBlock :=
    canonical_encode_injective
      (constructiveBlockCodec context.kindSchema leftKind)
      blockBytesExact
  cases blockExact
  rfl

/-- Equal kinds and block bytes induce equal derived typed-key encodings. -/
theorem encode_derived_registry_key_eq
    (context : GraphCodecContext)
    {leftKind rightKind : context.kindSchema.Kind}
    {leftBytes rightBytes : GraphBytes}
    (kindExact : leftKind = rightKind)
    (bytesExact : leftBytes = rightBytes) :
    encodeCanonicalRegistryKey context
        ⟨leftKind, context.blockWireAddress leftKind leftBytes⟩ =
      encodeCanonicalRegistryKey context
        ⟨rightKind, context.blockWireAddress rightKind rightBytes⟩ := by
  subst rightKind
  subst rightBytes
  rfl

/--
Block-byte preservation across one graph transport also preserves the complete
derived typed registry key.
-/
theorem transported_registry_key_bytes_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (leftIndex : Fin left.canonicalRegistry.length) :
    encodeCanonicalRegistryKey context
        (left.canonicalRegistry.get leftIndex).key =
      encodeCanonicalRegistryKey context
        (right.canonicalRegistry.get
          (isomorphism.transport.blockBijection.forward leftIndex)).key := by
  have leftDerived :=
    left.blockAddressesDerived
      (left.canonicalRegistry.get leftIndex)
      (list_get_mem_fin left.canonicalRegistry leftIndex)
  have rightDerived :=
    right.blockAddressesDerived
      (right.canonicalRegistry.get
        (isomorphism.transport.blockBijection.forward leftIndex))
      (list_get_mem_fin right.canonicalRegistry
        (isomorphism.transport.blockBijection.forward leftIndex))
  have kindExact :=
    isomorphism.transport.blockKindPreserved leftIndex
  unfold SomeCanonicalBlock.key
  rw [leftDerived, rightDerived]
  exact
    encode_derived_registry_key_eq
      context kindExact (blockBytes leftIndex)

/-- The transported key-byte sets have exactly the same finite members. -/
theorem transported_registry_key_bytes_mem_iff
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (bytes : GraphBytes) :
    bytes ∈
        left.canonicalRegistry.map
          (fun entry =>
            encodeCanonicalRegistryKey context entry.key) ↔
      bytes ∈
        right.canonicalRegistry.map
          (fun entry =>
            encodeCanonicalRegistryKey context entry.key) := by
  constructor
  · intro leftMember
    rcases List.mem_map.mp leftMember with
      ⟨leftEntry, leftEntryMember, leftEntryExact⟩
    rcases List.get_of_mem leftEntryMember with
      ⟨leftIndex, leftGetExact⟩
    apply List.mem_map.mpr
    refine
      ⟨right.canonicalRegistry.get
          (isomorphism.transport.blockBijection.forward leftIndex),
        list_get_mem_fin right.canonicalRegistry
          (isomorphism.transport.blockBijection.forward leftIndex),
        ?_⟩
    calc
      encodeCanonicalRegistryKey context
          (right.canonicalRegistry.get
            (isomorphism.transport.blockBijection.forward leftIndex)).key =
          encodeCanonicalRegistryKey context
            (left.canonicalRegistry.get leftIndex).key :=
        (transported_registry_key_bytes_eq
          isomorphism blockBytes leftIndex).symm
      _ = encodeCanonicalRegistryKey context leftEntry.key :=
        congrArg
          (fun entry =>
            encodeCanonicalRegistryKey context entry.key)
          leftGetExact
      _ = bytes := leftEntryExact
  · intro rightMember
    rcases List.mem_map.mp rightMember with
      ⟨rightEntry, rightEntryMember, rightEntryExact⟩
    rcases List.get_of_mem rightEntryMember with
      ⟨rightIndex, rightGetExact⟩
    let leftIndex :=
      isomorphism.transport.blockBijection.inverse rightIndex
    apply List.mem_map.mpr
    refine
      ⟨left.canonicalRegistry.get leftIndex,
        list_get_mem_fin left.canonicalRegistry leftIndex,
        ?_⟩
    calc
      encodeCanonicalRegistryKey context
          (left.canonicalRegistry.get leftIndex).key =
          encodeCanonicalRegistryKey context
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).key :=
        transported_registry_key_bytes_eq
          isomorphism blockBytes leftIndex
      _ = encodeCanonicalRegistryKey context
            (right.canonicalRegistry.get rightIndex).key := by
        exact
          congrArg
            (fun index =>
              encodeCanonicalRegistryKey context
                (right.canonicalRegistry.get index).key)
            (isomorphism.transport.blockBijection.rightInverse rightIndex)
      _ = encodeCanonicalRegistryKey context rightEntry.key :=
        congrArg
          (fun entry =>
            encodeCanonicalRegistryKey context entry.key)
          rightGetExact
      _ = bytes := rightEntryExact

/-- The transported registry key-byte lists are permutations. -/
theorem transported_registry_key_bytes_permutation
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block) :
    List.Perm
      (left.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key))
      (right.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key)) :=
  no_duplicates_mem_iff_permutation
    left.registryKeysNoDup
    right.registryKeysNoDup
    (transported_registry_key_bytes_mem_iff isomorphism blockBytes)

/-- A closed registry's full typed-key encodings retain its strict order. -/
theorem canonical_registry_key_bytes_sorted
    {context : GraphCodecContext}
    (graph : ClosedRootedGraph context) :
    List.Pairwise
      (bytesLessOrEqual (fun bytes : GraphBytes => bytes))
      (graph.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key)) := by
  rw [List.pairwise_map]
  exact graph.registryStrictlySorted.imp (by
    intro leftEntry rightEntry ordered
    unfold bytesLessOrEqual
    simp [ordered])

/- Because both transported key lists are duplicate-free and canonically
sorted, their permutation equality strengthens to literal list equality. -/
set_option linter.deprecated false in
theorem transported_registry_key_bytes_list_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block) :
    left.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) =
      right.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) := by
  apply List.Perm.eq_of_sorted
    (fun first second _ _ =>
      bytes_less_or_equal_antisymmetric
        (fun bytes : GraphBytes => bytes)
        (fun equal => equal))
    (canonical_registry_key_bytes_sorted left)
    (canonical_registry_key_bytes_sorted right)
  exact transported_registry_key_bytes_permutation isomorphism blockBytes

/-- Transported closed registries have the same finite cardinality. -/
theorem transported_registry_lengths_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block) :
    left.canonicalRegistry.length =
      right.canonicalRegistry.length := by
  have mappedLengths :=
    congrArg List.length
      (transported_registry_key_bytes_list_eq isomorphism blockBytes)
  simpa using mappedLengths

/-- Canonical sorting aligns the full typed key bytes at every numeric slot. -/
theorem same_index_registry_key_bytes_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (index : Nat)
    (leftBound : index < left.canonicalRegistry.length)
    (rightBound : index < right.canonicalRegistry.length) :
    encodeCanonicalRegistryKey context
        (left.canonicalRegistry.get ⟨index, leftBound⟩).key =
      encodeCanonicalRegistryKey context
        (right.canonicalRegistry.get ⟨index, rightBound⟩).key := by
  have optionExact :=
    congrArg (fun values => listGet? values index)
      (transported_registry_key_bytes_list_eq isomorphism blockBytes)
  simp only [list_get?_map] at optionExact
  rw [
    list_get?_eq_get left.canonicalRegistry ⟨index, leftBound⟩,
    list_get?_eq_get right.canonicalRegistry ⟨index, rightBound⟩
  ] at optionExact
  exact Option.some.inj optionExact

/-- Duplicate-free finite lists reflect equality of values back to indices. -/
theorem no_duplicates_get_injective_global :
    ∀ (values : List α),
      NoDuplicates values →
      ∀ (leftIndex rightIndex : Fin values.length),
        values.get leftIndex = values.get rightIndex →
        leftIndex = rightIndex := by
  intro values
  induction values with
  | nil =>
      intro _ leftIndex
      exact Fin.elim0 leftIndex
  | cons head tail ih =>
      intro noDuplicates leftIndex rightIndex getExact
      have headDifferent :=
        (List.pairwise_cons.mp noDuplicates).1
      have tailNoDuplicates :=
        (List.pairwise_cons.mp noDuplicates).2
      rcases leftIndex with ⟨leftIndex, leftBound⟩
      rcases rightIndex with ⟨rightIndex, rightBound⟩
      cases leftIndex with
      | zero =>
          cases rightIndex with
          | zero =>
              rfl
          | succ rightIndex =>
              have rightTailBound : rightIndex < tail.length :=
                Nat.succ_lt_succ_iff.mp rightBound
              have rightMember :=
                list_get_mem_fin tail ⟨rightIndex, rightTailBound⟩
              exact False.elim
                (headDifferent
                  (tail.get ⟨rightIndex, rightTailBound⟩)
                  rightMember
                  (by simpa using getExact))
      | succ leftIndex =>
          have leftTailBound : leftIndex < tail.length :=
            Nat.succ_lt_succ_iff.mp leftBound
          cases rightIndex with
          | zero =>
              have leftMember :=
                list_get_mem_fin tail ⟨leftIndex, leftTailBound⟩
              exact False.elim
                (headDifferent
                  (tail.get ⟨leftIndex, leftTailBound⟩)
                  leftMember
                  (by simpa using getExact.symm))
          | succ rightIndex =>
              have rightTailBound : rightIndex < tail.length :=
                Nat.succ_lt_succ_iff.mp rightBound
              have tailIndexExact :
                  (⟨leftIndex, leftTailBound⟩ : Fin tail.length) =
                    ⟨rightIndex, rightTailBound⟩ :=
                ih tailNoDuplicates
                  ⟨leftIndex, leftTailBound⟩
                  ⟨rightIndex, rightTailBound⟩
                  (by simpa using getExact)
              apply Fin.ext
              simpa using congrArg Fin.val tailIndexExact

/--
Strict canonical key ordering forces the global block transport to preserve
the numeric registry slot.
-/
theorem transported_block_index_val_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (leftIndex : Fin left.canonicalRegistry.length) :
    (isomorphism.transport.blockBijection.forward leftIndex).val =
      leftIndex.val := by
  let encodeKey : SomeCanonicalBlock context → GraphBytes :=
    fun entry => encodeCanonicalRegistryKey context entry.key
  have rightSameBound :
      leftIndex.val < right.canonicalRegistry.length := by
    rw [← transported_registry_lengths_eq isomorphism blockBytes]
    exact leftIndex.isLt
  let rightSameIndex : Fin right.canonicalRegistry.length :=
    ⟨leftIndex.val, rightSameBound⟩
  have transportedKeyExact :
      encodeKey
          (right.canonicalRegistry.get
            (isomorphism.transport.blockBijection.forward leftIndex)) =
        encodeKey (left.canonicalRegistry.get leftIndex) :=
    (transported_registry_key_bytes_eq
      isomorphism blockBytes leftIndex).symm
  have sameIndexKeyExact :
      encodeKey (left.canonicalRegistry.get leftIndex) =
        encodeKey (right.canonicalRegistry.get rightSameIndex) :=
    same_index_registry_key_bytes_eq
      isomorphism blockBytes leftIndex.val
        leftIndex.isLt rightSameBound
  let transportedMapIndex :
      Fin (right.canonicalRegistry.map encodeKey).length :=
    ⟨(isomorphism.transport.blockBijection.forward leftIndex).val,
      by
        simpa only [List.length_map] using
          (isomorphism.transport.blockBijection.forward leftIndex).isLt⟩
  let sameMapIndex :
      Fin (right.canonicalRegistry.map encodeKey).length :=
    ⟨rightSameIndex.val,
      by simpa only [List.length_map] using rightSameIndex.isLt⟩
  have mappedGetExact :
      (right.canonicalRegistry.map encodeKey).get transportedMapIndex =
        (right.canonicalRegistry.map encodeKey).get sameMapIndex := by
    simpa [transportedMapIndex, sameMapIndex] using
      transportedKeyExact.trans sameIndexKeyExact
  have mappedIndexExact :
      transportedMapIndex = sameMapIndex :=
    no_duplicates_get_injective_global
      (right.canonicalRegistry.map encodeKey)
      right.registryKeysNoDup
      transportedMapIndex sameMapIndex mappedGetExact
  exact congrArg Fin.val mappedIndexExact

/-- Equal sorted slots contain the same dependent canonical entry. -/
theorem same_index_registry_entry_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (index : Nat)
    (leftBound : index < left.canonicalRegistry.length)
    (rightBound : index < right.canonicalRegistry.length) :
    left.canonicalRegistry.get ⟨index, leftBound⟩ =
      right.canonicalRegistry.get ⟨index, rightBound⟩ := by
  let leftIndex : Fin left.canonicalRegistry.length :=
    ⟨index, leftBound⟩
  let rightIndex : Fin right.canonicalRegistry.length :=
    ⟨index, rightBound⟩
  have keyExact :
      (left.canonicalRegistry.get leftIndex).key =
        (right.canonicalRegistry.get rightIndex).key :=
    encode_canonical_registry_key_injective
      (same_index_registry_key_bytes_eq
        isomorphism blockBytes index leftBound rightBound)
  have transportedIndexExact :
      isomorphism.transport.blockBijection.forward leftIndex =
        rightIndex :=
    Fin.ext (transported_block_index_val_eq
      isomorphism blockBytes leftIndex)
  have sameIndexBlockBytes :
      encodeCanonicalBlock
          (left.canonicalRegistry.get leftIndex).block =
        encodeCanonicalBlock
          (right.canonicalRegistry.get rightIndex).block := by
    rw [← transportedIndexExact]
    exact blockBytes leftIndex
  exact
    some_canonical_block_eq_of_key_eq_of_block_bytes_eq
      keyExact sameIndexBlockBytes

/-- Transported block-byte equality determines the literal closed registry. -/
theorem transported_registry_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block) :
    left.canonicalRegistry = right.canonicalRegistry := by
  apply List.ext_get
    (transported_registry_lengths_eq isomorphism blockBytes)
  intro index leftBound rightBound
  exact
    same_index_registry_entry_eq
      isomorphism blockBytes index leftBound rightBound

/--
Transported block bytes together with a fixed transported root-node index
determine the complete serialized canonical projection.
-/
theorem serialized_canonical_projection_eq_of_block_bytes_and_root_node
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (rootNodeValueFixed :
      ((isomorphism.transport.nodeBijection
          ⟨left.canonicalRoot.blockIndex,
            left.canonicalRoot.blockBound⟩).forward
          ⟨left.canonicalRoot.localIndex,
            left.canonicalRoot.localBound⟩).val =
        left.canonicalRoot.localIndex) :
    serializedCanonicalProjection left =
      serializedCanonicalProjection right := by
  have registryExact :
      left.canonicalRegistry = right.canonicalRegistry :=
    transported_registry_eq isomorphism blockBytes
  have rootBlockExact :
      left.canonicalRoot.blockIndex =
        right.canonicalRoot.blockIndex :=
    (transported_block_index_val_eq isomorphism blockBytes
      ⟨left.canonicalRoot.blockIndex,
        left.canonicalRoot.blockBound⟩).symm.trans
      isomorphism.root.blockIndexExact.symm
  have rootLocalExact :
      left.canonicalRoot.localIndex =
        right.canonicalRoot.localIndex :=
    rootNodeValueFixed.symm.trans
      isomorphism.root.localIndexExact.symm
  have serializedRootExact :
      SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex =
        SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          right.canonicalRoot.localIndex := by
    calc
      SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex =
        SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex :=
        congrArg
          (fun blockIndex =>
            SerializedCanonicalRoot.mk blockIndex
              left.canonicalRoot.localIndex)
          rootBlockExact
      _ = SerializedCanonicalRoot.mk
            right.canonicalRoot.blockIndex
            right.canonicalRoot.localIndex :=
        congrArg
          (SerializedCanonicalRoot.mk
            right.canonicalRoot.blockIndex)
          rootLocalExact
  unfold serializedCanonicalProjection
  calc
    CanonicalRootedGraph.mk left.canonicalRegistry
        (SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex) =
      CanonicalRootedGraph.mk right.canonicalRegistry
        (SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex) :=
      congrArg
        (fun registry =>
          CanonicalRootedGraph.mk registry
            (SerializedCanonicalRoot.mk
              left.canonicalRoot.blockIndex
              left.canonicalRoot.localIndex))
        registryExact
    _ = CanonicalRootedGraph.mk right.canonicalRegistry
          (SerializedCanonicalRoot.mk
            right.canonicalRoot.blockIndex
            right.canonicalRoot.localIndex) :=
      congrArg
        (CanonicalRootedGraph.mk right.canonicalRegistry)
        serializedRootExact

/--
Block-byte rigidity and local-node index rigidity determine the complete
serialized canonical projection.
-/
theorem serialized_canonical_projection_eq_of_block_and_node_rigidity
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (blockBytes :
      ∀ leftIndex,
        encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block =
          encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftIndex)).block)
    (nodeIndexValuesFixed :
      ∀ (leftIndex : Fin left.canonicalRegistry.length)
        (leftNodeIndex :
          Fin
            (left.canonicalRegistry.get
              leftIndex).block.nodes.length),
        ((isomorphism.transport.nodeBijection
          leftIndex).forward leftNodeIndex).val =
            leftNodeIndex.val) :
    serializedCanonicalProjection left =
      serializedCanonicalProjection right :=
  serialized_canonical_projection_eq_of_block_bytes_and_root_node
    isomorphism blockBytes
      (nodeIndexValuesFixed
        ⟨left.canonicalRoot.blockIndex,
          left.canonicalRoot.blockBound⟩
        ⟨left.canonicalRoot.localIndex,
          left.canonicalRoot.localBound⟩)

private def TransportedBlockBytes
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftIndex : Fin left.canonicalRegistry.length) : Prop :=
  encodeCanonicalBlock
      (left.canonicalRegistry.get leftIndex).block =
    encodeCanonicalBlock
      (right.canonicalRegistry.get
        (isomorphism.transport.blockBijection.forward
          leftIndex)).block

private def TransportedNodeValuesFixed
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftIndex : Fin left.canonicalRegistry.length) : Prop :=
  ∀ leftNodeIndex,
    ((isomorphism.transport.nodeBijection leftIndex).forward
      leftNodeIndex).val =
    leftNodeIndex.val

private structure TransportExactAt
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftIndex : Fin left.canonicalRegistry.length) where
  agreement :
    LowerRankCanonicalEnvironmentAgreement
      isomorphism.transport leftIndex
  blockBytes :
    TransportedBlockBytes isomorphism leftIndex
  nodeValuesFixed :
    TransportedNodeValuesFixed isomorphism leftIndex

/--
Strong dependency-height induction establishes canonical block bytes and
local-node index rigidity at every transported block.
-/
private theorem graph_isomorphism_exactness_by_dependency_height
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right) :
    ∀ leftIndex,
      Nonempty
        (TransportExactAt isomorphism leftIndex) := by
  have buildAtHeight :
      ∀ rank,
        ∀ leftIndex,
          left.dependency.height leftIndex.val = rank →
            Nonempty
              (TransportExactAt isomorphism leftIndex) := by
    intro rank
    induction rank using Nat.strongRecOn with
    | ind rank lowerBuild =>
        intro leftIndex heightExact
        have lowerBlocks :
            ∀ lowerIndex,
              left.dependency.height lowerIndex.val <
                  left.dependency.height leftIndex.val →
                TransportedBlockBytes isomorphism lowerIndex := by
          intro lowerIndex lower
          exact
            Nonempty.elim
              (lowerBuild
                (left.dependency.height lowerIndex.val)
                (by omega)
                lowerIndex rfl)
              (fun exactAt => exactAt.blockBytes)
        have lowerNodes :
            ∀ lowerIndex,
              left.dependency.height lowerIndex.val <
                  left.dependency.height leftIndex.val →
                TransportedNodeValuesFixed isomorphism lowerIndex := by
          intro lowerIndex lower
          exact
            Nonempty.elim
              (lowerBuild
                (left.dependency.height lowerIndex.val)
                (by omega)
                lowerIndex rfl)
              (fun exactAt => exactAt.nodeValuesFixed)
        let agreement :=
          isomorphism.lowerRankEnvironmentAgreement
            leftIndex
            (fun lowerIndex lower =>
              lowerBlocks lowerIndex lower)
            (fun lowerIndex lower =>
              lowerNodes lowerIndex lower)
        have candidateBytes :=
          pure_materialize_transport_encode_exact
            leftIndex agreement (isomorphism.blocks leftIndex)
        have blockBytes :
            TransportedBlockBytes isomorphism leftIndex :=
          block_encode_eq_of_isomorphic_canonical_minima
            isomorphism.transport leftIndex agreement
            (isomorphism.blocks leftIndex)
            (left.canonicalMinima
              (left.canonicalRegistry.get leftIndex)
              (list_get_mem_fin
                left.canonicalRegistry leftIndex))
            (right.canonicalMinima
              (right.canonicalRegistry.get
                (isomorphism.transport.blockBijection.forward
                  leftIndex))
              (list_get_mem_fin
                right.canonicalRegistry
                (isomorphism.transport.blockBijection.forward
                  leftIndex)))
        have nodeValuesFixed :
            TransportedNodeValuesFixed isomorphism leftIndex :=
          transported_node_indices_rigid_of_candidate_bytes
            isomorphism.transport leftIndex
            candidateBytes blockBytes
        exact
          ⟨{ agreement
             blockBytes
             nodeValuesFixed }⟩
  intro leftIndex
  exact
    buildAtHeight
      (left.dependency.height leftIndex.val)
      leftIndex rfl

/--
Every concrete graph isomorphism determines identical serialized canonical
projections.
-/
theorem graph_isomorphism_implies_serialized_projection_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right) :
    serializedCanonicalProjection left =
      serializedCanonicalProjection right := by
  have exactAt :=
    graph_isomorphism_exactness_by_dependency_height isomorphism
  exact
    serialized_canonical_projection_eq_of_block_and_node_rigidity
      isomorphism
      (fun leftIndex =>
        Nonempty.elim
          (exactAt leftIndex)
          (fun result => result.blockBytes))
      (fun leftIndex leftNodeIndex =>
        Nonempty.elim
          (exactAt leftIndex)
          (fun result =>
            result.nodeValuesFixed leftNodeIndex))

/--
Propositionally witnessed graph isomorphism determines equality of the
canonical quotient observation.
-/
theorem graph_isomorphic_implies_canonical_graph_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphic : GraphIsomorphic left right) :
    canonicalGraph left = canonicalGraph right := by
  exact
    Nonempty.elim isomorphic
      (fun isomorphism => by
        unfold canonicalGraph
        exact
          graph_isomorphism_implies_serialized_projection_eq
            isomorphism)

/--
Concrete graph isomorphism is exact equality of the canonical quotient
observation.
-/
theorem graph_isomorphic_iff_canonical_graph_eq
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context} :
    GraphIsomorphic left right ↔
      canonicalGraph left = canonicalGraph right := by
  constructor
  · exact graph_isomorphic_implies_canonical_graph_eq
  · intro canonicalExact
    apply canonical_projection_eq_implies_graph_isomorphic
    simpa [canonicalGraph] using canonicalExact

/--
The concrete canonical graph encoder reflects the complete serialized
projection on already closed graphs.
-/
theorem encode_canonical_graph_reflects_serialized_projection
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (encodedExact :
      encodeCanonicalGraph context left =
        encodeCanonicalGraph context right) :
    serializedCanonicalProjection left =
      serializedCanonicalProjection right := by
  rcases
      encode_canonical_graph_reflects_registry_root encodedExact with
    ⟨registryExact, rootKeyExact, rootLocalExact⟩
  let encodeKey : SomeCanonicalBlock context → GraphBytes :=
    fun entry => encodeCanonicalRegistryKey context entry.key
  let leftRootIndex : Fin left.canonicalRegistry.length :=
    ⟨left.canonicalRoot.blockIndex,
      left.canonicalRoot.blockBound⟩
  let rightRootIndex : Fin right.canonicalRegistry.length :=
    ⟨right.canonicalRoot.blockIndex,
      right.canonicalRoot.blockBound⟩
  have leftRootRightBound :
      left.canonicalRoot.blockIndex <
        right.canonicalRegistry.length := by
    rw [← registryExact]
    exact left.canonicalRoot.blockBound
  let leftRootInRight : Fin right.canonicalRegistry.length :=
    ⟨left.canonicalRoot.blockIndex, leftRootRightBound⟩
  have leftEntryExact :
      left.canonicalRegistry.get leftRootIndex =
        right.canonicalRegistry.get leftRootInRight := by
    have optionExact :=
      congrArg
        (fun registry =>
          listGet? registry left.canonicalRoot.blockIndex)
        registryExact
    have indexedOptionExact :
        listGet? left.canonicalRegistry leftRootIndex.val =
          listGet? right.canonicalRegistry leftRootInRight.val := by
      simpa [leftRootIndex, leftRootInRight] using optionExact
    rw [
      list_get?_eq_get left.canonicalRegistry leftRootIndex,
      list_get?_eq_get right.canonicalRegistry leftRootInRight
    ] at indexedOptionExact
    exact Option.some.inj indexedOptionExact
  have rightRootKeyExact :
      encodeKey
          (right.canonicalRegistry.get leftRootInRight) =
        encodeKey
          (right.canonicalRegistry.get rightRootIndex) :=
    (congrArg encodeKey leftEntryExact).symm.trans rootKeyExact
  let leftMappedIndex :
      Fin (right.canonicalRegistry.map encodeKey).length :=
    ⟨leftRootInRight.val, by
      simpa only [List.length_map] using leftRootInRight.isLt⟩
  let rightMappedIndex :
      Fin (right.canonicalRegistry.map encodeKey).length :=
    ⟨rightRootIndex.val, by
      simpa only [List.length_map] using rightRootIndex.isLt⟩
  have mappedGetExact :
      (right.canonicalRegistry.map encodeKey).get leftMappedIndex =
        (right.canonicalRegistry.map encodeKey).get
          rightMappedIndex := by
    simpa [leftMappedIndex, rightMappedIndex] using rightRootKeyExact
  have mappedIndexExact :
      leftMappedIndex = rightMappedIndex :=
    no_duplicates_get_injective_global
      (right.canonicalRegistry.map encodeKey)
      right.registryKeysNoDup
      leftMappedIndex rightMappedIndex mappedGetExact
  have rootBlockExact :
      left.canonicalRoot.blockIndex =
        right.canonicalRoot.blockIndex :=
    congrArg Fin.val mappedIndexExact
  have serializedRootExact :
      SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex =
        SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          right.canonicalRoot.localIndex := by
    calc
      SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex =
        SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex :=
        congrArg
          (fun blockIndex =>
            SerializedCanonicalRoot.mk blockIndex
              left.canonicalRoot.localIndex)
          rootBlockExact
      _ =
        SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          right.canonicalRoot.localIndex :=
        congrArg
          (SerializedCanonicalRoot.mk
            right.canonicalRoot.blockIndex)
          rootLocalExact
  unfold serializedCanonicalProjection
  calc
    CanonicalRootedGraph.mk left.canonicalRegistry
        (SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex) =
      CanonicalRootedGraph.mk right.canonicalRegistry
        (SerializedCanonicalRoot.mk
          left.canonicalRoot.blockIndex
          left.canonicalRoot.localIndex) :=
      congrArg
        (fun registry =>
          CanonicalRootedGraph.mk registry
            (SerializedCanonicalRoot.mk
              left.canonicalRoot.blockIndex
              left.canonicalRoot.localIndex))
        registryExact
    _ =
      CanonicalRootedGraph.mk right.canonicalRegistry
        (SerializedCanonicalRoot.mk
          right.canonicalRoot.blockIndex
          right.canonicalRoot.localIndex) :=
      congrArg
        (CanonicalRootedGraph.mk right.canonicalRegistry)
        serializedRootExact

/--
Canonical graph bytes are equal exactly for concretely isomorphic closed
rooted graphs.
-/
theorem canonical_graph_bytes_eq_iff_isomorphic
    (left right : ClosedRootedGraph context) :
    encodeCanonicalGraph context left =
        encodeCanonicalGraph context right ↔
      GraphIsomorphic left right := by
  constructor
  · intro encodedExact
    apply graph_isomorphic_iff_canonical_graph_eq.mpr
    simpa [canonicalGraph] using
      encode_canonical_graph_reflects_serialized_projection encodedExact
  · intro isomorphic
    exact
      encode_canonical_graph_factors_serialized_projection
        (by
          simpa [canonicalGraph] using
            graph_isomorphic_iff_canonical_graph_eq.mp isomorphic)

theorem GraphIsomorphic.symm
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphic : GraphIsomorphic left right) :
    GraphIsomorphic right left :=
  graph_isomorphic_iff_canonical_graph_eq.mpr
    (graph_isomorphic_iff_canonical_graph_eq.mp isomorphic).symm

theorem GraphIsomorphic.trans
    {context : GraphCodecContext}
    {left middle right : ClosedRootedGraph context}
    (leftMiddle : GraphIsomorphic left middle)
    (middleRight : GraphIsomorphic middle right) :
    GraphIsomorphic left right :=
  graph_isomorphic_iff_canonical_graph_eq.mpr
    ((graph_isomorphic_iff_canonical_graph_eq.mp leftMiddle).trans
      (graph_isomorphic_iff_canonical_graph_eq.mp middleRight))

theorem closed_rooted_graph_equivalence
    (context : GraphCodecContext) :
    Equivalence
      (fun left right : ClosedRootedGraph context =>
        GraphIsomorphic left right) :=
  ⟨GraphIsomorphic.refl,
    GraphIsomorphic.symm,
    GraphIsomorphic.trans⟩

/--
The addressed-graph implementation domain is quotient adequate.
-/
def closedRootedGraphQuotientAdequate
    (context : GraphCodecContext) :
    QuotientAdequate (closedRootedGraphDomain context) where
  equivalence := fun _ =>
    closed_rooted_graph_equivalence context
  observe_sound := by
    intro _ left right isomorphic
    exact graph_isomorphic_implies_canonical_graph_eq isomorphic

/--
The canonical observation is complete for graph isomorphism.
-/
theorem closedRootedGraphObservationExact
    (context : GraphCodecContext) :
    ObservationExact (closedRootedGraphDomain context) := by
  intro _ left right observedExact
  exact graph_isomorphic_iff_canonical_graph_eq.mpr observedExact

/-- Quotient carrier of closed rooted graphs modulo concrete isomorphism. -/
abbrev RootedGraphClass (context : GraphCodecContext) :=
  Quotient
    ((closedRootedGraphDomain context).setoid
      (closedRootedGraphQuotientAdequate context) ())

/--
Encode an addressed-graph quotient class through its canonical graph
observation.
-/
def encodeGraphClass
    (context : GraphCodecContext)
    (graphClass : RootedGraphClass context) : GraphBytes :=
  Quotient.lift
    (encodeCanonicalGraph context)
    (fun _left _right isomorphic =>
      encode_canonical_graph_factors_serialized_projection
        (graph_isomorphic_iff_canonical_graph_eq.mp isomorphic))
    graphClass

/-- Decode canonical graph bytes into the addressed-graph quotient class. -/
def decodeGraphBytes
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (bytes : GraphBytes) :
    Option (RootedGraphClass context) :=
  match decodeCanonicalGraphDetailed context injective bytes with
  | .error _ => none
  | .ok graph =>
      some
        (qAbs (closedRootedGraphDomain context)
          (closedRootedGraphQuotientAdequate context) () graph)

theorem decode_encode_canonical_graph
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context) :
    decodeGraphBytes context injective
        (encodeCanonicalGraph context graph) =
      some
        (qAbs (closedRootedGraphDomain context)
          (closedRootedGraphQuotientAdequate context) () graph) := by
  rcases
      decode_detailed_encode_observation context injective graph with
    ⟨decoded, decodedExact, observationExact⟩
  unfold decodeGraphBytes
  rw [decodedExact]
  simp only
  apply congrArg some
  apply
    (qAbs_eq_iff_equivalent
      (closedRootedGraphDomain context)
      (closedRootedGraphQuotientAdequate context) () decoded graph).2
  exact
    graph_isomorphic_iff_canonical_graph_eq.mpr
      observationExact

theorem encode_decode_canonical_graph
    {context : GraphCodecContext}
    {injective : GraphDigestInjective context}
    {bytes : GraphBytes}
    {graphClass : RootedGraphClass context}
    (accepted :
      decodeGraphBytes context injective bytes = some graphClass) :
    encodeGraphClass context graphClass = bytes := by
  unfold decodeGraphBytes at accepted
  cases detailedExact :
      decodeCanonicalGraphDetailed context injective bytes with
  | error residue =>
      simp [detailedExact] at accepted
  | ok graph =>
      have classExact :
          qAbs (closedRootedGraphDomain context)
              (closedRootedGraphQuotientAdequate context) () graph =
            graphClass := by
        simpa [detailedExact] using accepted
      rw [← classExact]
      exact decode_detailed_reencodes_exact detailedExact

/--
Exact constructive codec for addressed-graph quotient classes.
-/
def constructiveGraphCodec
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context) :
    ExactCanonicalCodec (RootedGraphClass context) GraphBytes where
  encode := encodeGraphClass context
  decode := decodeGraphBytes context injective
  decode_encode := by
    intro graphClass
    refine Quotient.inductionOn graphClass ?_
    intro graph
    exact decode_encode_canonical_graph context injective graph
  encode_decode_canonical := by
    intro bytes graphClass accepted
    exact encode_decode_canonical_graph accepted

/-- Public quotient-adequacy name retained by the addressed-graph API. -/
abbrev closedRootedGraphAdequate
    (context : GraphCodecContext) :
    QuotientAdequate (closedRootedGraphDomain context) :=
  closedRootedGraphQuotientAdequate context

/--
Under the explicit root-digest injectivity premise, root-address equality is
exactly graph isomorphism.
-/
theorem root_address_eq_iff_graph_isomorphic
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context) :
    rootAddress context left = rootAddress context right ↔
      GraphIsomorphic left right := by
  simpa [
    rootAddress,
    canonicalObjectAddress,
    canonicalBytes,
    constructiveGraphCodec,
    encodeGraphClass,
    closedRootedGraphAdequate
  ] using
    (canonical_object_address_eq_iff_equivalent
      (closedRootedGraphDomain context)
      (closedRootedGraphAdequate context) ()
      (constructiveGraphCodec context injective)
      context.rootBinding injective.root left right)

/-- Root-address equality soundly reflects graph isomorphism. -/
theorem root_address_sound
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (equal : rootAddress context left = rootAddress context right) :
    GraphIsomorphic left right :=
  (root_address_eq_iff_graph_isomorphic
    context injective left right).mp equal

/-- Graph isomorphism completely determines the typed root address. -/
theorem root_address_complete
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (isomorphic : GraphIsomorphic left right) :
    rootAddress context left = rootAddress context right :=
  (root_address_eq_iff_graph_isomorphic
    context injective left right).mpr isomorphic

end Residua.RCC.Addressing.AddressedGraph


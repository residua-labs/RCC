import RCC.AddressedGraph
import RCCTests.AddressedGraphCodec

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph

namespace Residua.RCC.Addressing.AddressedGraph.Tests

/-! `Codec.Tests.text` uses `String.toList`, which carries a hidden choice
dependency under Lean 4.29. The final exact-type fixture therefore
reuses only the choice-free schema, bindings, and digest proofs, and builds
wire text from explicit scalar lists. -/
def concreteBlockWire
    (bytes : GraphBytes) : GraphWireAddress .syntax where
  algorithm := ⟨['f']⟩
  domainQ := ⟨['b']⟩
  schemaQ := ⟨['v']⟩
  digest :=
    ⟨(Codec.Tests.byteTokens bytes).map Codec.Tests.tokenChar⟩

theorem concrete_block_wire_refines (bytes : GraphBytes) :
    (concreteBlockWire bytes).toAddress =
      Codec.Tests.blockBinding.address bytes := rfl

def concreteContext : GraphCodecContext where
  kindSchema := Codec.Tests.fixtureSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := fun _ => Codec.Tests.blockBinding
  blockWireAddress := fun _ => concreteBlockWire
  blockWireAddressRefines := fun _ => concrete_block_wire_refines
  rootBinding := Codec.Tests.rootBinding

def concreteInjective : GraphDigestInjective concreteContext where
  block := fun _ => Codec.Tests.block_injective
  root := Codec.Tests.root_injective

def concreteSingletonNode
    (payload : Nat) : CanonicalNode Codec.Tests.fixtureSchema :=
  { payload, edgeCollections := [] }

def concreteSingletonBlock
    (payload : Nat) : CanonicalBlock Codec.Tests.fixtureSchema () :=
  .dagSingleton (concreteSingletonNode payload)

def concreteSingletonEntry
    (payload : Nat) : SomeCanonicalBlock concreteContext :=
  { kind := ()
    blockQ :=
      concreteBlockWire
        (encodeCanonicalBlock (concreteSingletonBlock payload))
    block := concreteSingletonBlock payload }

def concreteSingletonRegistry
    (payload : Nat) : List (SomeCanonicalBlock concreteContext) :=
  [concreteSingletonEntry payload]

theorem concrete_singleton_collection_impossible
    (payload : Nat)
    (occurrence :
      CanonicalCollectionOccurrence
        (concreteSingletonBlock payload).nodes) :
    False := by
  have nodeBound :
      occurrence.sourceNodeIndex <
        (concreteSingletonBlock payload).nodes.length :=
    list_get?_some_bound occurrence.sourceNodeLookup
  have nodeIndexZero : occurrence.sourceNodeIndex = 0 := by
    change occurrence.sourceNodeIndex < 1 at nodeBound
    omega
  have nodeExact :
      occurrence.sourceNode = concreteSingletonNode payload := by
    have lookup := occurrence.sourceNodeLookup
    change
      listGet? [concreteSingletonNode payload]
          occurrence.sourceNodeIndex =
        some occurrence.sourceNode at lookup
    rw [nodeIndexZero] at lookup
    exact Option.some.inj lookup.symm
  have collectionLookup := occurrence.owningCollectionLookup
  rw [nodeExact] at collectionLookup
  simp [concreteSingletonNode, listGet?] at collectionLookup

theorem concrete_singleton_block_well_formed
    (payload : Nat) :
    CanonicalBlockWellFormed (concreteSingletonBlock payload) := by
  constructor
  · intro occurrence
    exact False.elim
      (concrete_singleton_collection_impossible
        payload occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    exact False.elim
      (concrete_singleton_collection_impossible
        payload occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    exact False.elim
      (concrete_singleton_collection_impossible
        payload occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    intro _
    exact False.elim
      (concrete_singleton_collection_impossible payload occurrence)
  · intro node member
    have nodeExact : node = concreteSingletonNode payload := by
      change node ∈ [concreteSingletonNode payload] at member
      simpa using member
    subst node
    rfl
  · exact
      decode_encode_canonical_block
        Codec.Tests.fixtureSchema ()
        (concreteSingletonBlock payload)

theorem concrete_singleton_registry_well_formed
    (payload : Nat) :
    CanonicalRegistryWellFormed
      concreteContext (concreteSingletonRegistry payload) := by
  constructor
  intro index
  have indexBound := index.isLt
  have indexZero :
      index = ⟨0, by simp [concreteSingletonRegistry]⟩ := by
    change index.val < 1 at indexBound
    apply Fin.ext
    change index.val = 0
    omega
  subst index
  exact concrete_singleton_block_well_formed payload

theorem concrete_singleton_has_no_public_occurrence
    (payload : Nat)
    (occurrence :
      PublicReferenceOccurrence
        (concreteSingletonRegistry payload)) :
    False := by
  have sourceBound := occurrence.sourceBlockBound
  have sourceIndexZero : occurrence.sourceBlockIndex = 0 := by
    simp [concreteSingletonRegistry] at sourceBound
    omega
  have sourceExact :
      occurrence.sourceBlock = concreteSingletonEntry payload := by
    simpa [
      concreteSingletonRegistry,
      sourceIndexZero,
      listGet?
    ] using occurrence.sourceBlockLookup.symm
  have nodeLookup := occurrence.sourceNodeLookup
  rw [sourceExact] at nodeLookup
  have nodeBound :=
    list_get?_some_bound occurrence.sourceNodeLookup
  rw [sourceExact] at nodeBound
  have nodeIndexZero : occurrence.sourceNodeIndex = 0 := by
    change occurrence.sourceNodeIndex < 1 at nodeBound
    omega
  have nodeExact :
      occurrence.sourceNode = concreteSingletonNode payload := by
    change
      listGet? [concreteSingletonNode payload]
          occurrence.sourceNodeIndex =
        some occurrence.sourceNode at nodeLookup
    rw [nodeIndexZero] at nodeLookup
    exact Option.some.inj nodeLookup.symm
  have collectionLookup := occurrence.owningCollectionLookup
  rw [nodeExact] at collectionLookup
  simp [concreteSingletonNode, listGet?] at collectionLookup

def concreteSingletonKeysNoDup
    (payload : Nat) :
    CanonicalRegistryKeysNoDup
      concreteContext (concreteSingletonRegistry payload) := by
  simp [CanonicalRegistryKeysNoDup, concreteSingletonRegistry]

def concreteSingletonResolvedEdges
    (payload : Nat) :
    ResolvedEdgeTable
      (concreteSingletonRegistry payload)
      (concreteSingletonKeysNoDup payload) where
  edges := []
  sound := by simp
  complete := by
    intro occurrence
    exact False.elim
      (concrete_singleton_has_no_public_occurrence payload occurrence)
  occurrenceNoDuplicates := by
    simp [NoDuplicateOccurrenceIdentity]

def concreteSingletonDependency
    (payload : Nat) :
    DependencyCertificate
      (concreteSingletonResolvedEdges payload) where
  height := fun _ => 0
  indexBound := by
    intro index indexBound
    simp [concreteSingletonRegistry]
  decreases := by
    intro source target reference
    rcases reference with ⟨edge, member, _⟩
    simp [concreteSingletonResolvedEdges] at member

def concreteSingletonGraph
    (payload : Nat) : ClosedRootedGraph concreteContext where
  canonicalRegistry := concreteSingletonRegistry payload
  canonicalRoot :=
    { blockIndex := 0
      blockBound := by simp [concreteSingletonRegistry]
      localIndex := 0
      localBound := by
        simp [
          concreteSingletonRegistry,
          concreteSingletonEntry,
          concreteSingletonBlock,
          Residua.RCC.Addressing.AddressedGraph.Foundation.CanonicalBlock.nodes
        ] }
  registryStrictlySorted := by
    simp [
      CanonicalRegistryStrictOrder,
      concreteSingletonRegistry
    ]
  registryKeysNoDup := concreteSingletonKeysNoDup payload
  registryWellFormed :=
    concrete_singleton_registry_well_formed payload
  connectivity := by
    intro entry member nodes cyclic
    simp [concreteSingletonRegistry] at member
    subst entry
    simp [
      concreteSingletonEntry,
      concreteSingletonBlock
    ] at cyclic
  resolvedEdges := concreteSingletonResolvedEdges payload
  dependency := concreteSingletonDependency payload
  blockAddressesDerived := by
    intro entry member
    simp [concreteSingletonRegistry] at member
    subst entry
    rfl
  canonicalMinima := by
    intro entry member
    simp [concreteSingletonRegistry] at member
    subst entry
    exact
      .dagTrivial
        (concreteSingletonNode payload) rfl
        (concrete_singleton_block_well_formed payload)

def concreteGraphA : ClosedRootedGraph concreteContext :=
  concreteSingletonGraph 1

def concreteGraphBSeed : ClosedRootedGraph concreteContext :=
  concreteSingletonGraph 2

theorem concrete_seed_payloads_distinct :
    (concreteSingletonNode 1).payload ≠
      (concreteSingletonNode 2).payload := by
  decide

def concreteGraphB : ClosedRootedGraph concreteContext :=
  match
      decodeCanonicalGraphDetailed
        concreteContext concreteInjective
        (encodeCanonicalGraph concreteContext concreteGraphBSeed) with
  | .error _ => concreteGraphA
  | .ok graph => graph

set_option maxRecDepth 100000 in
theorem concrete_graph_b_decodes :
    decodeCanonicalGraphDetailed
        concreteContext concreteInjective
        (encodeCanonicalGraph concreteContext concreteGraphBSeed) =
      .ok concreteGraphB := by
  rcases
      decode_detailed_encode_observation
        concreteContext concreteInjective concreteGraphBSeed with
    ⟨decoded, decodedExact, _⟩
  have graphExact : concreteGraphB = decoded := by
    exact
      congrArg
        (fun result =>
          match result with
          | .error _ => concreteGraphA
          | .ok graph => graph)
        decodedExact
  rw [graphExact]
  exact decodedExact

set_option maxRecDepth 100000 in
theorem concrete_graph_b_observes_seed :
    serializedCanonicalProjection concreteGraphB =
      serializedCanonicalProjection concreteGraphBSeed := by
  rcases
      decode_detailed_encode_observation
        concreteContext concreteInjective concreteGraphBSeed with
    ⟨decoded, decodedExact, observationExact⟩
  have graphExact : concreteGraphB = decoded := by
    exact
      congrArg
        (fun result =>
          match result with
          | .error _ => concreteGraphA
          | .ok graph => graph)
        decodedExact
  rw [graphExact]
  exact observationExact

set_option autoImplicit false in
theorem concrete_graph_a_decode_encode :
    decodeGraphBytes concreteContext concreteInjective
        (encodeCanonicalGraph concreteContext concreteGraphA) =
      some
        (qAbs (closedRootedGraphDomain concreteContext)
          (closedRootedGraphAdequate concreteContext) ()
          concreteGraphA) :=
  decode_encode_canonical_graph
    concreteContext concreteInjective concreteGraphA

set_option autoImplicit false in
theorem concrete_graph_b_decode_encode :
    decodeGraphBytes concreteContext concreteInjective
        (encodeCanonicalGraph concreteContext concreteGraphB) =
      some
        (qAbs (closedRootedGraphDomain concreteContext)
          (closedRootedGraphAdequate concreteContext) ()
          concreteGraphB) :=
  decode_encode_canonical_graph
    concreteContext concreteInjective concreteGraphB

theorem concrete_graph_bytes_eq_iff_isomorphic :
    encodeCanonicalGraph concreteContext concreteGraphA =
        encodeCanonicalGraph concreteContext concreteGraphB ↔
      GraphIsomorphic concreteGraphA concreteGraphB :=
  canonical_graph_bytes_eq_iff_isomorphic concreteGraphA concreteGraphB

theorem concrete_root_address_eq_iff_isomorphic :
    rootAddress concreteContext concreteGraphA =
        rootAddress concreteContext concreteGraphB ↔
      GraphIsomorphic concreteGraphA concreteGraphB :=
  root_address_eq_iff_graph_isomorphic
    concreteContext concreteInjective concreteGraphA concreteGraphB

theorem concrete_root_address_sound
    (equal :
      rootAddress concreteContext concreteGraphA =
        rootAddress concreteContext concreteGraphB) :
    GraphIsomorphic concreteGraphA concreteGraphB :=
  root_address_sound
    concreteContext concreteInjective
    concreteGraphA concreteGraphB equal

theorem concrete_root_address_complete
    (isomorphic : GraphIsomorphic concreteGraphA concreteGraphB) :
    rootAddress concreteContext concreteGraphA =
      rootAddress concreteContext concreteGraphB :=
  root_address_complete
    concreteContext concreteInjective
    concreteGraphA concreteGraphB isomorphic

#check_failure
  fun
    (equal :
      rootAddress concreteContext concreteGraphA =
        rootAddress concreteContext concreteGraphB) =>
    root_address_sound
      concreteContext Codec.Tests.root_injective
      concreteGraphA concreteGraphB equal

/-! The public roundtrip freezes the exact quotient abstraction, including
the implementation context `()`. -/
theorem graph_decode_encode_contract
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context) :
    decodeGraphBytes context injective
        (encodeCanonicalGraph context graph) =
      some
        (qAbs (closedRootedGraphDomain context)
          (closedRootedGraphAdequate context) () graph) :=
  decode_encode_canonical_graph context injective graph

theorem graph_encode_decode_contract
    (accepted :
      decodeGraphBytes context injective bytes = some graphClass) :
    encodeGraphClass context graphClass = bytes :=
  encode_decode_canonical_graph accepted

theorem graph_bytes_exactly_isomorphism_contract
    (left right : ClosedRootedGraph context) :
    encodeCanonicalGraph context left =
        encodeCanonicalGraph context right ↔
      GraphIsomorphic left right :=
  canonical_graph_bytes_eq_iff_isomorphic left right

/-! Every structural mutant is expressed over real closed graphs and the real
graph encoder/root function, never over caller-supplied byte records. -/
theorem nonisomorphic_graph_bytes_differ
    (left right : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic left right) :
    encodeCanonicalGraph context left ≠
      encodeCanonicalGraph context right := by
  intro equalBytes
  exact different
    ((canonical_graph_bytes_eq_iff_isomorphic left right).1 equalBytes)

theorem nonisomorphic_root_addresses_differ
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic left right) :
    rootAddress context left ≠ rootAddress context right := by
  intro equalRoot
  exact different
    ((root_address_eq_iff_graph_isomorphic
      context injective left right).1 equalRoot)

theorem ordered_mutant_contract
    (injective : GraphDigestInjective context)
    (ordered reversed : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic ordered reversed) :
    encodeCanonicalGraph context ordered ≠
        encodeCanonicalGraph context reversed ∧
      rootAddress context ordered ≠ rootAddress context reversed :=
  ⟨nonisomorphic_graph_bytes_differ ordered reversed different,
    nonisomorphic_root_addresses_differ
      context injective ordered reversed different⟩

theorem unordered_mutant_contract
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (isomorphic : GraphIsomorphic left right) :
    encodeCanonicalGraph context left =
        encodeCanonicalGraph context right ∧
      rootAddress context left = rootAddress context right :=
  ⟨(canonical_graph_bytes_eq_iff_isomorphic left right).2 isomorphic,
    (root_address_eq_iff_graph_isomorphic
      context injective left right).2 isomorphic⟩

theorem multiplicity_mutant_contract
    (injective : GraphDigestInjective context)
    (single repeated : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic single repeated) :
    encodeCanonicalGraph context single ≠
        encodeCanonicalGraph context repeated ∧
      rootAddress context single ≠ rootAddress context repeated :=
  ordered_mutant_contract injective single repeated different

theorem direction_mutant_contract
    (injective : GraphDigestInjective context)
    (outgoing incoming : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic outgoing incoming) :
    encodeCanonicalGraph context outgoing ≠
        encodeCanonicalGraph context incoming ∧
      rootAddress context outgoing ≠ rootAddress context incoming :=
  ordered_mutant_contract injective outgoing incoming different

theorem label_mutant_contract
    (injective : GraphDigestInjective context)
    (first second : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic first second) :
    encodeCanonicalGraph context first ≠
        encodeCanonicalGraph context second ∧
      rootAddress context first ≠ rootAddress context second :=
  ordered_mutant_contract injective first second different

/-! Soundness consumes the complete block-and-root injectivity profile. -/
theorem root_soundness_full_injectivity_contract
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (equal : rootAddress context left = rootAddress context right) :
    GraphIsomorphic left right :=
  root_address_sound context injective left right equal

/-! The final AK-6 public surface and its semantic mutants must stay within the
permitted kernel boundary. These audits are intentionally adjacent to the
exact contracts they protect so a theorem rename cannot silently drop the
check. -/
#print axioms decode_encode_canonical_graph
#print axioms encode_decode_canonical_graph
#print axioms canonical_graph_bytes_eq_iff_isomorphic
#print axioms root_address_eq_iff_graph_isomorphic
#print axioms root_address_sound
#print axioms root_address_complete

#print axioms ordered_mutant_contract
#print axioms unordered_mutant_contract
#print axioms multiplicity_mutant_contract
#print axioms direction_mutant_contract
#print axioms label_mutant_contract

example (graph : ClosedRootedGraph context) :
    GraphIsomorphic graph graph :=
  GraphIsomorphic.refl graph

example (isomorphic : GraphIsomorphic left right) :
    GraphIsomorphic right left :=
  GraphIsomorphic.symm isomorphic

example
    (leftMiddle : GraphIsomorphic left middle)
    (middleRight : GraphIsomorphic middle right) :
    GraphIsomorphic left right :=
  GraphIsomorphic.trans leftMiddle middleRight

/-! Root pointers expose two independent indices and bounds only. -/
#check CanonicalNodePointer.blockIndex
#check CanonicalNodePointer.blockBound
#check CanonicalNodePointer.localIndex
#check CanonicalNodePointer.localBound
#check_failure CanonicalNodePointer.targetIndex
#check_failure CanonicalNodePointer.ref

end Residua.RCC.Addressing.AddressedGraph.Tests


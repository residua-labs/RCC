import RCC.AddressedGraphFoundation

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressedGraph.Foundation.Tests

/-!
# AK-6 shared addressed-graph foundation contracts

These tests pin the proof-free canonical-block syntax and its exact structural
codec.  Closure properties intentionally do not occur here: an empty cyclic
block and a cyclic block with an out-of-bounds local selector are valid syntax
and must decode successfully.
-/

/-! ## Closed two-kind schema -/

inductive GraphKind
  | syntax
  | judgment
  deriving DecidableEq, Repr

def graphKindEnumerate : List GraphKind :=
  [.syntax, .judgment]

theorem graph_kind_enumerate_no_duplicates :
    ∀ (leftIndex rightIndex)
      (leftBound : leftIndex < graphKindEnumerate.length)
      (rightBound : rightIndex < graphKindEnumerate.length),
      graphKindEnumerate[leftIndex]'leftBound =
          graphKindEnumerate[rightIndex]'rightBound →
      leftIndex = rightIndex := by
  intro leftIndex rightIndex leftBound rightBound equalKind
  have leftCases : leftIndex = 0 ∨ leftIndex = 1 := by
    simp [graphKindEnumerate] at leftBound
    omega
  have rightCases : rightIndex = 0 ∨ rightIndex = 1 := by
    simp [graphKindEnumerate] at rightBound
    omega
  rcases leftCases with rfl | rfl <;>
    rcases rightCases with rfl | rfl <;>
    simp [graphKindEnumerate] at equalKind ⊢

theorem graph_kind_enumerate_complete (kind : GraphKind) :
    kind ∈ graphKindEnumerate := by
  cases kind <;> simp [graphKindEnumerate]

def graphKindCode : GraphKind → Nat
  | .syntax => 0
  | .judgment => 1

theorem graph_kind_code_injective :
    ∀ {left right},
      graphKindCode left = graphKindCode right → left = right := by
  intro left right equalCode
  cases left <;> cases right <;> simp [graphKindCode] at equalCode ⊢

def graphKindAddressKind : GraphKind → AddressKind
  | .syntax => .syntax
  | .judgment => .judgment

theorem graph_kind_address_kind_injective :
    ∀ {left right},
      graphKindAddressKind left = graphKindAddressKind right → left = right := by
  intro left right equalKind
  cases left <;> cases right <;> simp [graphKindAddressKind] at equalKind ⊢

def graphKindSchema : GraphKindSchema where
  Kind := GraphKind
  decideKindEq := fun left right => inferInstanceAs (Decidable (left = right))
  enumerate := graphKindEnumerate
  enumerateNoDuplicates := graph_kind_enumerate_no_duplicates
  enumerateComplete := graph_kind_enumerate_complete
  kindCode := graphKindCode
  kindCodeInjective := graph_kind_code_injective
  toAddressKind := graphKindAddressKind
  toAddressKindInjective := graph_kind_address_kind_injective

theorem graph_bytes_carrier_contract :
    GraphBytes = List Nat := by
  rfl

def graphText (scalars : List Char) : GraphText :=
  { scalars := scalars }

theorem graph_text_exact_carrier_contract :
    (graphText ['g', 'r', 'a', 'p', 'h']).scalars =
      ['g', 'r', 'a', 'p', 'h'] := by
  rfl

theorem graph_text_value_contract :
    (graphText ['g', 'r', 'a', 'p', 'h']).value = "graph" := by
  rfl

/-! ## Exact structural frames and readable bindings -/

def structuralGraphFrame :
    ExactFrame GraphBytes (DigestPreimage GraphBytes) where
  encode := fun preimage => preimage
  encode_injective := by
    intro left right equalWire
    exact equalWire

def graphKindName : GraphKind → String
  | .syntax => "syntax"
  | .judgment => "judgment"

def fixtureReadableText : GraphText :=
  graphText
    ['f', 'i', 'x', 't', 'u', 'r', 'e', '-', 'r', 'e', 'a', 'd', 'a', 'b',
      'l', 'e']

def fixtureOtherText : GraphText :=
  graphText
    ['f', 'i', 'x', 't', 'u', 'r', 'e', '-', 'o', 't', 'h', 'e', 'r']

def graphBlockDomainText : GraphKind → GraphText
  | .syntax =>
      graphText
        ['r', 'e', 's', 'i', 'd', 'u', 'a', ':', 'a', 'k', '6', ':', 'b',
          'l', 'o', 'c', 'k', ':', 's', 'y', 'n', 't', 'a', 'x']
  | .judgment =>
      graphText
        ['r', 'e', 's', 'i', 'd', 'u', 'a', ':', 'a', 'k', '6', ':', 'b',
          'l', 'o', 'c', 'k', ':', 'j', 'u', 'd', 'g', 'm', 'e', 'n', 't']

def graphOtherDomainText : GraphText :=
  graphText
    ['r', 'e', 's', 'i', 'd', 'u', 'a', ':', 'a', 'k', '6', ':', 'b', 'l',
      'o', 'c', 'k', ':', 'o', 't', 'h', 'e', 'r']

def graphBlockSchemaText : GraphText :=
  graphText
    ['r', 'e', 's', 'i', 'd', 'u', 'a', ':', 'a', 'k', '6', ':', 'b', 'l',
      'o', 'c', 'k', ':', 'v', '1']

def graphBlockOtherSchemaText : GraphText :=
  graphText
    ['r', 'e', 's', 'i', 'd', 'u', 'a', ':', 'a', 'k', '6', ':', 'b', 'l',
      'o', 'c', 'k', ':', 'v', '2']

def graphBytesScalars : GraphBytes → List Char
  | [] => []
  | byte :: rest =>
      List.replicate byte 'x' ++ ';' :: graphBytesScalars rest

def graphBlockDigestText
    (kind : GraphKind) (bytes : GraphBytes) : GraphText :=
  graphText
    ((match kind with
      | .syntax => ['s', 'y', 'n', 't', 'a', 'x', ':']
      | .judgment => ['j', 'u', 'd', 'g', 'm', 'e', 'n', 't', ':']) ++
      graphBytesScalars bytes)

def readableGraphDigest
    (digestPrefix : String) (preimage : DigestPreimage GraphBytes) : Digest :=
  ⟨digestPrefix ++ ":" ++ reprStr preimage.canonicalBytes⟩

def graphBlockBinding
    (kind : graphKindSchema.Kind) :
    DigestBinding
      (graphKindSchema.toAddressKind kind)
      GraphBytes
      (DigestPreimage GraphBytes) where
  algorithm := ⟨fixtureReadableText.value⟩
  domainQ := ⟨(graphBlockDomainText kind).value⟩
  schemaQ := ⟨graphBlockSchemaText.value⟩
  frame := structuralGraphFrame
  hash := fun preimage =>
    ⟨(graphBlockDigestText kind preimage.canonicalBytes).value⟩

def graphBlockWireAddress
    (kind : graphKindSchema.Kind) (bytes : GraphBytes) :
    GraphWireAddress (graphKindSchema.toAddressKind kind) where
  algorithm := fixtureReadableText
  domainQ := graphBlockDomainText kind
  schemaQ := graphBlockSchemaText
  digest := graphBlockDigestText kind bytes

theorem graph_block_wire_address_refines
    (kind : graphKindSchema.Kind) (bytes : GraphBytes) :
    (graphBlockWireAddress kind bytes).toAddress =
      (graphBlockBinding kind).address bytes := by
  rfl

def graphRootBinding :
    DigestBinding
      .implementation GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"fixture-readable"⟩
  domainQ := ⟨"residua:ak6:root"⟩
  schemaQ := ⟨"residua:ak6:root:v1"⟩
  frame := structuralGraphFrame
  hash := readableGraphDigest "root"

def syntaxAddressA : GraphWireAddress .syntax :=
  { algorithm := fixtureReadableText
    domainQ := graphBlockDomainText .syntax
    schemaQ := graphBlockSchemaText
    digest :=
      graphText
        ['s', 'y', 'n', 't', 'a', 'x', '-', 'a'] }

def syntaxAddressB : GraphWireAddress .syntax :=
  { algorithm := fixtureReadableText
    domainQ := graphBlockDomainText .syntax
    schemaQ := graphBlockSchemaText
    digest :=
      graphText
        ['s', 'y', 'n', 't', 'a', 'x', '-', 'b'] }

def syntaxAddressAlgorithmB : GraphWireAddress .syntax :=
  { syntaxAddressA with algorithm := fixtureOtherText }

def syntaxAddressDomainB : GraphWireAddress .syntax :=
  { syntaxAddressA with domainQ := graphOtherDomainText }

def syntaxAddressSchemaB : GraphWireAddress .syntax :=
  { syntaxAddressA with schemaQ := graphBlockOtherSchemaText }

def judgmentAddressA : GraphWireAddress .judgment :=
  { algorithm := fixtureReadableText
    domainQ := graphBlockDomainText .judgment
    schemaQ := graphBlockSchemaText
    digest :=
      graphText
        ['j', 'u', 'd', 'g', 'm', 'e', 'n', 't', '-', 'a'] }

theorem graph_wire_address_exact_type_contract :
    syntaxAddressA =
      ({ algorithm := fixtureReadableText
         domainQ := graphBlockDomainText .syntax
         schemaQ := graphBlockSchemaText
         digest :=
           graphText ['s', 'y', 'n', 't', 'a', 'x', '-', 'a'] } :
        GraphWireAddress .syntax) := by
  rfl

theorem graph_wire_address_to_address_contract :
    syntaxAddressA.toAddress =
      ({ algorithm := ⟨"fixture-readable"⟩
         domainQ := ⟨"residua:ak6:block:syntax"⟩
         schemaQ := ⟨"residua:ak6:block:v1"⟩
         digest := ⟨"syntax-a"⟩ } : Address .syntax) := by
  rfl

def syntaxExternalA : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressA
      canonicalLocalIndex := 0 }

def syntaxExternalB : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressB
      canonicalLocalIndex := 0 }

def syntaxExternalAlgorithmB : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressAlgorithmB
      canonicalLocalIndex := 0 }

def syntaxExternalDomainB : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressDomainB
      canonicalLocalIndex := 0 }

def syntaxExternalSchemaB : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressSchemaB
      canonicalLocalIndex := 0 }

def syntaxExternalIndexB : ExternalRef graphKindSchema where
  kind := .syntax
  target :=
    { blockQ := syntaxAddressA
      canonicalLocalIndex := 1 }

def judgmentExternalA : ExternalRef graphKindSchema where
  kind := .judgment
  target :=
    { blockQ := judgmentAddressA
      canonicalLocalIndex := 1 }

theorem syntax_fixture_addresses_differ :
    syntaxAddressA ≠ syntaxAddressB := by
  intro equalAddress
  have equalDigestValue :=
    congrArg (fun address => address.digest.value) equalAddress
  change "syntax-a" = "syntax-b" at equalDigestValue
  exact (by decide : "syntax-a" ≠ "syntax-b") equalDigestValue

theorem block_node_address_observation_contract :
    syntaxExternalA.target.address = syntaxAddressA.toAddress := by
  rfl

/-! ## Complete block grammar fixtures -/

abbrev FixtureCollection :=
  EdgeCollection graphKindSchema (ExternalRef graphKindSchema)

def childrenLabel : GraphLabel :=
  graphText ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n']

def premisesLabel : GraphLabel :=
  graphText ['p', 'r', 'e', 'm', 'i', 's', 'e', 's']

def backLabel : GraphLabel :=
  graphText ['b', 'a', 'c', 'k']

def xLabel : GraphLabel :=
  graphText ['x']

def uLabel : GraphLabel :=
  graphText ['u']

def edgeLabel : GraphLabel :=
  graphText ['e', 'd', 'g', 'e']

def parentsLabel : GraphLabel :=
  graphText ['p', 'a', 'r', 'e', 'n', 't', 's']

def orderedOutgoing :
    FixtureCollection :=
  .ordered childrenLabel .outgoing .syntax
    [.local 0, .external syntaxExternalA]

def orderedOutgoingReversed :
    FixtureCollection :=
  .ordered childrenLabel .outgoing .syntax
    [.external syntaxExternalA, .local 0]

def unorderedIncomingRepeatedTargets :
    FixtureCollection :=
  .unordered premisesLabel .incoming .judgment
    [.external judgmentExternalA, .external judgmentExternalA]

def completeNode : CanonicalNode graphKindSchema where
  payload := 7
  edgeCollections :=
    [orderedOutgoing, unorderedIncomingRepeatedTargets,
      unorderedIncomingRepeatedTargets]

def secondNode : CanonicalNode graphKindSchema where
  payload := 11
  edgeCollections :=
    [.ordered backLabel .outgoing .syntax [.local 0]]

def dagFixture : CanonicalBlock graphKindSchema .syntax :=
  .dagSingleton completeNode

def cyclicFixture : CanonicalBlock graphKindSchema .syntax :=
  .cyclic [completeNode, secondNode]

def emptyCyclicFixture : CanonicalBlock graphKindSchema .syntax :=
  .cyclic []

def outOfBoundsNode : CanonicalNode graphKindSchema where
  payload := 0
  edgeCollections :=
    [.ordered xLabel .outgoing .syntax [.local 9]]

def outOfBoundsLocalFixture : CanonicalBlock graphKindSchema .syntax :=
  .cyclic [outOfBoundsNode]

theorem ordered_accessor_contract :
    orderedOutgoing.mode = .ordered ∧
      orderedOutgoing.labelText = childrenLabel ∧
      orderedOutgoing.label = "children" ∧
      orderedOutgoing.direction = .outgoing ∧
      orderedOutgoing.expectedTargetKind = .syntax ∧
      orderedOutgoing.targets =
        [.local 0, .external syntaxExternalA] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem unordered_accessor_contract :
    unorderedIncomingRepeatedTargets.mode = .unordered ∧
      unorderedIncomingRepeatedTargets.labelText = premisesLabel ∧
      unorderedIncomingRepeatedTargets.label = "premises" ∧
      unorderedIncomingRepeatedTargets.direction = .incoming ∧
      unorderedIncomingRepeatedTargets.expectedTargetKind = .judgment ∧
      unorderedIncomingRepeatedTargets.targets =
        [.external judgmentExternalA, .external judgmentExternalA] := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-!
The following hand-derived byte strings pin the TLV grammar.  Expected bytes
do not call the encoder or any encoder helper.
-/

theorem dag_empty_collections_exact_bytes :
    encodeCanonicalBlock
        (CanonicalBlock.dagSingleton
          (schema := graphKindSchema) (sourceKind := .syntax)
          { payload := 7, edgeCollections := [] }) =
      [1, 8, 3, 6, 4, 1, 7, 13, 1, 0] := by
  decide

theorem empty_cyclic_exact_bytes :
    encodeCanonicalBlock emptyCyclicFixture =
      [2, 3, 13, 1, 0] := by
  decide

theorem encode_typed_address_contract :
    encodeTypedAddress graphKindSchema .syntax syntaxAddressA =
      [14, 75,
        10, 1, 0,
        16, 102, 105, 120, 116, 117, 114, 101, 45,
          114, 101, 97, 100, 97, 98, 108, 101,
        24, 114, 101, 115, 105, 100, 117, 97, 58,
          97, 107, 54, 58, 98, 108, 111, 99, 107, 58,
          115, 121, 110, 116, 97, 120,
        20, 114, 101, 115, 105, 100, 117, 97, 58,
          97, 107, 54, 58, 98, 108, 111, 99, 107, 58,
          118, 49,
        8, 115, 121, 110, 116, 97, 120, 45, 97] := by
  decide

def unorderedIncomingExternalTagFixture :
    CanonicalBlock graphKindSchema .syntax :=
  .dagSingleton
    { payload := 13
      edgeCollections :=
        [.unordered uLabel .incoming .judgment
          [.external judgmentExternalA]] }

/-!
This literal simultaneously pins the nested unordered-collection tag `6`,
incoming-direction tag `9`, external-reference tag `11`, and typed-address
tag `14`, including every enclosing element count and payload length.
-/
theorem unordered_incoming_external_nested_exact_bytes :
    encodeCanonicalBlock unorderedIncomingExternalTagFixture =
      [1, 110,
        3, 108,
        4, 1, 13,
        13, 103, 1, 101,
        6, 99,
        7, 2, 1, 117,
        9, 0,
        10, 1, 1,
        13, 88, 1, 86,
        11, 84,
        14, 79,
        10, 1, 1,
        16, 102, 105, 120, 116, 117, 114, 101, 45,
          114, 101, 97, 100, 97, 98, 108, 101,
        26, 114, 101, 115, 105, 100, 117, 97, 58,
          97, 107, 54, 58, 98, 108, 111, 99, 107, 58,
          106, 117, 100, 103, 109, 101, 110, 116,
        20, 114, 101, 115, 105, 100, 117, 97, 58,
          97, 107, 54, 58, 98, 108, 111, 99, 107, 58,
          118, 49,
        10, 106, 117, 100, 103, 109, 101, 110, 116, 45, 97,
        12, 1, 1] := by
  decide

theorem out_of_bounds_local_exact_bytes :
    encodeCanonicalBlock outOfBoundsLocalFixture =
      [2, 31,
        13, 29, 1, 27,
        3, 25,
        4, 1, 0,
        13, 20, 1, 18,
        5, 16,
        7, 2, 1, 120,
        8, 0,
        10, 1, 0,
        13, 5, 1, 3,
        12, 1, 9] := by
  decide

def singleCollectionBlock
    (payload : Nat) (collection : FixtureCollection) :
    CanonicalBlock graphKindSchema .syntax :=
  .dagSingleton
    { payload := payload
      edgeCollections := [collection] }

private def firstExternalDigest :
    CanonicalBlock graphKindSchema .syntax → String
  | .dagSingleton node =>
      match node.edgeCollections with
      | collection :: _ =>
          match collection.targets with
          | .external external :: _ =>
              external.target.blockQ.digest.value
          | _ => ""
      | _ => ""
  | .cyclic _ => ""

private def externalView
    (external : ExternalRef graphKindSchema) : List String :=
  [graphKindName external.kind,
    external.target.blockQ.algorithm.value,
    external.target.blockQ.domainQ.value,
    external.target.blockQ.schemaQ.value,
    external.target.blockQ.digest.value]

private def firstExternalView :
    CanonicalBlock graphKindSchema .syntax → List String
  | .dagSingleton node =>
      match node.edgeCollections with
      | collection :: _ =>
          match collection.targets with
          | .external external :: _ => externalView external
          | _ => []
      | _ => []
  | .cyclic _ => []

private def firstExternalIndex :
    CanonicalBlock graphKindSchema .syntax → Nat
  | .dagSingleton node =>
      match node.edgeCollections with
      | collection :: _ =>
          match collection.targets with
          | .external external :: _ =>
              external.target.canonicalLocalIndex
          | _ => 0
      | _ => 0
  | .cyclic _ => 0

private theorem unequal_blocks_have_unequal_bytes
    {left right : CanonicalBlock graphKindSchema .syntax}
    (different : left ≠ right) :
    encodeCanonicalBlock left ≠ encodeCanonicalBlock right := by
  intro equalBytes
  exact different
    (canonical_encode_injective
      (constructiveBlockCodec graphKindSchema .syntax) equalBytes)

private theorem external_view_change_has_unequal_bytes
    (left right : ExternalRef graphKindSchema)
    (different : externalView left ≠ externalView right) :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.external left])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.external right])) := by
  apply unequal_blocks_have_unequal_bytes
  intro equalBlock
  exact different (congrArg firstExternalView equalBlock)

theorem block_tag_changes_encoding :
    encodeCanonicalBlock
        (CanonicalBlock.dagSingleton
          (schema := graphKindSchema) (sourceKind := .syntax) completeNode) ≠
      encodeCanonicalBlock
        (CanonicalBlock.cyclic
          (schema := graphKindSchema) (sourceKind := .syntax) [completeNode]) := by
  apply unequal_blocks_have_unequal_bytes
  simp

theorem payload_changes_encoding :
    encodeCanonicalBlock (singleCollectionBlock 7 orderedOutgoing) ≠
      encodeCanonicalBlock (singleCollectionBlock 8 orderedOutgoing) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem label_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered childrenLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered parentsLabel .outgoing .syntax [.local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock, childrenLabel, parentsLabel, graphText]

theorem direction_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .incoming .syntax [.local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem expected_kind_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .judgment [.local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem collection_mode_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.unordered edgeLabel .outgoing .syntax [.local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem ordered_position_changes_encoding :
    encodeCanonicalBlock (singleCollectionBlock 7 orderedOutgoing) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7 orderedOutgoingReversed) := by
  apply unequal_blocks_have_unequal_bytes
  simp [
    singleCollectionBlock, orderedOutgoing, orderedOutgoingReversed,
    syntaxExternalA
  ]

theorem local_index_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 1])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem external_kind_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external judgmentExternalA])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [
    singleCollectionBlock, syntaxExternalA, judgmentExternalA,
    syntaxAddressA, judgmentAddressA
  ]

theorem address_envelope_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalB])) := by
  exact external_view_change_has_unequal_bytes
    syntaxExternalA syntaxExternalB (by decide)

theorem address_algorithm_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalAlgorithmB])) := by
  exact external_view_change_has_unequal_bytes
    syntaxExternalA syntaxExternalAlgorithmB (by decide)

theorem address_domain_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalDomainB])) := by
  exact external_view_change_has_unequal_bytes
    syntaxExternalA syntaxExternalDomainB (by decide)

theorem address_schema_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalSchemaB])) := by
  exact external_view_change_has_unequal_bytes
    syntaxExternalA syntaxExternalSchemaB (by decide)

theorem external_canonical_index_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalA])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax
            [.external syntaxExternalIndexB])) := by
  apply unequal_blocks_have_unequal_bytes
  intro equalBlock
  have equalIndex := congrArg firstExternalIndex equalBlock
  change (0 : Nat) = 1 at equalIndex
  exact (by decide : (0 : Nat) ≠ 1) equalIndex

theorem target_list_length_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.ordered edgeLabel .outgoing .syntax [.local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem target_multiplicity_changes_encoding :
    encodeCanonicalBlock
        (singleCollectionBlock 7
          (.unordered edgeLabel .outgoing .syntax [.local 0])) ≠
      encodeCanonicalBlock
        (singleCollectionBlock 7
          (.unordered edgeLabel .outgoing .syntax
            [.local 0, .local 0])) := by
  apply unequal_blocks_have_unequal_bytes
  simp [singleCollectionBlock]

theorem collection_multiplicity_changes_encoding :
    encodeCanonicalBlock
        (CanonicalBlock.dagSingleton
          (schema := graphKindSchema) (sourceKind := .syntax)
          { payload := 7
            edgeCollections := [orderedOutgoing] }) ≠
      encodeCanonicalBlock
        (CanonicalBlock.dagSingleton
          (schema := graphKindSchema) (sourceKind := .syntax)
          { payload := 7
            edgeCollections := [orderedOutgoing, orderedOutgoing] }) := by
  apply unequal_blocks_have_unequal_bytes
  simp

/-! ## Exact decoder residues -/

def unknownTagBytes : GraphBytes :=
  [99, 0]

def truncatedTlvBytes : GraphBytes :=
  [2]

def noncanonicalNaturalBytes : GraphBytes :=
  [2, 32,
    13, 30, 1, 28,
    3, 26,
    4, 1, 0,
    13, 21, 1, 19,
    5, 17,
    7, 2, 1, 120,
    8, 0,
    10, 1, 0,
    13, 6, 1, 4,
    12, 2, 0, 0]

def noncanonicalStringBytes : GraphBytes :=
  [2, 31,
    13, 29, 1, 27,
    3, 25,
    4, 1, 0,
    13, 20, 1, 18,
    5, 16,
    7, 2, 1, 55296,
    8, 0,
    10, 1, 0,
    13, 5, 1, 3,
    12, 1, 0]

def invalidKindCodeBytes : GraphBytes :=
  [2, 31,
    13, 29, 1, 27,
    3, 25,
    4, 1, 0,
    13, 20, 1, 18,
    5, 16,
    7, 2, 1, 120,
    8, 0,
    10, 1, 2,
    13, 5, 1, 3,
    12, 1, 0]

def unknownDirectionWithPayloadBytes : GraphBytes :=
  [2, 32,
    13, 30, 1, 28,
    3, 26,
    4, 1, 0,
    13, 21, 1, 19,
    5, 17,
    7, 2, 1, 120,
    99, 1, 0,
    10, 1, 0,
    13, 5, 1, 3,
    12, 1, 0]

def malformedNestedLengthBytes : GraphBytes :=
  [2, 31,
    13, 29, 1, 27,
    3, 25,
    4, 1, 0,
    13, 20, 1, 18,
    5, 16,
    7, 2, 1, 120,
    8, 0,
    10, 1, 0,
    13, 5, 1, 4,
    12, 1, 0]

def trailingDataBytes : GraphBytes :=
  [2, 3, 13, 1, 0, 0]

theorem decoder_unknown_tag_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax unknownTagBytes =
      .error .unknownTag := by
  rfl

theorem decoder_truncated_tlv_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax truncatedTlvBytes =
      .error .truncated := by
  rfl

theorem decoder_noncanonical_natural_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax noncanonicalNaturalBytes =
      .error .noncanonicalNatural := by
  rfl

theorem decoder_noncanonical_string_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax noncanonicalStringBytes =
      .error .noncanonicalString := by
  rfl

theorem decoder_invalid_kind_code_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax invalidKindCodeBytes =
      .error .invalidKindCode := by
  rfl

theorem decoder_unknown_direction_tag_precedes_payload_shape :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax unknownDirectionWithPayloadBytes =
      .error .unknownTag := by
  rfl

theorem decoder_malformed_nested_length_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax malformedNestedLengthBytes =
      .error .malformedLength := by
  rfl

theorem decoder_trailing_data_residue :
    decodeCanonicalBlockDetailed
        graphKindSchema .syntax trailingDataBytes =
      .error .trailingData := by
  rfl

/-! ## Exact block-codec laws and syntax-layer boundary -/

theorem block_decode_encode_contract
    (block : CanonicalBlock graphKindSchema kind) :
    decodeCanonicalBlockDetailed graphKindSchema kind
        (encodeCanonicalBlock block) =
      .ok block :=
  decode_encode_canonical_block graphKindSchema kind block

theorem block_prefix_encode_decode_contract
    (accepted :
      decodeCanonicalBlockPrefix graphKindSchema kind bytes =
        .ok (block, suffix)) :
    encodeCanonicalBlock block ++ suffix = bytes :=
  encode_decode_canonical_block_prefix accepted

theorem block_encode_decode_contract
    (accepted :
      decodeCanonicalBlockDetailed graphKindSchema kind bytes = .ok block) :
    encodeCanonicalBlock block = bytes :=
  encode_decode_canonical_block accepted

theorem block_codec_injective_contract :
    ∀ {left right},
      (constructiveBlockCodec graphKindSchema kind).encode left =
          (constructiveBlockCodec graphKindSchema kind).encode right →
        left = right :=
  by
    intro left right equalBytes
    exact
      canonical_encode_injective
        (constructiveBlockCodec graphKindSchema kind) equalBytes

theorem empty_cyclic_syntax_decodes :
    decodeCanonicalBlockDetailed graphKindSchema .syntax
        (encodeCanonicalBlock emptyCyclicFixture) =
      .ok emptyCyclicFixture :=
  block_decode_encode_contract emptyCyclicFixture

theorem out_of_bounds_local_selector_syntax_decodes :
    decodeCanonicalBlockDetailed graphKindSchema .syntax
        (encodeCanonicalBlock outOfBoundsLocalFixture) =
      .ok outOfBoundsLocalFixture :=
  block_decode_encode_contract outOfBoundsLocalFixture

/-! ## Pure context, digest profile, and raw-ingest refinement boundary -/

def graphCodecContext : GraphCodecContext where
  kindSchema := graphKindSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := graphBlockBinding
  blockWireAddress := graphBlockWireAddress
  blockWireAddressRefines := graph_block_wire_address_refines
  rootBinding := graphRootBinding

theorem graph_digest_injective_block_contract
    (profile : GraphDigestInjective graphCodecContext)
    (kind : graphCodecContext.kindSchema.Kind) :
    DigestInjectiveOnCanonicalRange
      (graphCodecContext.blockBinding kind) :=
  profile.block kind

theorem graph_digest_injective_root_contract
    (profile : GraphDigestInjective graphCodecContext) :
    DigestInjectiveOnCanonicalRange graphCodecContext.rootBinding :=
  profile.root

noncomputable def honestBlockRuntimeCodec
    (kind : graphCodecContext.kindSchema.Kind) :
    RuntimeCanonicalCodec
      (CanonicalBlock graphCodecContext.kindSchema kind)
      GraphBytes where
  encode :=
    (constructiveBlockCodec graphCodecContext.kindSchema kind).encode
  decode :=
    (constructiveBlockCodec graphCodecContext.kindSchema kind).decode

noncomputable def honestBlockRuntimeRefines
    (kind : graphCodecContext.kindSchema.Kind) :
    (honestBlockRuntimeCodec kind).RefinesExact
      (constructiveBlockCodec graphCodecContext.kindSchema kind) where
  encode_eq := rfl
  decode_eq := rfl

def emptyBlockStore
    (kind : graphCodecContext.kindSchema.Kind) :
    AddressedStore
      (graphCodecContext.kindSchema.toAddressKind kind)
      GraphBytes :=
  fun _ => none

noncomputable def honestRawIngestProfile : RawIngestProfile graphCodecContext where
  blockRuntimeCodec := honestBlockRuntimeCodec
  blockRuntimeRefines := honestBlockRuntimeRefines
  blockStore := emptyBlockStore

theorem raw_ingest_refinement_contract
    (kind : graphCodecContext.kindSchema.Kind) :
    (honestRawIngestProfile.blockRuntimeCodec kind).RefinesExact
      (constructiveBlockCodec graphCodecContext.kindSchema kind) :=
  honestRawIngestProfile.blockRuntimeRefines kind

/-!
`GraphCodecContext` fixes the constructive block codec outside caller input.
Adding a caller-selected codec field must remain ill-typed.
-/
#check_failure
  ({ kindSchema := graphKindSchema
     BlockWire := DigestPreimage GraphBytes
     RootWire := DigestPreimage GraphBytes
     blockCodec := fun kind =>
       constructiveBlockCodec graphKindSchema kind
     blockBinding := graphBlockBinding
     blockWireAddress := graphBlockWireAddress
     blockWireAddressRefines := graph_block_wire_address_refines
     rootBinding := graphRootBinding } : GraphCodecContext)

/-!
The address-kind index is authoritative: a judgment wire address cannot be
encoded or installed where the closed schema selects syntax.
-/
#check_failure
  encodeTypedAddress graphKindSchema .syntax judgmentAddressA

#check_failure
  ({ blockQ := judgmentAddressA
     canonicalLocalIndex := 0 } :
    BlockNodeAddress graphKindSchema .syntax)

def wrongDomainBlockWireAddress
    (kind : graphKindSchema.Kind) (bytes : GraphBytes) :
    GraphWireAddress (graphKindSchema.toAddressKind kind) :=
  { graphBlockWireAddress kind bytes with
    domainQ := graphOtherDomainText }

def wrongSchemaBlockWireAddress
    (kind : graphKindSchema.Kind) (bytes : GraphBytes) :
    GraphWireAddress (graphKindSchema.toAddressKind kind) :=
  { graphBlockWireAddress kind bytes with
    schemaQ := graphBlockOtherSchemaText }

/-!
The context refinement bridge also rejects constructive envelopes whose
domain or schema observation differs from the reused AK-3 binding.
-/
#check_failure
  ({ kindSchema := graphKindSchema
     BlockWire := DigestPreimage GraphBytes
     RootWire := DigestPreimage GraphBytes
     blockBinding := graphBlockBinding
     blockWireAddress := wrongDomainBlockWireAddress
     blockWireAddressRefines := graph_block_wire_address_refines
     rootBinding := graphRootBinding } : GraphCodecContext)

#check_failure
  ({ kindSchema := graphKindSchema
     BlockWire := DigestPreimage GraphBytes
     RootWire := DigestPreimage GraphBytes
     blockBinding := graphBlockBinding
     blockWireAddress := wrongSchemaBlockWireAddress
     blockWireAddressRefines := graph_block_wire_address_refines
     rootBinding := graphRootBinding } : GraphCodecContext)

def unrelatedNatCodec : ExactCanonicalCodec Nat GraphBytes where
  encode := fun value => [value]
  decode := fun bytes =>
    match bytes with
    | [value] => some value
    | _ => none
  decode_encode := by
    intro value
    rfl
  encode_decode_canonical := by
    intro bytes value accepted
    cases bytes with
    | nil => simp at accepted
    | cons first rest =>
        cases rest with
        | nil =>
            simp at accepted
            cases accepted
            rfl
        | cons second rest =>
            simp at accepted

/-!
The refinement field is definitionally tied to `constructiveBlockCodec`.
Substituting an unrelated exact codec must not elaborate as a raw profile.
-/
#check_failure
  ({ blockRuntimeCodec := honestBlockRuntimeCodec
     blockRuntimeRefines := fun kind =>
       show
         (honestBlockRuntimeCodec kind).RefinesExact unrelatedNatCodec
       from honestBlockRuntimeRefines kind
     blockStore := emptyBlockStore } : RawIngestProfile graphCodecContext)

#print axioms graphKindSchema
#print axioms graph_text_value_contract
#print axioms graph_wire_address_to_address_contract
#print axioms block_node_address_observation_contract
#print axioms ordered_accessor_contract
#print axioms graph_block_wire_address_refines
#print axioms dag_empty_collections_exact_bytes
#print axioms block_codec_injective_contract
#print axioms graphCodecContext
#print axioms honestRawIngestProfile
#print axioms decode_encode_canonical_block
#print axioms encode_decode_canonical_block

end Residua.RCC.Addressing.AddressedGraph.Foundation.Tests


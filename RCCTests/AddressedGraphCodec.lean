import RCC.AddressedGraphCodec

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph

namespace Residua.RCC.Addressing.AddressedGraph.Codec.Tests

set_option linter.deprecated false

/-! A concrete injective digest context makes every byte observation inhabited. -/

inductive ByteToken
  | digit
  | separator
  deriving DecidableEq

def tokenChar : ByteToken → Char
  | .digit => 'x'
  | .separator => ';'

def tokenByte : ByteToken → UInt8
  | .digit => 120
  | .separator => 59

def byteTokens : GraphBytes → List ByteToken
  | [] => []
  | byte :: rest =>
      List.replicate byte .digit ++ .separator :: byteTokens rest

def decodeCell : List ByteToken → Option (Nat × List ByteToken)
  | [] => none
  | .digit :: rest =>
      match decodeCell rest with
      | none => none
      | some (value, suffix) => some (value + 1, suffix)
  | .separator :: rest => some (0, rest)

theorem decode_cell
    (value : Nat) (suffix : List ByteToken) :
    decodeCell
        (List.replicate value .digit ++ .separator :: suffix) =
      some (value, suffix) := by
  induction value with
  | zero => rfl
  | succ value inductionHypothesis =>
      simp [List.replicate_succ, decodeCell, inductionHypothesis]

theorem byte_tokens_injective :
    ∀ {left right}, byteTokens left = byteTokens right → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons value rest =>
          simp [byteTokens] at equal
  | cons value rest inductionHypothesis =>
      intro right equal
      cases right with
      | nil => simp [byteTokens] at equal
      | cons other tail =>
          have decoded := congrArg decodeCell equal
          simp only [byteTokens] at decoded
          rw [decode_cell, decode_cell] at decoded
          have pairEqual :
              (value, byteTokens rest) = (other, byteTokens tail) :=
            Option.some.inj decoded
          have valueEqual := congrArg Prod.fst pairEqual
          have restEqual := congrArg Prod.snd pairEqual
          cases valueEqual
          exact congrArg (List.cons value)
            (inductionHypothesis restEqual)

theorem token_utf8_flatMap : ∀ tokens : List ByteToken,
    (tokens.map tokenChar).flatMap String.utf8EncodeChar =
      tokens.map tokenByte := by
  intro tokens
  induction tokens with
  | nil => rfl
  | cons token rest inductionHypothesis =>
      cases token <;>
        simp [tokenChar, tokenByte, String.utf8EncodeChar,
          inductionHypothesis] <;> decide

theorem token_toUTF8_data (tokens : List ByteToken) :
    (String.toUTF8 (tokens.map tokenChar).asString).data.toList =
      tokens.map tokenByte := by
  rw [← token_utf8_flatMap tokens]
  first
  | rfl
  | (change
        (String.ofList (tokens.map tokenChar)).toByteArray.data.toList =
          _
     rw [String.toByteArray_ofList]
     simp [List.utf8Encode])

theorem token_byte_injective
    {left right : ByteToken}
    (equal : tokenByte left = tokenByte right) :
    left = right := by
  cases left <;> cases right <;> simp [tokenByte] at equal ⊢

theorem token_bytes_injective :
    ∀ {left right : List ByteToken},
      left.map tokenByte = right.map tokenByte → left = right := by
  intro left
  induction left with
  | nil =>
      intro right equality
      cases right <;> simp_all
  | cons token rest inductionHypothesis =>
      intro right equality
      cases right with
      | nil => simp at equality
      | cons other tail =>
          simp only [List.map] at equality
          injection equality with headEquality tailEquality
          cases token_byte_injective headEquality
          exact congrArg (List.cons token)
            (inductionHypothesis tailEquality)

def fixtureSchema : GraphKindSchema where
  Kind := Unit
  decideKindEq := fun left right => inferInstanceAs (Decidable (left = right))
  enumerate := [()]
  enumerateNoDuplicates := by
    intro left right leftBound rightBound _
    simp at leftBound rightBound
    omega
  enumerateComplete := by simp
  kindCode := fun _ => 0
  kindCodeInjective := by intro left right _; cases left; cases right; rfl
  toAddressKind := fun _ => .syntax
  toAddressKindInjective := by
    intro left right _
    cases left
    cases right
    rfl

def frame : ExactFrame GraphBytes (DigestPreimage GraphBytes) where
  encode := fun bytes => bytes
  encode_injective := fun equality => equality

def blockBinding :
    DigestBinding .syntax GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"f"⟩
  domainQ := ⟨"b"⟩
  schemaQ := ⟨"v"⟩
  frame := frame
  hash := fun bytes =>
    ⟨((byteTokens bytes.canonicalBytes).map tokenChar).asString⟩

def text (value : List Char) : GraphText := ⟨value⟩
def blockWire (bytes : GraphBytes) : GraphWireAddress .syntax where
  algorithm := text ['f']
  domainQ := text ['b']
  schemaQ := text ['v']
  digest := ⟨(byteTokens bytes).map tokenChar⟩

theorem block_wire_refines (bytes : GraphBytes) :
    (blockWire bytes).toAddress = blockBinding.address bytes := rfl

def rootBinding :
    DigestBinding .implementation GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"f"⟩
  domainQ := ⟨"r"⟩
  schemaQ := ⟨"v"⟩
  frame := frame
  hash := fun bytes =>
    ⟨((byteTokens bytes.canonicalBytes).map tokenChar).asString⟩

def context : GraphCodecContext where
  kindSchema := fixtureSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := fun _ => blockBinding
  blockWireAddress := fun _ => blockWire
  blockWireAddressRefines := fun _ => block_wire_refines
  rootBinding := rootBinding

theorem block_injective :
    DigestInjectiveOnCanonicalRange blockBinding := by
  intro left right equal
  have stringEqual := congrArg Digest.value equal
  simp only [blockBinding, DigestBinding.framedWire,
    DigestBinding.preimage, frame] at stringEqual
  have utf8Equal := congrArg String.toUTF8 stringEqual
  have dataEqual :
      (String.toUTF8
        ((byteTokens left).map tokenChar).asString).data.toList =
      (String.toUTF8
        ((byteTokens right).map tokenChar).asString).data.toList :=
    congrArg (fun bytes : ByteArray => bytes.data.toList) utf8Equal
  rw [token_toUTF8_data, token_toUTF8_data] at dataEqual
  have tokenEqual := token_bytes_injective dataEqual
  have bytesEqual := byte_tokens_injective tokenEqual
  cases bytesEqual
  rfl

theorem root_injective :
    DigestInjectiveOnCanonicalRange rootBinding := by
  intro left right equal
  have stringEqual := congrArg Digest.value equal
  simp only [rootBinding, DigestBinding.framedWire,
    DigestBinding.preimage, frame] at stringEqual
  have utf8Equal := congrArg String.toUTF8 stringEqual
  have dataEqual :
      (String.toUTF8
        ((byteTokens left).map tokenChar).asString).data.toList =
      (String.toUTF8
        ((byteTokens right).map tokenChar).asString).data.toList :=
    congrArg (fun bytes : ByteArray => bytes.data.toList) utf8Equal
  rw [token_toUTF8_data, token_toUTF8_data] at dataEqual
  have tokenEqual := token_bytes_injective dataEqual
  have bytesEqual := byte_tokens_injective tokenEqual
  cases bytesEqual
  rfl

def judgmentBlockBinding :
    DigestBinding .judgment GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"f"⟩
  domainQ := ⟨"j"⟩
  schemaQ := ⟨"v"⟩
  frame := frame
  hash := fun bytes =>
    ⟨((byteTokens bytes.canonicalBytes).map tokenChar).asString⟩

def judgmentBlockWire
    (bytes : GraphBytes) : GraphWireAddress .judgment where
  algorithm := text ['f']
  domainQ := text ['j']
  schemaQ := text ['v']
  digest := ⟨(byteTokens bytes).map tokenChar⟩

theorem judgment_block_injective :
    DigestInjectiveOnCanonicalRange judgmentBlockBinding := by
  intro left right equal
  have stringEqual := congrArg Digest.value equal
  simp only [judgmentBlockBinding, DigestBinding.framedWire,
    DigestBinding.preimage, frame] at stringEqual
  have utf8Equal := congrArg String.toUTF8 stringEqual
  have dataEqual :
      (String.toUTF8
        ((byteTokens left).map tokenChar).asString).data.toList =
      (String.toUTF8
        ((byteTokens right).map tokenChar).asString).data.toList :=
    congrArg (fun bytes : ByteArray => bytes.data.toList) utf8Equal
  rw [token_toUTF8_data, token_toUTF8_data] at dataEqual
  have tokenEqual := token_bytes_injective dataEqual
  have bytesEqual := byte_tokens_injective tokenEqual
  cases bytesEqual
  rfl

def injective : GraphDigestInjective context where
  block := fun _ => block_injective
  root := root_injective

inductive PairKind
  | source
  | target
  deriving DecidableEq

def pairSchema : GraphKindSchema where
  Kind := PairKind
  decideKindEq := fun left right =>
    inferInstanceAs (Decidable (left = right))
  enumerate := [.source, .target]
  enumerateNoDuplicates := by
    intro left right leftBound rightBound equal
    change left < 2 at leftBound
    change right < 2 at rightBound
    have leftCases : left = 0 ∨ left = 1 := by omega
    have rightCases : right = 0 ∨ right = 1 := by omega
    rcases leftCases with rfl | rfl <;>
      rcases rightCases with rfl | rfl <;>
      simp_all
  enumerateComplete := by
    intro kind
    cases kind <;> simp
  kindCode := fun
    | .source => 0
    | .target => 1
  kindCodeInjective := by
    intro left right equal
    cases left <;> cases right <;> simp_all
  toAddressKind := fun
    | .source => .syntax
    | .target => .judgment
  toAddressKindInjective := by
    intro left right equal
    cases left <;> cases right <;> simp_all

def pairContext : GraphCodecContext where
  kindSchema := pairSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := fun
    | .source => blockBinding
    | .target => judgmentBlockBinding
  blockWireAddress := fun
    | .source => blockWire
    | .target => judgmentBlockWire
  blockWireAddressRefines := by
    intro kind bytes
    cases kind <;> rfl
  rootBinding := rootBinding

def pairInjective : GraphDigestInjective pairContext where
  block := fun kind => by
    cases kind
    · exact block_injective
    · exact judgment_block_injective
  root := root_injective

/-! A proof-complete, store-free one-block graph is the positive corpus root. -/
def positiveNode : CanonicalNode fixtureSchema :=
  { payload := 1, edgeCollections := [] }

def positiveBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton positiveNode

def positiveEntry : SomeCanonicalBlock context :=
  { kind := ()
    blockQ := blockWire (encodeCanonicalBlock positiveBlock)
    block := positiveBlock }

def positiveRegistry : List (SomeCanonicalBlock context) :=
  [positiveEntry]

theorem positive_collection_impossible
    (occurrence :
      CanonicalCollectionOccurrence positiveBlock.nodes) :
    False := by
  have nodeBound :
      occurrence.sourceNodeIndex < positiveBlock.nodes.length := by
    exact list_get?_some_bound occurrence.sourceNodeLookup
  have nodeIndexZero : occurrence.sourceNodeIndex = 0 := by
    change occurrence.sourceNodeIndex < 1 at nodeBound
    omega
  have nodeExact : occurrence.sourceNode = positiveNode := by
    have lookup := occurrence.sourceNodeLookup
    change
      listGet? [positiveNode] occurrence.sourceNodeIndex =
        some occurrence.sourceNode at lookup
    rw [nodeIndexZero] at lookup
    exact Option.some.inj lookup.symm
  have collectionLookup := occurrence.owningCollectionLookup
  rw [nodeExact] at collectionLookup
  simp [positiveNode, listGet?] at collectionLookup

theorem positive_block_well_formed :
    CanonicalBlockWellFormed positiveBlock := by
  constructor
  · intro occurrence
    exact False.elim
      (positive_collection_impossible
        occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    exact False.elim
      (positive_collection_impossible
        occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    exact False.elim
      (positive_collection_impossible
        occurrence.toCanonicalCollectionOccurrence)
  · intro occurrence
    intro _
    exact False.elim (positive_collection_impossible occurrence)
  · intro node member
    have nodeExact : node = positiveNode := by
      change node ∈ [positiveNode] at member
      simpa using member
    subst node
    rfl
  · exact decode_encode_canonical_block fixtureSchema () positiveBlock

theorem positive_registry_well_formed :
    CanonicalRegistryWellFormed context positiveRegistry := by
  constructor
  intro index
  have indexBound := index.isLt
  have indexZero : index = ⟨0, by decide⟩ := by
    change index.val < 1 at indexBound
    apply Fin.ext
    change index.val = 0
    omega
  subst index
  exact positive_block_well_formed

theorem positive_registry_has_no_public_occurrence
    (occurrence : PublicReferenceOccurrence positiveRegistry) :
    False := by
  have sourceBound := occurrence.sourceBlockBound
  have sourceIndexZero : occurrence.sourceBlockIndex = 0 := by
    simp [positiveRegistry] at sourceBound
    omega
  have sourceExact : occurrence.sourceBlock = positiveEntry := by
    simpa [positiveRegistry, sourceIndexZero, listGet?] using
      occurrence.sourceBlockLookup.symm
  have nodeLookup := occurrence.sourceNodeLookup
  rw [sourceExact] at nodeLookup
  have nodeBound :=
    list_get?_some_bound occurrence.sourceNodeLookup
  rw [sourceExact] at nodeBound
  have nodeIndexZero : occurrence.sourceNodeIndex = 0 := by
    change occurrence.sourceNodeIndex < 1 at nodeBound
    omega
  have nodeExact : occurrence.sourceNode = positiveNode := by
    change
      listGet? [positiveNode] occurrence.sourceNodeIndex =
        some occurrence.sourceNode at nodeLookup
    rw [nodeIndexZero] at nodeLookup
    exact Option.some.inj nodeLookup.symm
  have collectionLookup := occurrence.owningCollectionLookup
  rw [nodeExact] at collectionLookup
  simp [positiveNode, listGet?] at collectionLookup

def positiveKeysNoDup :
    CanonicalRegistryKeysNoDup context positiveRegistry := by
  simp [CanonicalRegistryKeysNoDup, positiveRegistry]

def positiveResolvedEdges :
    ResolvedEdgeTable positiveRegistry positiveKeysNoDup where
  edges := []
  sound := by simp
  complete := by
    intro occurrence
    exact False.elim (positive_registry_has_no_public_occurrence occurrence)
  occurrenceNoDuplicates := by
    simp [NoDuplicateOccurrenceIdentity]

def positiveDependency :
    DependencyCertificate positiveResolvedEdges where
  height := fun _ => 0
  indexBound := by
    intro index indexBound
    simp [positiveRegistry]
  decreases := by
    intro source target reference
    rcases reference with ⟨edge, member, _⟩
    simp [positiveResolvedEdges] at member

def positiveGraph : ClosedRootedGraph context where
  canonicalRegistry := positiveRegistry
  canonicalRoot :=
    { blockIndex := 0
      blockBound := by decide
      localIndex := 0
      localBound := by decide }
  registryStrictlySorted := by
    simp [CanonicalRegistryStrictOrder, positiveRegistry]
  registryKeysNoDup := positiveKeysNoDup
  registryWellFormed := positive_registry_well_formed
  connectivity := by
    intro entry member nodes cyclic
    simp [positiveRegistry] at member
    subst entry
    simp [positiveEntry, positiveBlock] at cyclic
  resolvedEdges := positiveResolvedEdges
  dependency := positiveDependency
  blockAddressesDerived := by
    intro entry member
    simp [positiveRegistry] at member
    subst entry
    rfl
  canonicalMinima := by
    intro entry member
    simp [positiveRegistry] at member
    subst entry
    exact .dagTrivial positiveNode rfl positive_block_well_formed

noncomputable def residue (bytes : GraphBytes) : Option GraphDecodeResidue :=
  match decodeCanonicalGraphDetailed context injective bytes with
  | .error refusal => some refusal
  | .ok _ => none

noncomputable def accepted (bytes : GraphBytes) : Bool :=
  match decodeCanonicalGraphDetailed context injective bytes with
  | .error _ => false
  | .ok _ => true

/-! Real graph envelopes exercise the production TLV parser. -/
def positiveBytes : GraphBytes :=
  encodeCanonicalGraph context positiveGraph

def testTlv (tag : Nat) (payload : GraphBytes) : GraphBytes :=
  [tag, payload.length] ++ payload

def testEncodeGraphText (value : GraphText) : GraphBytes :=
  value.scalars.length :: value.scalars.map Char.toNat

def testEncodeWireAddress
    (address : GraphWireAddress kind) : GraphBytes :=
  testEncodeGraphText address.algorithm ++
    testEncodeGraphText address.domainQ ++
    testEncodeGraphText address.schemaQ ++
    testEncodeGraphText address.digest

def testEncodeRegistryEntry
    (entry : SomeCanonicalBlock context) : GraphBytes :=
  testTlv 34
    (testTlv 35 [fixtureSchema.kindCode entry.kind] ++
      testTlv 36 (testEncodeWireAddress entry.blockQ) ++
      testTlv 37 (encodeCanonicalBlock entry.block))

def testEncodePairRegistryEntry
    (entry : SomeCanonicalBlock pairContext) : GraphBytes :=
  testTlv 34
    (testTlv 35 [pairSchema.kindCode entry.kind] ++
      testTlv 36 (testEncodeWireAddress entry.blockQ) ++
      testTlv 37 (encodeCanonicalBlock entry.block))

def testEncodeRoot
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (address : GraphWireAddress (schema.toAddressKind kind))
    (localIndex : Nat) : GraphBytes :=
  testTlv 38
    (testTlv 39
        (testTlv 35 [schema.kindCode kind] ++
          testTlv 36 (testEncodeWireAddress address)) ++
      testTlv 40 [localIndex])

def positiveEntryBytes : GraphBytes :=
  (positiveBytes.drop 6).take 74

def positiveRootBytes : GraphBytes :=
  positiveBytes.drop (6 + positiveEntryBytes.length)

def testRegistryEntries (entries : List GraphBytes) : GraphBytes :=
  entries.flatMap (fun entry => entry.length :: entry)

def graphWithEntries (entries : List GraphBytes) : GraphBytes :=
  testTlv 32
    (testTlv 33 (entries.length :: testRegistryEntries entries) ++
      positiveRootBytes)

def alternateNode : CanonicalNode fixtureSchema :=
  { payload := 2, edgeCollections := [] }

def alternateBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton alternateNode

def alternateEntry : SomeCanonicalBlock context :=
  { kind := ()
    blockQ := blockWire (encodeCanonicalBlock alternateBlock)
    block := alternateBlock }

def alternateEntryBytes : GraphBytes :=
  testEncodeRegistryEntry alternateEntry

def alternateEntrySameKeyBytes : GraphBytes :=
  let payload := positiveEntryBytes.drop 2
  let oldBlockFrameLength :=
    2 + (encodeCanonicalBlock positiveBlock).length
  let addressPrefix :=
    payload.take (payload.length - oldBlockFrameLength)
  testTlv 34
    (addressPrefix ++
      testTlv 37 (encodeCanonicalBlock alternateBlock))

def duplicateIdenticalPayloadBytes : GraphBytes :=
  graphWithEntries [positiveEntryBytes, positiveEntryBytes]

def duplicateDistinctPayloadBytes : GraphBytes :=
  graphWithEntries [positiveEntryBytes, alternateEntrySameKeyBytes]

def invalidKindBytes : GraphBytes :=
  positiveBytes.set 10 1

def noncanonicalStringBytes : GraphBytes :=
  positiveBytes.set 14 1114112

def noncanonicalBlockEnvelopeBytes : GraphBytes :=
  positiveBytes.set 68 99

def unknownBlockTagBytes : GraphBytes :=
  positiveBytes.set 70 99

def missingRootEnvelopeBytes : GraphBytes :=
  positiveBytes.set 80 99

def descendingUniqueRegistryBytes : GraphBytes :=
  graphWithEntries [alternateEntryBytes, positiveEntryBytes]

def blockAddressMismatchEntry : SomeCanonicalBlock context :=
  { kind := ()
    blockQ := blockWire (encodeCanonicalBlock alternateBlock)
    block := positiveBlock }

def blockAddressMismatchBytes : GraphBytes :=
  graphWithEntries [testEncodeRegistryEntry blockAddressMismatchEntry]

def rootAddressSuffixBytes : GraphBytes :=
  positiveBytes.set 83 61

def rootMemberOutOfBoundsBytes : GraphBytes :=
  positiveBytes.set (positiveBytes.length - 1) 1

def bytesForUncheckedBlock
    (block : CanonicalBlock fixtureSchema ()) : GraphBytes :=
  let entry : SomeCanonicalBlock context :=
    { kind := ()
      blockQ := blockWire (encodeCanonicalBlock block)
      block }
  graphWithEntries [testEncodeRegistryEntry entry]

def bytesForPreAddressBlock
    (block : CanonicalBlock fixtureSchema ()) : GraphBytes :=
  let entry : SomeCanonicalBlock context :=
    { kind := ()
      blockQ :=
        { algorithm := text []
          domainQ := text []
          schemaQ := text []
          digest := text ['x'] }
      block }
  graphWithEntries [testEncodeRegistryEntry entry]

def rootedBytesForUncheckedBlock
    (block : CanonicalBlock fixtureSchema ()) : GraphBytes :=
  let entry : SomeCanonicalBlock context :=
    { kind := ()
      blockQ := blockWire (encodeCanonicalBlock block)
      block }
  let entryBytes := testEncodeRegistryEntry entry
  let rootBytes :=
    testEncodeRoot fixtureSchema () entry.blockQ 0
  testTlv 32
    (testTlv 33
        (1 :: entryBytes.length :: entryBytes) ++
      rootBytes)

def localCollection (target : Nat) :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .ordered (text ['l', 'o', 'c', 'a', 'l']) .outgoing () [.local target]

def dagLocalReferenceBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections := [localCollection 0] }

def cyclicOutOfBoundsBlock : CanonicalBlock fixtureSchema () :=
  .cyclic
    [{ payload := 1
       edgeCollections := [localCollection 1] }]

def disconnectedCyclicBlock : CanonicalBlock fixtureSchema () :=
  .cyclic
    [{ payload := 1, edgeCollections := [] },
     { payload := 2, edgeCollections := [] }]

def shortBlockWire : GraphWireAddress .syntax :=
  { algorithm := text []
    domainQ := text []
    schemaQ := text []
    digest := text ['x'] }

def shortBlockWireNamed (digest : List Char) :
    GraphWireAddress .syntax :=
  { algorithm := text []
    domainQ := text []
    schemaQ := text []
    digest := text digest }

def externalAt (index : Nat) : ExternalRef fixtureSchema :=
  { kind := ()
    target :=
      { blockQ := shortBlockWire
        canonicalLocalIndex := index } }

def externalTo
    (address : GraphWireAddress .syntax)
    (index : Nat) : ExternalRef fixtureSchema :=
  { kind := ()
    target :=
      { blockQ := address
        canonicalLocalIndex := index } }

def unorderedTargetsBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.unordered (text ['e', 'd', 'g', 'e']) .outgoing ()
          [.external (externalAt 1),
           .external (externalAt 0)]] }

def outerCollectionsBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.ordered (text ['z']) .outgoing () [],
         .ordered (text ['a']) .outgoing () []] }

def missingTargetBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.ordered (text ['e', 'd', 'g', 'e']) .outgoing ()
          [.external
            (externalTo
              (shortBlockWireNamed ['m', 'i', 's', 's', 'i', 'n', 'g'])
              0)]] }

def memberOutOfBoundsBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.ordered (text ['e', 'd', 'g', 'e']) .outgoing ()
          [.external (externalAt 1)]] }

def cycleAddressA : GraphWireAddress .syntax :=
  shortBlockWireNamed ['a']

def cycleAddressB : GraphWireAddress .syntax :=
  shortBlockWireNamed ['b']

def cycleBlockA : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.ordered (text ['e', 'd', 'g', 'e']) .outgoing ()
          [.external (externalTo cycleAddressB 0)]] }

def cycleBlockB : CanonicalBlock fixtureSchema () :=
  .dagSingleton
    { payload := 2
      edgeCollections :=
        [.ordered (text ['e', 'd', 'g', 'e']) .outgoing ()
          [.external (externalTo cycleAddressA 0)]] }

def cycleEntryA : SomeCanonicalBlock context :=
  { kind := (), blockQ := cycleAddressA, block := cycleBlockA }

def cycleEntryB : SomeCanonicalBlock context :=
  { kind := (), blockQ := cycleAddressB, block := cycleBlockB }

def twoCycleNode
    (payload target : Nat) : CanonicalNode fixtureSchema :=
  { payload
    edgeCollections :=
      [.ordered (text []) .outgoing ()
        [.local target]] }

def symmetricTwoCycleBlock : CanonicalBlock fixtureSchema () :=
  .cyclic
    [twoCycleNode 1 1,
     twoCycleNode 1 0]

def nonminimumTwoCycleBlock : CanonicalBlock fixtureSchema () :=
  .cyclic
    [twoCycleNode 2 1,
     twoCycleNode 1 0]

def minimumTwoCycleBlock : CanonicalBlock fixtureSchema () :=
  .cyclic
    [twoCycleNode 1 1,
     twoCycleNode 2 0]

def dagLocalReferenceBytes : GraphBytes :=
  bytesForPreAddressBlock dagLocalReferenceBlock

def cyclicOutOfBoundsBytes : GraphBytes :=
  bytesForPreAddressBlock cyclicOutOfBoundsBlock

def disconnectedCyclicBytes : GraphBytes :=
  bytesForPreAddressBlock disconnectedCyclicBlock

def unnormalizedTargetsBytes : GraphBytes :=
  bytesForPreAddressBlock unorderedTargetsBlock

def unnormalizedCollectionsBytes : GraphBytes :=
  bytesForPreAddressBlock outerCollectionsBlock

def missingTargetBytes : GraphBytes :=
  bytesForPreAddressBlock missingTargetBlock

def memberOutOfBoundsBytes : GraphBytes :=
  bytesForPreAddressBlock memberOutOfBoundsBlock

def crossBlockCycleBytes : GraphBytes :=
  graphWithEntries
    [testEncodeRegistryEntry cycleEntryA,
     testEncodeRegistryEntry cycleEntryB]

def ambiguousCanonicalLabelBytes : GraphBytes :=
  bytesForPreAddressBlock symmetricTwoCycleBlock

def nonminimumCyclicBytes : GraphBytes :=
  bytesForPreAddressBlock nonminimumTwoCycleBlock

def canonicalTwoCycleBytes : GraphBytes :=
  rootedBytesForUncheckedBlock minimumTwoCycleBlock

def pairTargetAddress : GraphWireAddress .judgment :=
  judgmentBlockWire []

def pairMismatchExternal : ExternalRef pairSchema :=
  { kind := .target
    target :=
      { blockQ := pairTargetAddress
        canonicalLocalIndex := 0 } }

def pairMismatchBlock :
    CanonicalBlock pairSchema PairKind.source :=
  .dagSingleton
    { payload := 1
      edgeCollections :=
        [.ordered (text ['e', 'd', 'g', 'e']) .outgoing .source
          [.external pairMismatchExternal]] }

def pairMismatchEntry : SomeCanonicalBlock pairContext :=
  { kind := .source
    blockQ := blockWire (encodeCanonicalBlock pairMismatchBlock)
    block := pairMismatchBlock }

def pairLocalKindMismatchBlock :
    CanonicalBlock pairSchema PairKind.source :=
  .cyclic
    [{ payload := 1
       edgeCollections :=
        [.ordered (text ['l', 'o', 'c', 'a', 'l']) .outgoing .target
          [.local 0]] }]

def pairLocalKindMismatchEntry : SomeCanonicalBlock pairContext :=
  { kind := .source
    blockQ :=
      blockWire
        (encodeCanonicalBlock pairLocalKindMismatchBlock)
    block := pairLocalKindMismatchBlock }

def pairMismatchBytes : GraphBytes :=
  let entryBytes := testEncodePairRegistryEntry pairMismatchEntry
  let rootBytes :=
    testEncodeRoot pairSchema .source pairMismatchEntry.blockQ 0
  testTlv 32
    (testTlv 33
        (1 :: entryBytes.length :: entryBytes) ++
      rootBytes)

def pairLocalKindMismatchBytes : GraphBytes :=
  let entryBytes :=
    testEncodePairRegistryEntry pairLocalKindMismatchEntry
  let rootBytes :=
    testEncodeRoot pairSchema .source
      pairLocalKindMismatchEntry.blockQ 0
  testTlv 32
    (testTlv 33
        (1 :: entryBytes.length :: entryBytes) ++
      rootBytes)

noncomputable def pairResidue
    (bytes : GraphBytes) : Option GraphDecodeResidue :=
  match
      decodeCanonicalGraphDetailed
        pairContext pairInjective bytes with
  | .error refusal => some refusal
  | .ok _ => none

example : residue [99, 0] = some .unknownGraphTag := by decide
example : residue [] = some .truncatedEnvelope := by decide
example : residue [32] = some .truncatedEnvelope := by decide
example : residue [32, 1] = some .malformedEnvelopeLength := by decide
example :
    residue [32, 2, 33, 0] =
      some .noncanonicalNatural := by decide
example : residue [32, 0, 0] = some .trailingData := by decide
set_option maxRecDepth 100000 in
example :
    residue invalidKindBytes = some .invalidKindCode := by decide
set_option maxRecDepth 100000 in
example :
    residue noncanonicalStringBytes =
      some .noncanonicalString := by decide
set_option maxRecDepth 100000 in
example :
    residue noncanonicalBlockEnvelopeBytes =
      some .noncanonicalBlockTLV := by decide
set_option maxRecDepth 100000 in
example :
    residue unknownBlockTagBytes =
      some (.blockDecodeRefused .unknownTag) := by decide
set_option maxRecDepth 100000 in
example :
    residue missingRootEnvelopeBytes =
      some .rootNotInRegistry := by decide
set_option maxRecDepth 100000 in
example :
    residue descendingUniqueRegistryBytes =
      some .unsortedRegistry := by decide
set_option maxRecDepth 100000 in
example :
    residue blockAddressMismatchBytes =
      some .blockAddressMismatch := by decide
set_option maxRecDepth 100000 in
example :
    residue rootAddressSuffixBytes =
      some .rootBlockAddressMismatch := by decide
set_option maxRecDepth 100000 in
example :
    residue rootMemberOutOfBoundsBytes =
      some .rootMemberIndexOutOfBounds := by decide
set_option maxRecDepth 100000 in
example :
    residue dagLocalReferenceBytes =
      some .localRefInDag := by rfl
set_option maxRecDepth 100000 in
example :
    residue cyclicOutOfBoundsBytes =
      some .localIndexOutOfBounds := by rfl
set_option maxRecDepth 100000 in
example :
    residue disconnectedCyclicBytes =
      some .localConnectivityRefused := by rfl
set_option maxRecDepth 100000 in
example :
    residue unnormalizedTargetsBytes =
      some .unnormalizedUnorderedTargets := by rfl
set_option maxRecDepth 100000 in
example :
    residue unnormalizedCollectionsBytes =
      some .unnormalizedEdgeCollections := by rfl
set_option maxRecDepth 100000 in
example :
    residue missingTargetBytes =
      some .targetMissing := by rfl
set_option maxRecDepth 100000 in
example :
    residue memberOutOfBoundsBytes =
      some .canonicalMemberIndexOutOfBounds := by rfl
set_option maxRecDepth 100000 in
example :
    residue crossBlockCycleBytes =
      some .crossBlockCycle := by rfl
set_option maxRecDepth 100000 in
theorem ambiguous_canonical_label_refusal :
    residue ambiguousCanonicalLabelBytes =
      some .ambiguousCanonicalLabel := by rfl
set_option maxRecDepth 100000 in
example :
    residue nonminimumCyclicBytes =
      some .blockNotCanonicalMinimum := by rfl
set_option maxRecDepth 100000 in
theorem canonical_two_cycle_retains_minimum :
    ∃ decoded,
      decodeCanonicalGraphDetailed
          context injective canonicalTwoCycleBytes =
        .ok decoded ∧
      EveryBlockStoredAtCanonicalMinimum
        decoded.canonicalRegistry := by
  have acceptedExact :
      accepted canonicalTwoCycleBytes = true := by rfl
  cases decodedExact :
      decodeCanonicalGraphDetailed
        context injective canonicalTwoCycleBytes with
  | error residue =>
      simp [accepted, decodedExact] at acceptedExact
  | ok decoded =>
      exact
        ⟨decoded, rfl,
          decoded.canonicalMinima⟩

set_option maxRecDepth 100000 in
example :
    pairResidue pairMismatchBytes =
      some .targetKindMismatch := by rfl
set_option maxRecDepth 100000 in
example :
    pairResidue pairLocalKindMismatchBytes =
      some .localTargetKindMismatch := by rfl
set_option maxRecDepth 100000 in
example :
    duplicateIdenticalPayloadBytes ≠
      duplicateDistinctPayloadBytes := by decide
set_option maxRecDepth 100000 in
example :
    residue duplicateIdenticalPayloadBytes =
      some .duplicateRegistryKey := by decide
set_option maxRecDepth 100000 in
example :
    residue duplicateDistinctPayloadBytes =
      some .duplicateRegistryKey := by decide

example : accepted positiveBytes = true := by
  rcases
      decode_detailed_encode_observation
        context injective positiveGraph with
    ⟨decoded, acceptedExact, _⟩
  unfold accepted positiveBytes
  rw [acceptedExact]

theorem detailed_encode_observation_contract
    (graph : ClosedRootedGraph context) :
    ∃ decoded,
      decodeCanonicalGraphDetailed context injective
          (encodeCanonicalGraph context graph) = .ok decoded ∧
      serializedCanonicalProjection decoded =
        serializedCanonicalProjection graph :=
  decode_detailed_encode_observation context injective graph

theorem never_duplicate_refusal_contract
    (graph : ClosedRootedGraph context) :
    decodeCanonicalGraphDetailed context injective
        (encodeCanonicalGraph context graph) ≠
      .error .duplicateRegistryKey :=
  decode_encode_never_duplicate_refusal context injective graph

theorem encoded_registry_keys_unique_contract
    (graph : ClosedRootedGraph context) :
    EncodedRegistryKeys context
        (encodeCanonicalGraph context graph) =
      graph.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) ∧
    NoDuplicates
      (EncodedRegistryKeys context
        (encodeCanonicalGraph context graph)) :=
  encode_canonical_graph_registry_keys_unique context graph

theorem domain_exact_contract
    (graph : ClosedRootedGraph context) :
    ∃ decoded,
      decodeCanonicalGraphDetailed context injective
          (encodeCanonicalGraph context graph) = .ok decoded ∧
      CanonicalRegistryWellFormed
        context decoded.canonicalRegistry ∧
      validatePublicOccurrences
          decoded.canonicalRegistry decoded.registryKeysNoDup =
        .ok decoded.resolvedEdges ∧
      EveryBlockStoredAtCanonicalMinimum
        decoded.canonicalRegistry :=
  decode_encode_domain_exact context injective graph

theorem detailed_reencode_contract
    (accepted :
      decodeCanonicalGraphDetailed context injective bytes = .ok graph) :
    encodeCanonicalGraph context graph = bytes :=
  decode_detailed_reencodes_exact accepted

theorem ambient_free_contract
    (accepted :
      decodeCanonicalGraphDetailed context injective bytes = .ok graph) :
    PureDecodeWitness context bytes graph :=
  decode_graph_bytes_ambient_free accepted

#print axioms encode_canonical_graph_registry_keys_unique
#print axioms decode_graph_bytes_ambient_free
#print axioms decode_encode_never_duplicate_refusal
#print axioms decode_encode_domain_exact
#print axioms decode_detailed_encode_observation
#print axioms decode_detailed_reencodes_exact
#print axioms ambiguous_canonical_label_refusal

end Residua.RCC.Addressing.AddressedGraph.Codec.Tests


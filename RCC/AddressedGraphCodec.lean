import RCC.AddressedGraphClosed

/-!
# RCC addressed-graph pure codec

This module owns the store-free whole-graph wire format.  Its decoder may
consume only canonical bytes, the frozen graph context, and the explicit
digest-injectivity certificate.
-/

namespace Residua.RCC.Addressing.AddressedGraph

open Residua.RCC.Addressing

inductive GraphDecodeResidue
  | unknownGraphTag
  | truncatedEnvelope
  | malformedEnvelopeLength
  | noncanonicalNatural
  | noncanonicalString
  | invalidKindCode
  | blockDecodeRefused (residue : BlockDecodeResidue)
  | localRefInDag
  | localIndexOutOfBounds
  | localTargetKindMismatch
  | unnormalizedUnorderedTargets
  | unnormalizedEdgeCollections
  | noncanonicalBlockTLV
  | unsortedRegistry
  | duplicateRegistryKey
  | targetKindMismatch
  | targetMissing
  | canonicalMemberIndexOutOfBounds
  | rootNotInRegistry
  | rootMemberIndexOutOfBounds
  | localConnectivityRefused
  | crossBlockCycle
  | ambiguousCanonicalLabel
  | blockNotCanonicalMinimum
  | blockAddressMismatch
  | rootBlockAddressMismatch
  | addressAlias
  | trailingData
  | noncanonicalReencoding
  deriving DecidableEq, Repr

private def graphTlv (tag : Nat) (payload : GraphBytes) :
    GraphBytes :=
  [tag, payload.length] ++ payload

private def encodeGraphText (value : GraphText) : GraphBytes :=
  value.scalars.length :: value.scalars.map Char.toNat

private def encodeGraphWireAddress
    (address : GraphWireAddress kind) : GraphBytes :=
  encodeGraphText address.algorithm ++
    (encodeGraphText address.domainQ ++
      (encodeGraphText address.schemaQ ++
        encodeGraphText address.digest))

private def encodeRegistryEntry
    (context : GraphCodecContext)
    (entry : SomeCanonicalBlock context) : GraphBytes :=
  graphTlv 34
    (graphTlv 35 [context.kindSchema.kindCode entry.kind] ++
      (graphTlv 36 (encodeGraphWireAddress entry.blockQ) ++
        graphTlv 37 (encodeCanonicalBlock entry.block)))

private def encodeRegistryEntries
    (context : GraphCodecContext) :
    List (SomeCanonicalBlock context) → GraphBytes
  | [] =>
      []
  | head :: tail =>
      let encoded := encodeRegistryEntry context head
      encoded.length ::
        (encoded ++ encodeRegistryEntries context tail)

private def encodeRegistry
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : GraphBytes :=
  graphTlv 33
    (registry.length :: encodeRegistryEntries context registry)

private def encodeRootEntry
    (context : GraphCodecContext)
    (entry : SomeCanonicalBlock context) : GraphBytes :=
  graphTlv 35 [context.kindSchema.kindCode entry.kind] ++
    graphTlv 36 (encodeGraphWireAddress entry.blockQ)

private def encodeRootPointer
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context) : GraphBytes :=
  let rootIndex : Fin graph.canonicalRegistry.length :=
    ⟨graph.canonicalRoot.blockIndex, graph.canonicalRoot.blockBound⟩
  let rootEntry := graph.canonicalRegistry.get rootIndex
  graphTlv 38
    (graphTlv 39
        (encodeRootEntry context rootEntry) ++
      graphTlv 40 [graph.canonicalRoot.localIndex])

def encodeCanonicalGraph
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context) :
    GraphBytes :=
  graphTlv 32
    (encodeRegistry context graph.canonicalRegistry ++
      encodeRootPointer context graph)

theorem encode_canonical_graph_factors_serialized_projection
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (observationExact :
      serializedCanonicalProjection left =
        serializedCanonicalProjection right) :
    encodeCanonicalGraph context left =
      encodeCanonicalGraph context right := by
  have registryExact :
      left.canonicalRegistry =
        right.canonicalRegistry :=
    congrArg CanonicalRootedGraph.registry observationExact
  have rootBlockExact :
      left.canonicalRoot.blockIndex =
        right.canonicalRoot.blockIndex :=
    congrArg
      (fun projection =>
        projection.root.blockIndex)
      observationExact
  have rootLocalExact :
      left.canonicalRoot.localIndex =
        right.canonicalRoot.localIndex :=
    congrArg
      (fun projection =>
        projection.root.localIndex)
      observationExact
  simp [
    encodeCanonicalGraph,
    encodeRootPointer,
    registryExact,
    rootBlockExact,
    rootLocalExact
  ]

structure PureDecodeWitness
    (context : GraphCodecContext)
    (bytes : GraphBytes)
    (graph : ClosedRootedGraph context) : Prop where
  canonicalRegistryWellFormed :
    CanonicalRegistryWellFormed
      context graph.canonicalRegistry
  resolvedEdgeTable :
    validatePublicOccurrences
      graph.canonicalRegistry graph.registryKeysNoDup =
        .ok graph.resolvedEdges
  internalReferentialClosure :
    EveryPublicReferenceOccurrenceResolved
      graph.canonicalRegistry graph.registryKeysNoDup
  computedConnectivity :
    EveryCyclicBlockHasComputedConnectivity graph.canonicalRegistry
  computedDependency :
    ∃ certificate,
      buildDependencyCertificate graph.resolvedEdges =
        .ok certificate ∧
      certificate.height = graph.dependency.height
  recomputedAddresses :
    BlockAddressesDerived context graph.canonicalRegistry
  canonicalReencoding :
    encodeCanonicalGraph context graph = bytes

private abbrev GraphDecodeM (α : Type) :=
  Except GraphDecodeResidue α

private structure ParsedGraphTlv where
  tag : Nat
  payload : GraphBytes
  suffix : GraphBytes

private def readGraphTlv : GraphBytes → GraphDecodeM ParsedGraphTlv
  | [] =>
      .error .truncatedEnvelope
  | [_tag] =>
      .error .truncatedEnvelope
  | tag :: payloadLength :: rest =>
      if _enough : payloadLength ≤ rest.length then
        .ok
          { tag
            payload := rest.take payloadLength
            suffix := rest.drop payloadLength }
      else
        .error .malformedEnvelopeLength

private theorem read_graph_tlv_encode
    (tag : Nat)
    (payload suffix : GraphBytes) :
    readGraphTlv (graphTlv tag payload ++ suffix) =
      .ok
        { tag
          payload
          suffix } := by
  simp [graphTlv, readGraphTlv]

private structure ParsedGraphText where
  value : GraphText
  suffix : GraphBytes

private def parseGraphText : GraphBytes → GraphDecodeM ParsedGraphText
  | [] =>
      .error .truncatedEnvelope
  | textLength :: rest =>
      if _enough : textLength ≤ rest.length then
        let codes := rest.take textLength
        let value : GraphText := ⟨codes.map Char.ofNat⟩
        if _canonical : value.scalars.map Char.toNat = codes then
          .ok
            { value
              suffix := rest.drop textLength }
        else
          .error .noncanonicalString
      else
        .error .malformedEnvelopeLength

private theorem parse_graph_text_encode
    (value : GraphText)
    (suffix : GraphBytes) :
    parseGraphText (encodeGraphText value ++ suffix) =
      .ok
        { value
          suffix } := by
  rcases value with ⟨scalars⟩
  have scalarsRoundtrip :
      List.map (Char.ofNat ∘ Char.toNat) scalars = scalars := by
    induction scalars with
    | nil =>
        rfl
    | cons head tail tailIH =>
        simp [Function.comp_apply, Char.ofNat_toNat, tailIH]
  simp [
    encodeGraphText,
    parseGraphText,
    scalarsRoundtrip
  ]

private def parseExactGraphNat : GraphBytes → GraphDecodeM Nat
  | [value] =>
      .ok value
  | _ =>
      .error .noncanonicalNatural

private def decodeGraphKindCode
    (schema : GraphKindSchema) (code : Nat) :
    Option schema.Kind :=
  schema.enumerate.find? fun kind => schema.kindCode kind = code

private theorem decode_graph_kind_code_encode
    (schema : GraphKindSchema)
    (kind : schema.Kind) :
    decodeGraphKindCode schema (schema.kindCode kind) =
      some kind := by
  unfold decodeGraphKindCode
  cases found :
      schema.enumerate.find? fun candidate =>
        schema.kindCode candidate = schema.kindCode kind with
  | none =>
      have rejected :=
        (List.find?_eq_none.mp found)
          kind (schema.enumerateComplete kind)
      simp at rejected
  | some candidate =>
      have equalCode :
          schema.kindCode candidate =
            schema.kindCode kind := by
        simpa using List.find?_some found
      have equalKind :=
        schema.kindCodeInjective equalCode
      cases equalKind
      rfl

private structure ParsedGraphKind (schema : GraphKindSchema) where
  kind : schema.Kind
  suffix : GraphBytes

private def parseGraphKind
    (schema : GraphKindSchema)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedGraphKind schema) := do
  let framed ← readGraphTlv bytes
  if framed.tag = 35 then
    let code ← parseExactGraphNat framed.payload
    match decodeGraphKindCode schema code with
    | some kind =>
        .ok ⟨kind, framed.suffix⟩
    | none =>
        .error .invalidKindCode
  else
    .error .invalidKindCode

private theorem parse_graph_kind_encode
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (suffix : GraphBytes) :
    parseGraphKind schema
        (graphTlv 35 [schema.kindCode kind] ++ suffix) =
      .ok
        { kind
          suffix } := by
  unfold parseGraphKind
  rw [read_graph_tlv_encode]
  change
    (match
        decodeGraphKindCode schema (schema.kindCode kind) with
      | some decoded =>
          Except.ok
            ({ kind := decoded
               suffix } : ParsedGraphKind schema)
      | none =>
          Except.error GraphDecodeResidue.invalidKindCode) =
      Except.ok
        { kind
          suffix }
  rw [decode_graph_kind_code_encode]

private structure ParsedGraphWireAddress
    (context : GraphCodecContext)
    (kind : context.kindSchema.Kind) where
  address :
    GraphWireAddress (context.kindSchema.toAddressKind kind)
  suffix : GraphBytes

private def parseGraphWireAddress
    (context : GraphCodecContext)
    (kind : context.kindSchema.Kind)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedGraphWireAddress context kind) := do
  let framed ← readGraphTlv bytes
  if framed.tag = 36 then
    let algorithm ← parseGraphText framed.payload
    let domain ← parseGraphText algorithm.suffix
    let schema ← parseGraphText domain.suffix
    let digest ← parseGraphText schema.suffix
    if digest.suffix = [] then
      .ok
        { address :=
            { algorithm := algorithm.value
              domainQ := domain.value
              schemaQ := schema.value
              digest := digest.value }
          suffix := framed.suffix }
    else
      .error .noncanonicalString
  else
    .error .noncanonicalString

private theorem parse_graph_wire_address_encode
    (context : GraphCodecContext)
    (kind : context.kindSchema.Kind)
    (address :
      GraphWireAddress
        (context.kindSchema.toAddressKind kind))
    (suffix : GraphBytes) :
    parseGraphWireAddress context kind
        (graphTlv 36 (encodeGraphWireAddress address) ++ suffix) =
      .ok
        { address
          suffix } := by
  unfold parseGraphWireAddress
  rw [read_graph_tlv_encode]
  unfold encodeGraphWireAddress
  change
    (do
      let algorithm ←
        parseGraphText
          (encodeGraphText address.algorithm ++
            (encodeGraphText address.domainQ ++
              (encodeGraphText address.schemaQ ++
                encodeGraphText address.digest)))
      let domain ← parseGraphText algorithm.suffix
      let schema ← parseGraphText domain.suffix
      let digest ← parseGraphText schema.suffix
      if digest.suffix = [] then
        .ok
          ({ address :=
              { algorithm := algorithm.value
                domainQ := domain.value
                schemaQ := schema.value
                digest := digest.value }
             suffix } :
            ParsedGraphWireAddress context kind)
      else
        .error .noncanonicalString) =
      .ok
        { address
          suffix }
  simp only [
    Bind.bind,
    Except.bind
  ]
  simp only [parse_graph_text_encode]
  have digestExact :
      parseGraphText (encodeGraphText address.digest) =
        .ok
          { value := address.digest
            suffix := [] } := by
    simpa using parse_graph_text_encode address.digest []
  rw [digestExact]
  rfl

private structure ParsedRegistryEntry
    (context : GraphCodecContext) where
  entry : SomeCanonicalBlock context
  suffix : GraphBytes

private def parseRegistryEntry
    (context : GraphCodecContext)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedRegistryEntry context) := do
  let framed ← readGraphTlv bytes
  if framed.tag = 34 then
    let kind ← parseGraphKind context.kindSchema framed.payload
    let address ←
      parseGraphWireAddress context kind.kind kind.suffix
    let blockFrame ← readGraphTlv address.suffix
    if blockFrame.tag = 37 then
      if blockFrame.suffix = [] then
        match
            decodeCanonicalBlockDetailed
              context.kindSchema kind.kind blockFrame.payload with
        | .ok block =>
            .ok
              { entry :=
                  { kind := kind.kind
                    blockQ := address.address
                    block }
                suffix := framed.suffix }
        | .error residue =>
            .error (.blockDecodeRefused residue)
      else
        .error .noncanonicalBlockTLV
    else
      .error .noncanonicalBlockTLV
  else
    .error .noncanonicalBlockTLV

private theorem parse_registry_entry_encode
    (context : GraphCodecContext)
    (entry : SomeCanonicalBlock context)
    (suffix : GraphBytes) :
    parseRegistryEntry context
        (encodeRegistryEntry context entry ++ suffix) =
      .ok
        { entry
          suffix } := by
  rcases entry with ⟨kind, address, block⟩
  unfold parseRegistryEntry encodeRegistryEntry
  rw [read_graph_tlv_encode]
  simp only [Bind.bind, Except.bind]
  simp only [parse_graph_kind_encode]
  simp only [parse_graph_wire_address_encode]
  simp only [if_true]
  have blockFrameExact :
      readGraphTlv
          (graphTlv 37 (encodeCanonicalBlock block)) =
        .ok
          { tag := 37
            payload := encodeCanonicalBlock block
            suffix := [] } := by
    simpa using
      read_graph_tlv_encode
        37 (encodeCanonicalBlock block) []
  rw [blockFrameExact]
  simp only
  rw [decode_encode_canonical_block]
  rfl

private def parseRegistryEntries
    (context : GraphCodecContext) :
    Nat → GraphBytes →
      GraphDecodeM
        (List (SomeCanonicalBlock context) × GraphBytes)
  | 0, bytes =>
      .ok ([], bytes)
  | _ + 1, [] =>
      .error .truncatedEnvelope
  | remaining + 1, entryLength :: rest =>
      if _enough : entryLength ≤ rest.length then
        let entryBytes := rest.take entryLength
        match parseRegistryEntry context entryBytes with
        | .error residue =>
            .error residue
        | .ok parsedEntry =>
            if parsedEntry.suffix = [] then
              match
                  parseRegistryEntries context remaining
                    (rest.drop entryLength) with
              | .error residue =>
                  .error residue
              | .ok (entries, suffix) =>
                  .ok (parsedEntry.entry :: entries, suffix)
            else
              .error .noncanonicalBlockTLV
      else
        .error .malformedEnvelopeLength

private theorem parse_registry_entries_encode
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (suffix : GraphBytes) :
    parseRegistryEntries context registry.length
        (encodeRegistryEntries context registry ++ suffix) =
      .ok (registry, suffix) := by
  induction registry with
  | nil =>
      rfl
  | cons head tail tailIH =>
      have headExact :
          parseRegistryEntry context
              (encodeRegistryEntry context head) =
            .ok
              { entry := head
                suffix := [] } := by
        simpa using
          parse_registry_entry_encode context head []
      simp [
        encodeRegistryEntries,
        parseRegistryEntries,
        headExact,
        tailIH
      ]

private structure ParsedRegistry
    (context : GraphCodecContext) where
  registry : List (SomeCanonicalBlock context)
  suffix : GraphBytes

private def parseRegistry
    (context : GraphCodecContext)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedRegistry context) := do
  let framed ← readGraphTlv bytes
  if framed.tag = 33 then
    match framed.payload with
    | [] =>
        .error .noncanonicalNatural
    | entryCount :: entriesBytes =>
        match
            parseRegistryEntries context entryCount entriesBytes with
        | .error residue =>
            .error residue
        | .ok (registry, []) =>
            .ok ⟨registry, framed.suffix⟩
        | .ok (_, _ :: _) =>
            .error .trailingData
  else
    .error .unknownGraphTag

private theorem parse_registry_encode
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (suffix : GraphBytes) :
    parseRegistry context
        (encodeRegistry context registry ++ suffix) =
      .ok
        { registry
          suffix } := by
  have entriesExact :
      parseRegistryEntries context registry.length
          (encodeRegistryEntries context registry) =
        .ok (registry, []) := by
    simpa using
      parse_registry_entries_encode context registry []
  unfold parseRegistry encodeRegistry
  rw [read_graph_tlv_encode]
  simp only [Bind.bind, Except.bind]
  rw [entriesExact]
  rfl

private structure ParsedRootPointer
    (context : GraphCodecContext) where
  kind : context.kindSchema.Kind
  blockQ :
    GraphWireAddress (context.kindSchema.toAddressKind kind)
  localIndex : Nat
  suffix : GraphBytes

private def parsedRootPointerOfCanonical
    (context : GraphCodecContext)
    {registry : List (SomeCanonicalBlock context)}
    (root : CanonicalNodePointer context registry)
    (suffix : GraphBytes) :
    ParsedRootPointer context :=
  let rootIndex : Fin registry.length :=
    ⟨root.blockIndex, root.blockBound⟩
  let rootEntry := registry.get rootIndex
  { kind := rootEntry.kind
    blockQ := rootEntry.blockQ
    localIndex := root.localIndex
    suffix }

private def parseRootPointer
    (context : GraphCodecContext)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedRootPointer context) := do
  let rootFrame ← readGraphTlv bytes
  if rootFrame.tag = 38 then
    let selectorFrame ← readGraphTlv rootFrame.payload
    if selectorFrame.tag = 39 then
      let kind ←
        parseGraphKind context.kindSchema selectorFrame.payload
      let address ←
        parseGraphWireAddress context kind.kind kind.suffix
      if address.suffix = [] then
        let indexFrame ← readGraphTlv selectorFrame.suffix
        if indexFrame.tag = 40 then
          let localIndex ← parseExactGraphNat indexFrame.payload
          if indexFrame.suffix = [] then
            .ok
              { kind := kind.kind
                blockQ := address.address
                localIndex
                suffix := rootFrame.suffix }
          else
            .error .trailingData
        else
          .error .noncanonicalNatural
      else
        .error .rootBlockAddressMismatch
    else
      .error .rootBlockAddressMismatch
  else
    .error .rootNotInRegistry

private theorem parse_root_pointer_encode
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context)
    (suffix : GraphBytes) :
    parseRootPointer context
        (encodeRootPointer context graph ++ suffix) =
      .ok
        (parsedRootPointerOfCanonical
          context graph.canonicalRoot suffix) := by
  let rootIndex : Fin graph.canonicalRegistry.length :=
    ⟨graph.canonicalRoot.blockIndex,
      graph.canonicalRoot.blockBound⟩
  let rootEntry :=
    graph.canonicalRegistry.get rootIndex
  change
    parseRootPointer context
        (graphTlv 38
            (graphTlv 39
                (graphTlv 35
                    [context.kindSchema.kindCode rootEntry.kind] ++
                  graphTlv 36
                    (encodeGraphWireAddress rootEntry.blockQ)) ++
              graphTlv 40 [graph.canonicalRoot.localIndex]) ++
          suffix) =
      .ok
        { kind := rootEntry.kind
          blockQ := rootEntry.blockQ
          localIndex := graph.canonicalRoot.localIndex
          suffix }
  have addressExact :
      parseGraphWireAddress context rootEntry.kind
          (graphTlv 36
            (encodeGraphWireAddress rootEntry.blockQ)) =
        .ok
          { address := rootEntry.blockQ
            suffix := [] } := by
    simpa using
      parse_graph_wire_address_encode
        context rootEntry.kind rootEntry.blockQ []
  have indexFrameExact :
      readGraphTlv
          (graphTlv 40 [graph.canonicalRoot.localIndex]) =
        .ok
          { tag := 40
            payload := [graph.canonicalRoot.localIndex]
            suffix := [] } := by
    simpa using
      read_graph_tlv_encode
        40 [graph.canonicalRoot.localIndex] []
  unfold parseRootPointer
  rw [read_graph_tlv_encode]
  simp only [Bind.bind, Except.bind]
  rw [read_graph_tlv_encode]
  simp only
  rw [parse_graph_kind_encode]
  simp only
  rw [addressExact]
  simp only
  rw [indexFrameExact]
  rfl

private structure ParsedGraphSyntax
    (context : GraphCodecContext) where
  registry : List (SomeCanonicalBlock context)
  root : ParsedRootPointer context

private def parseCanonicalGraphSyntax
    (context : GraphCodecContext)
    (bytes : GraphBytes) :
    GraphDecodeM (ParsedGraphSyntax context) := do
  let graphFrame ← readGraphTlv bytes
  if graphFrame.tag = 32 then
    if graphFrame.suffix = [] then
      let registry ← parseRegistry context graphFrame.payload
      let root ← parseRootPointer context registry.suffix
      if root.suffix = [] then
        .ok
          { registry := registry.registry
            root }
      else
        .error .trailingData
    else
      .error .trailingData
  else
    .error .unknownGraphTag

private theorem parse_canonical_graph_syntax_encode
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context) :
    parseCanonicalGraphSyntax context
        (encodeCanonicalGraph context graph) =
      .ok
        { registry := graph.canonicalRegistry
          root :=
            parsedRootPointerOfCanonical
              context graph.canonicalRoot [] } := by
  have graphFrameExact :
      readGraphTlv (encodeCanonicalGraph context graph) =
        .ok
          { tag := 32
            payload :=
              encodeRegistry context graph.canonicalRegistry ++
                encodeRootPointer context graph
            suffix := [] } := by
    unfold encodeCanonicalGraph
    simpa using
      read_graph_tlv_encode
        32
        (encodeRegistry context graph.canonicalRegistry ++
          encodeRootPointer context graph)
        []
  have registryExact :
      parseRegistry context
          (encodeRegistry context graph.canonicalRegistry ++
            encodeRootPointer context graph) =
        .ok
          { registry := graph.canonicalRegistry
            suffix := encodeRootPointer context graph } :=
    parse_registry_encode
      context graph.canonicalRegistry
        (encodeRootPointer context graph)
  have rootExact :
      parseRootPointer context
          (encodeRootPointer context graph) =
        .ok
          (parsedRootPointerOfCanonical
            context graph.canonicalRoot []) := by
    simpa using parse_root_pointer_encode context graph []
  unfold parseCanonicalGraphSyntax
  rw [graphFrameExact]
  simp only [Bind.bind, Except.bind]
  rw [registryExact]
  simp only
  rw [rootExact]
  rfl

/--
Project the exact typed registry-key bytes carried by a canonical graph wire
encoding. Malformed bytes have no emitted-key projection.
-/
def EncodedRegistryKeys
    (context : GraphCodecContext)
    (bytes : GraphBytes) : List GraphBytes :=
  match parseCanonicalGraphSyntax context bytes with
  | .error _ =>
      []
  | .ok parsed =>
      parsed.registry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key)

/--
The whole-graph encoder emits exactly the closed carrier's registry keys, and
that emitted projection contains no duplicate key bytes.
-/
theorem encode_canonical_graph_registry_keys_unique
    (context : GraphCodecContext)
    (graph : ClosedRootedGraph context) :
    EncodedRegistryKeys context
        (encodeCanonicalGraph context graph) =
      graph.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) ∧
    NoDuplicates
      (EncodedRegistryKeys context
        (encodeCanonicalGraph context graph)) := by
  have emittedExact :
      EncodedRegistryKeys context
          (encodeCanonicalGraph context graph) =
        graph.canonicalRegistry.map
          (fun entry =>
            encodeCanonicalRegistryKey context entry.key) := by
    unfold EncodedRegistryKeys
    rw [parse_canonical_graph_syntax_encode context graph]
  exact
    ⟨emittedExact,
      emittedExact.symm ▸ graph.registryKeysNoDup⟩

/--
Equal canonical graph bytes expose the same serialized registry, root key,
and root-local selector.
-/
theorem encode_canonical_graph_reflects_registry_root
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (encodedExact :
      encodeCanonicalGraph context left =
        encodeCanonicalGraph context right) :
    left.canonicalRegistry = right.canonicalRegistry ∧
      encodeCanonicalRegistryKey context
          (left.canonicalRegistry.get
            ⟨left.canonicalRoot.blockIndex,
              left.canonicalRoot.blockBound⟩).key =
        encodeCanonicalRegistryKey context
          (right.canonicalRegistry.get
            ⟨right.canonicalRoot.blockIndex,
              right.canonicalRoot.blockBound⟩).key ∧
      left.canonicalRoot.localIndex =
        right.canonicalRoot.localIndex := by
  have parsedExact :=
    congrArg (parseCanonicalGraphSyntax context) encodedExact
  rw [
    parse_canonical_graph_syntax_encode context left,
    parse_canonical_graph_syntax_encode context right
  ] at parsedExact
  have syntaxExact := Except.ok.inj parsedExact
  refine
    ⟨congrArg ParsedGraphSyntax.registry syntaxExact, ?_, ?_⟩
  · simpa [parsedRootPointerOfCanonical, SomeCanonicalBlock.key] using
      congrArg
        (fun parsed =>
          encodeCanonicalRegistryKey context
            ({ kind := parsed.root.kind
               blockQ := parsed.root.blockQ } :
              CanonicalRegistryKey context.kindSchema))
        syntaxExact
  · simpa [parsedRootPointerOfCanonical] using
      congrArg
        (fun parsed => parsed.root.localIndex)
        syntaxExact

private structure NoDuplicateBytesWitness
    (values : List GraphBytes) : Type where
  valid : NoDuplicates values

private def validateNoDuplicateBytes :
    (values : List GraphBytes) →
      GraphDecodeM (NoDuplicateBytesWitness values)
  | [] =>
      .ok ⟨by simp [NoDuplicates]⟩
  | head :: tail =>
      if duplicate : head ∈ tail then
        .error .duplicateRegistryKey
      else
        match validateNoDuplicateBytes tail with
        | .error residue =>
            .error residue
        | .ok tailNoDuplicates =>
            .ok ⟨by
              unfold NoDuplicates
              rw [List.pairwise_cons]
              exact
                ⟨by
                  intro value valueMember headExact
                  apply duplicate
                  rw [headExact]
                  exact valueMember,
                tailNoDuplicates.valid⟩⟩

private structure RegistryStrictOrderWitness
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Type where
  valid : CanonicalRegistryStrictOrder context registry

private def validateRegistryStrictOrder
    (context : GraphCodecContext) :
    (registry : List (SomeCanonicalBlock context)) →
      GraphDecodeM (RegistryStrictOrderWitness context registry)
  | [] =>
      .ok ⟨by simp [CanonicalRegistryStrictOrder]⟩
  | head :: tail =>
      if ordered :
          ∀ right, right ∈ tail →
            compareGraphBytes
              (encodeCanonicalRegistryKey context head.key)
              (encodeCanonicalRegistryKey context right.key) = .lt then
        match validateRegistryStrictOrder context tail with
        | .error residue =>
            .error residue
        | .ok tailOrdered =>
            .ok ⟨by
              unfold CanonicalRegistryStrictOrder
              rw [List.pairwise_cons]
              exact ⟨ordered, tailOrdered.valid⟩⟩
      else
        .error .unsortedRegistry

private structure ValidatedRegistryOrder
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Type where
  keysNoDup : CanonicalRegistryKeysNoDup context registry
  strictlySorted : CanonicalRegistryStrictOrder context registry

private def validateRegistryOrder
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) :
    GraphDecodeM (ValidatedRegistryOrder context registry) := do
  let encodedKeys :=
    registry.map
      (fun entry => encodeCanonicalRegistryKey context entry.key)
  let keysNoDup ← validateNoDuplicateBytes encodedKeys
  let strictlySorted ← validateRegistryStrictOrder context registry
  .ok
    { keysNoDup := by
        simpa [CanonicalRegistryKeysNoDup, encodedKeys] using
      keysNoDup.valid
      strictlySorted := strictlySorted.valid }

private theorem validate_no_duplicate_bytes_complete :
    ∀ {values : List GraphBytes},
      NoDuplicates values →
      ∃ witness,
        validateNoDuplicateBytes values = .ok witness
  | [], _ =>
      ⟨⟨by simp [NoDuplicates]⟩, rfl⟩
  | head :: tail, noDuplicates => by
      have separated :
          (∀ value ∈ tail, head ≠ value) ∧
            NoDuplicates tail := by
        unfold NoDuplicates at noDuplicates
        rw [List.pairwise_cons] at noDuplicates
        exact noDuplicates
      have headAbsent : head ∉ tail := by
        intro headMember
        exact (separated.1 head headMember) rfl
      rcases
          validate_no_duplicate_bytes_complete separated.2 with
        ⟨tailWitness, tailExact⟩
      simp only [validateNoDuplicateBytes, headAbsent, tailExact]
      exact
        ⟨{ valid := by
              unfold NoDuplicates
              rw [List.pairwise_cons]
              exact separated },
          rfl⟩

private theorem validate_registry_strict_order_complete
    (context : GraphCodecContext) :
    ∀ {registry : List (SomeCanonicalBlock context)},
      CanonicalRegistryStrictOrder context registry →
      ∃ witness,
        validateRegistryStrictOrder context registry = .ok witness
  | [], _ =>
      ⟨⟨by simp [CanonicalRegistryStrictOrder]⟩, rfl⟩
  | head :: tail, strict => by
      have separated :
          (∀ right, right ∈ tail →
            compareGraphBytes
              (encodeCanonicalRegistryKey context head.key)
              (encodeCanonicalRegistryKey context right.key) = .lt) ∧
            CanonicalRegistryStrictOrder context tail := by
        unfold CanonicalRegistryStrictOrder at strict
        rw [List.pairwise_cons] at strict
        exact strict
      rcases
          validate_registry_strict_order_complete
            context separated.2 with
        ⟨tailWitness, tailExact⟩
      rw [
        validateRegistryStrictOrder,
        dif_pos separated.1,
        tailExact
      ]
      exact
        ⟨⟨by
            unfold CanonicalRegistryStrictOrder
            rw [List.pairwise_cons]
            exact separated⟩,
          rfl⟩

private theorem validate_registry_order_complete
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (keysNoDup : CanonicalRegistryKeysNoDup context registry)
    (strict : CanonicalRegistryStrictOrder context registry) :
    ∃ witness,
      validateRegistryOrder context registry = .ok witness := by
  let encodedKeys :=
    registry.map
      (fun entry => encodeCanonicalRegistryKey context entry.key)
  rcases
      validate_no_duplicate_bytes_complete
        (by
          simpa [CanonicalRegistryKeysNoDup, encodedKeys] using
            keysNoDup) with
    ⟨keysWitness, keysExact⟩
  rcases
      validate_registry_strict_order_complete context strict with
    ⟨strictWitness, strictExact⟩
  let witness : ValidatedRegistryOrder context registry :=
    { keysNoDup := by
        simpa [CanonicalRegistryKeysNoDup, encodedKeys] using
          keysWitness.valid
      strictlySorted := strictWitness.valid }
  refine ⟨witness, ?_⟩
  rw [
    validateRegistryOrder,
    keysExact,
    strictExact
  ]
  rfl

private theorem find_canonical_registry_lookup_complete_at
    (context : GraphCodecContext) :
    ∀ (registry : List (SomeCanonicalBlock context))
      (_keysNoDup : CanonicalRegistryKeysNoDup context registry)
      (index : Fin registry.length),
      ∃ found,
        findCanonicalRegistryLookup
            context (registry.get index).key registry =
          some found ∧
        found.targetBlock = registry.get index ∧
        found.targetBlockIndex = index.val := by
  intro registry
  induction registry with
  | nil =>
      intro _ index
      exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | cons head tail tailIH =>
      intro keysNoDup index
      have separated :
          (∀ value ∈
              tail.map (fun entry =>
                encodeCanonicalRegistryKey context entry.key),
              encodeCanonicalRegistryKey context head.key ≠ value) ∧
            NoDuplicates
              (tail.map (fun entry =>
                encodeCanonicalRegistryKey context entry.key)) := by
        simpa [
          CanonicalRegistryKeysNoDup,
          NoDuplicates
        ] using keysNoDup
      cases index with
      | mk value bound =>
          cases value with
          | zero =>
              refine
                ⟨{ targetBlockIndex := 0
                   targetBlockBound := by simp
                   targetBlock := head
                   targetLookup := rfl
                   targetKeyExact := rfl },
                  ?_, rfl, rfl⟩
              simp [findCanonicalRegistryLookup]
          | succ value =>
              have tailBound : value < tail.length :=
                Nat.succ_lt_succ_iff.mp bound
              let tailIndex : Fin tail.length :=
                ⟨value, tailBound⟩
              have targetMember :
                  encodeCanonicalRegistryKey
                      context (tail.get tailIndex).key ∈
                    tail.map (fun entry =>
                      encodeCanonicalRegistryKey context entry.key) :=
                List.mem_map.mpr
                  ⟨tail.get tailIndex,
                    List.mem_iff_get.mpr ⟨tailIndex, rfl⟩,
                    rfl⟩
              have headDifferent :
                  encodeCanonicalRegistryKey context head.key ≠
                    encodeCanonicalRegistryKey
                      context (tail.get tailIndex).key :=
                separated.1 _ targetMember
              rcases
                  tailIH separated.2 tailIndex with
                ⟨found, foundExact, targetExact,
                  targetIndexExact⟩
              change
                ∃ lifted,
                  findCanonicalRegistryLookup
                      context (tail.get tailIndex).key
                      (head :: tail) =
                    some lifted ∧
                  lifted.targetBlock = tail.get tailIndex ∧
                  lifted.targetBlockIndex = value + 1
              let lifted :
                  CanonicalRegistryLookup
                    context (head :: tail)
                    (tail.get tailIndex).key :=
                { targetBlockIndex := found.targetBlockIndex.succ
                  targetBlockBound :=
                    Nat.succ_lt_succ found.targetBlockBound
                  targetBlock := found.targetBlock
                  targetLookup := by
                    simpa using found.targetLookup
                  targetKeyExact := found.targetKeyExact }
              refine
                ⟨lifted, ?_, targetExact, ?_⟩
              simp only [findCanonicalRegistryLookup]
              split
              · rename_i keyExact
                exact False.elim (headDifferent keyExact)
              · split
                · rename_i notFound foundMissing
                  rw [foundMissing] at foundExact
                  cases foundExact
                · rename_i foundTail foundTailExact
                  have foundTailEq : foundTail = found :=
                    Option.some.inj
                      (foundTailExact.symm.trans foundExact)
                  subst foundTail
                  rfl
              exact congrArg Nat.succ targetIndexExact

private def validateRootPointer
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (root : ParsedRootPointer context) :
    GraphDecodeM (CanonicalNodePointer context registry) :=
  let targetKey : CanonicalRegistryKey context.kindSchema :=
    { kind := root.kind
      blockQ := root.blockQ }
  match findCanonicalRegistryLookup context targetKey registry with
  | none =>
      .error .rootNotInRegistry
  | some found =>
      if localBound :
          root.localIndex < found.targetBlock.block.nodes.length then
        .ok
          { blockIndex := found.targetBlockIndex
            blockBound := found.targetBlockBound
            localIndex := root.localIndex
            localBound := by
              have targetBlockExact :
                  registry.get
                      ⟨found.targetBlockIndex,
                        found.targetBlockBound⟩ =
                    found.targetBlock :=
                Option.some.inj
                  ((list_get?_eq_get registry
                    ⟨found.targetBlockIndex,
                      found.targetBlockBound⟩).symm.trans
                    found.targetLookup)
              rw [targetBlockExact]
              exact localBound }
      else
        .error .rootMemberIndexOutOfBounds

private theorem validate_root_pointer_complete
    (context : GraphCodecContext)
    {registry : List (SomeCanonicalBlock context)}
    (keysNoDup : CanonicalRegistryKeysNoDup context registry)
    (root : CanonicalNodePointer context registry) :
    ∃ validated,
      validateRootPointer context registry
          (parsedRootPointerOfCanonical context root []) =
        .ok validated ∧
      validated.blockIndex = root.blockIndex ∧
      validated.localIndex = root.localIndex := by
  let rootIndex : Fin registry.length :=
    ⟨root.blockIndex, root.blockBound⟩
  rcases
      find_canonical_registry_lookup_complete_at
        context registry keysNoDup rootIndex with
    ⟨found, foundExact, targetExact, targetIndexExact⟩
  have localBound :
      root.localIndex <
        found.targetBlock.block.nodes.length := by
    rw [targetExact]
    exact root.localBound
  have lookupExactForRoot :
      findCanonicalRegistryLookup context
          { kind :=
              (registry.get
                ⟨root.blockIndex, root.blockBound⟩).kind
            blockQ :=
              (registry.get
                ⟨root.blockIndex, root.blockBound⟩).blockQ }
          registry =
        some found := by
    simpa [rootIndex] using foundExact
  unfold validateRootPointer
  dsimp only [parsedRootPointerOfCanonical]
  split
  · rename_i lookupMissing
    rw [lookupMissing] at lookupExactForRoot
    cases lookupExactForRoot
  · rename_i foundTarget lookupExact
    have foundTargetExact : foundTarget = found :=
      Option.some.inj
        (lookupExact.symm.trans lookupExactForRoot)
    subst foundTarget
    split
    · exact
        ⟨_, rfl,
          by
            simpa [rootIndex] using targetIndexExact,
          rfl⟩
    · rename_i outOfBounds
      exact False.elim (outOfBounds localBound)

private structure BlockAddressesDerivedWitness
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Type where
  valid : BlockAddressesDerived context registry

private def validateBlockAddressesDerived
    (context : GraphCodecContext) :
    (registry : List (SomeCanonicalBlock context)) →
      GraphDecodeM (BlockAddressesDerivedWitness context registry)
  | [] =>
      .ok ⟨by simp [BlockAddressesDerived]⟩
  | head :: tail =>
      if addressExact :
          head.blockQ =
            context.blockWireAddress head.kind
              (encodeCanonicalBlock head.block) then
        match validateBlockAddressesDerived context tail with
        | .error residue =>
            .error residue
        | .ok tailDerived =>
            .ok ⟨by
              intro entry entryMember
              simp only [List.mem_cons] at entryMember
              rcases entryMember with entryExact | tailMember
              · subst entry
                exact addressExact
              · exact tailDerived.valid entry tailMember⟩
      else
        .error .blockAddressMismatch

private theorem validate_block_addresses_derived_complete
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (derived : BlockAddressesDerived context registry) :
    ∃ witness,
      validateBlockAddressesDerived context registry =
        .ok witness := by
  induction registry with
  | nil =>
      exact
        ⟨⟨by
          intro entry entryMember
          simp at entryMember⟩,
          rfl⟩
  | cons head tail tailIH =>
      have headDerived :
          head.blockQ =
            context.blockWireAddress head.kind
              (encodeCanonicalBlock head.block) :=
        derived head (by simp)
      have tailDerived :
          BlockAddressesDerived context tail := by
        intro entry entryMember
        exact derived entry (by simp [entryMember])
      rcases tailIH tailDerived with
        ⟨tailWitness, tailExact⟩
      simp only [validateBlockAddressesDerived]
      split
      · split
        · rename_i residue tailFailure
          rw [tailFailure] at tailExact
          cases tailExact
        · exact ⟨_, rfl⟩
      · rename_i addressMismatch
        exact False.elim (addressMismatch headDerived)

private def graphResidueOfPublicReference :
    PublicReferenceResolutionResidue → GraphDecodeResidue
  | .targetKindMismatch =>
      .targetKindMismatch
  | .targetMissing =>
      .targetMissing
  | .canonicalMemberIndexOutOfBounds =>
      .canonicalMemberIndexOutOfBounds

private structure ValidatedResolvedEdges
    (registry : List (SomeCanonicalBlock context))
    (keysNoDup :
      CanonicalRegistryKeysNoDup context registry) : Type where
  table : ResolvedEdgeTable registry keysNoDup
  exact :
    validatePublicOccurrences registry keysNoDup = .ok table

private def validateResolvedEdges
    (registry : List (SomeCanonicalBlock context))
    (keysNoDup : CanonicalRegistryKeysNoDup context registry) :
    GraphDecodeM (ValidatedResolvedEdges registry keysNoDup) :=
  match exact :
      validatePublicOccurrences registry keysNoDup with
  | .ok table =>
      .ok ⟨table, exact⟩
  | .error residue =>
      .error (graphResidueOfPublicReference residue)

private structure ValidatedDependency
    (table : ResolvedEdgeTable registry keysNoDup) : Type where
  certificate : DependencyCertificate table
  exact :
    buildDependencyCertificate table = .ok certificate

private def validateDependency
    (table : ResolvedEdgeTable registry keysNoDup) :
    GraphDecodeM (ValidatedDependency table) :=
  match exact : buildDependencyCertificate table with
  | .ok certificate =>
      .ok ⟨certificate, exact⟩
  | .error .crossBlockCycle =>
      .error .crossBlockCycle

private theorem validate_dependency_complete
    (table : ResolvedEdgeTable registry keysNoDup)
    (certificate : DependencyCertificate table)
    (certificateExact :
      buildDependencyCertificate table = .ok certificate) :
    ∃ validated,
      validateDependency table = .ok validated := by
  unfold validateDependency
  split
  · exact ⟨_, rfl⟩
  · rename_i residue dependencyFailure
    rw [dependencyFailure] at certificateExact
    cases certificateExact

private def resolvedTargetBlockIndex?
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    (keysNoDup :
      CanonicalRegistryKeysNoDup context registry)
    (occurrence : PublicReferenceOccurrence registry) :
    Option Nat :=
  match
      resolvePublicReferenceOccurrence keysNoDup occurrence with
  | .error _ =>
      none
  | .ok resolved =>
      some resolved.targetBlockIndex

private theorem rebuild_dependency_from_equivalent_table
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysNoDup :
      CanonicalRegistryKeysNoDup context registry}
    (sourceTable : ResolvedEdgeTable registry keysNoDup)
    (sourceDependency : DependencyCertificate sourceTable)
    (targetTable : ResolvedEdgeTable registry keysNoDup) :
    ∃ certificate,
      buildDependencyCertificate targetTable =
        .ok certificate := by
  apply build_dependency_complete
  refine ⟨sourceDependency.height, ?_⟩
  intro targetEdge targetEdgeMember
  rcases sourceTable.complete targetEdge.occurrence with
    ⟨sourceEdge, sourceEdgeMember, occurrenceExact⟩
  have sourceTargetObserved :
      resolvedTargetBlockIndex?
          keysNoDup sourceEdge.occurrence =
        some sourceEdge.resolved.targetBlockIndex := by
    unfold resolvedTargetBlockIndex?
    rw [sourceEdge.resolutionExact]
  have targetTargetObserved :
      resolvedTargetBlockIndex?
          keysNoDup targetEdge.occurrence =
        some targetEdge.resolved.targetBlockIndex := by
    unfold resolvedTargetBlockIndex?
    rw [targetEdge.resolutionExact]
  have targetObservationExact :
      resolvedTargetBlockIndex?
          keysNoDup sourceEdge.occurrence =
        resolvedTargetBlockIndex?
          keysNoDup targetEdge.occurrence :=
    congrArg
      (resolvedTargetBlockIndex? keysNoDup)
      occurrenceExact
  rw [
    sourceTargetObserved,
    targetTargetObserved
  ] at targetObservationExact
  have targetIndexExact :
      sourceEdge.resolved.targetBlockIndex =
        targetEdge.resolved.targetBlockIndex :=
    Option.some.inj targetObservationExact
  have sourceIndexExact :
      sourceEdge.occurrence.sourceBlockIndex =
        targetEdge.occurrence.sourceBlockIndex :=
    congrArg
      PublicReferenceOccurrence.sourceBlockIndex
      occurrenceExact
  have sourceDecrease :
      sourceDependency.height
          sourceEdge.resolved.targetBlockIndex <
        sourceDependency.height
          sourceEdge.occurrence.sourceBlockIndex :=
    sourceDependency.decreases
      ⟨sourceEdge, sourceEdgeMember, rfl, rfl⟩
  simpa [targetIndexExact, sourceIndexExact] using
    sourceDecrease

private structure ConnectivityWitness
    (registry : List (SomeCanonicalBlock context)) : Type where
  valid : EveryCyclicBlockHasComputedConnectivity registry

private def validateConnectivity :
    (registry : List (SomeCanonicalBlock context)) →
      GraphDecodeM (ConnectivityWitness registry)
  | [] =>
      .ok ⟨by simp [EveryCyclicBlockHasComputedConnectivity]⟩
  | head :: tail =>
      match blockExact : head.block with
      | .dagSingleton node =>
          match validateConnectivity tail with
          | .error residue =>
              .error residue
          | .ok tailConnectivity =>
              .ok ⟨by
                intro entry entryMember nodes cyclicExact
                simp only [List.mem_cons] at entryMember
                rcases entryMember with entryExact | tailMember
                · subst entry
                  rw [blockExact] at cyclicExact
                  cases cyclicExact
                · exact
                    tailConnectivity.valid
                      entry tailMember nodes cyclicExact⟩
      | .cyclic nodes =>
          match
              connectivityExact :
                Closure.buildConnectivityCertificate nodes with
          | .error _ =>
              .error .localConnectivityRefused
          | .ok certificate =>
              match validateConnectivity tail with
              | .error residue =>
                  .error residue
              | .ok tailConnectivity =>
                  .ok ⟨by
                    intro entry entryMember targetNodes cyclicExact
                    simp only [List.mem_cons] at entryMember
                    rcases entryMember with entryExact | tailMember
                    · subst entry
                      rw [blockExact] at cyclicExact
                      cases cyclicExact
                      exact ⟨certificate, connectivityExact⟩
                    · exact
                        tailConnectivity.valid
                          entry tailMember targetNodes cyclicExact⟩

private theorem validate_connectivity_complete
    (registry : List (SomeCanonicalBlock context))
    (valid : EveryCyclicBlockHasComputedConnectivity registry) :
    ∃ witness,
      validateConnectivity registry = .ok witness := by
  induction registry with
  | nil =>
      exact
        ⟨⟨by
          intro entry entryMember
          simp at entryMember⟩,
          rfl⟩
  | cons head tail tailIH =>
      have tailValid :
          EveryCyclicBlockHasComputedConnectivity tail := by
        intro entry entryMember
        exact valid entry (by simp [entryMember])
      rcases tailIH tailValid with
        ⟨tailWitness, tailExact⟩
      simp only [validateConnectivity]
      split
      · split
        · rename_i residue tailFailure
          rw [tailFailure] at tailExact
          cases tailExact
        · exact ⟨_, rfl⟩
      · rename_i nodes blockExact
        rcases
            valid head (by simp) nodes blockExact with
          ⟨certificate, connectivityExact⟩
        split
        · rename_i residue connectivityFailure
          rw [connectivityFailure] at connectivityExact
          cases connectivityExact
        · split
          · rename_i residue tailFailure
            rw [tailFailure] at tailExact
            cases tailExact
          · exact ⟨_, rfl⟩

private structure OuterCollectionsNormalizedWitness
    (nodes : List (CanonicalNode schema)) : Type where
  valid : EveryOuterCollectionListSortedWithMultiplicity nodes

private theorem list_eq_of_injective_map
    {encode : α → β}
    (injective : ∀ {left right}, encode left = encode right → left = right) :
    ∀ (left right : List α),
      left.map encode = right.map encode →
      left = right
  | [], [], _ =>
      rfl
  | [], _ :: _, encodedExact => by
      simp at encodedExact
  | _ :: _, [], encodedExact => by
      simp at encodedExact
  | leftHead :: leftTail, rightHead :: rightTail, encodedExact => by
      simp only [List.map, List.cons.injEq] at encodedExact
      rcases encodedExact with ⟨headExact, tailExact⟩
      have tailStructural :=
        list_eq_of_injective_map injective
          leftTail rightTail tailExact
      cases injective headExact
      cases tailStructural
      rfl

private def validateOuterCollectionsNormalized :
    (nodes : List (CanonicalNode schema)) →
      GraphDecodeM (OuterCollectionsNormalizedWitness nodes)
  | [] =>
      .ok ⟨by
        intro node nodeMember
        simp at nodeMember⟩
  | head :: tail =>
      if encodedNormalized :
          (normalizeOuterCollections head.edgeCollections).map
              collectionSortBytes =
            head.edgeCollections.map collectionSortBytes then
        have normalized :
            normalizeOuterCollections head.edgeCollections =
              head.edgeCollections :=
          list_eq_of_injective_map
            collection_sort_bytes_injective
            (normalizeOuterCollections head.edgeCollections)
            head.edgeCollections encodedNormalized
        match validateOuterCollectionsNormalized tail with
        | .error residue =>
            .error residue
        | .ok tailNormalized =>
            .ok ⟨by
              intro node nodeMember
              simp only [List.mem_cons] at nodeMember
              rcases nodeMember with nodeExact | tailMember
              · subst node
                exact normalized
              · exact tailNormalized.valid node tailMember⟩
      else
        .error .unnormalizedEdgeCollections

private theorem validate_outer_collections_normalized_complete :
    ∀ {nodes : List (CanonicalNode schema)},
      EveryOuterCollectionListSortedWithMultiplicity nodes →
      ∃ witness,
        validateOuterCollectionsNormalized nodes = .ok witness
  | [], _ =>
      ⟨⟨by
          intro node nodeMember
          simp at nodeMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headNormalized :
          normalizeOuterCollections head.edgeCollections =
            head.edgeCollections :=
        valid head (by simp)
      have encodedNormalized :
          (normalizeOuterCollections head.edgeCollections).map
              collectionSortBytes =
            head.edgeCollections.map collectionSortBytes :=
        congrArg (List.map collectionSortBytes) headNormalized
      have tailValid :
          EveryOuterCollectionListSortedWithMultiplicity tail := by
        intro node nodeMember
        exact valid node (List.mem_cons_of_mem _ nodeMember)
      rcases
          validate_outer_collections_normalized_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateOuterCollectionsNormalized,
        dif_pos encodedNormalized,
        tailExact
      ]
      exact
        ⟨⟨by
            intro node nodeMember
            exact valid node nodeMember⟩,
          rfl⟩

private def EveryCollectionTargetsNormalized
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ node, node ∈ nodes →
    ∀ collection, collection ∈ node.edgeCollections →
      normalizeTargetList collection = collection.targets

private structure CollectionTargetsNormalizedWitness
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Type where
  valid :
    ∀ collection, collection ∈ collections →
      normalizeTargetList collection = collection.targets

private def validateCollectionTargetsNormalized :
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) →
      GraphDecodeM (CollectionTargetsNormalizedWitness collections)
  | [] =>
      .ok ⟨by
        intro collection collectionMember
        simp at collectionMember⟩
  | head :: tail =>
      if encodedNormalized :
          (normalizeTargetList head).map (targetSortBytes head) =
            head.targets.map (targetSortBytes head) then
        have normalized :
            normalizeTargetList head = head.targets :=
          list_eq_of_injective_map
            (target_sort_bytes_injective head)
            (normalizeTargetList head) head.targets encodedNormalized
        match validateCollectionTargetsNormalized tail with
        | .error residue =>
            .error residue
        | .ok tailNormalized =>
            .ok ⟨by
              intro collection collectionMember
              simp only [List.mem_cons] at collectionMember
              rcases collectionMember with collectionExact | tailMember
              · subst collection
                exact normalized
              · exact
                  tailNormalized.valid collection tailMember⟩
      else
        .error .unnormalizedUnorderedTargets

private theorem validate_collection_targets_normalized_complete :
    ∀ {collections :
        List (EdgeCollection schema (ExternalRef schema))},
      (∀ collection, collection ∈ collections →
        normalizeTargetList collection = collection.targets) →
      ∃ witness,
        validateCollectionTargetsNormalized collections = .ok witness
  | [], _ =>
      ⟨⟨by
          intro collection collectionMember
          simp at collectionMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headNormalized :
          normalizeTargetList head = head.targets :=
        valid head (by simp)
      have encodedNormalized :
          (normalizeTargetList head).map (targetSortBytes head) =
            head.targets.map (targetSortBytes head) :=
        congrArg (List.map (targetSortBytes head)) headNormalized
      have tailValid :
          ∀ collection, collection ∈ tail →
            normalizeTargetList collection = collection.targets := by
        intro collection collectionMember
        exact valid collection (List.mem_cons_of_mem _ collectionMember)
      rcases
          validate_collection_targets_normalized_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateCollectionTargetsNormalized,
        dif_pos encodedNormalized,
        tailExact
      ]
      exact
        ⟨⟨by
            intro collection collectionMember
            exact valid collection collectionMember⟩,
          rfl⟩

private structure AllTargetsNormalizedWitness
    (nodes : List (CanonicalNode schema)) : Type where
  everyCollection : EveryCollectionTargetsNormalized nodes
  valid : EveryUnorderedTargetListSortedWithMultiplicity nodes

private theorem unordered_targets_valid_of_every_collection
    {nodes : List (CanonicalNode schema)}
    (everyCollection : EveryCollectionTargetsNormalized nodes) :
    EveryUnorderedTargetListSortedWithMultiplicity nodes := by
  intro occurrence _unordered
  have sourceBound :
      occurrence.sourceNodeIndex < nodes.length :=
    list_get?_some_bound occurrence.sourceNodeLookup
  let sourceIndex : Fin nodes.length :=
    ⟨occurrence.sourceNodeIndex, sourceBound⟩
  have sourceExact :
      nodes.get sourceIndex = occurrence.sourceNode :=
    Option.some.inj
      ((list_get?_eq_get nodes sourceIndex).symm.trans
        occurrence.sourceNodeLookup)
  have sourceMember : occurrence.sourceNode ∈ nodes := by
    rw [← sourceExact]
    exact list_get_mem_fin nodes sourceIndex
  have collectionBound :
      occurrence.owningCollectionIndex <
        occurrence.sourceNode.edgeCollections.length :=
    list_get?_some_bound occurrence.owningCollectionLookup
  let collectionIndex :
      Fin occurrence.sourceNode.edgeCollections.length :=
    ⟨occurrence.owningCollectionIndex, collectionBound⟩
  have collectionExact :
      occurrence.sourceNode.edgeCollections.get collectionIndex =
        occurrence.owningCollection :=
    Option.some.inj
      ((list_get?_eq_get
        occurrence.sourceNode.edgeCollections collectionIndex).symm.trans
        occurrence.owningCollectionLookup)
  have collectionMember :
      occurrence.owningCollection ∈
        occurrence.sourceNode.edgeCollections := by
    rw [← collectionExact]
    exact
      list_get_mem_fin
        occurrence.sourceNode.edgeCollections collectionIndex
  exact
    everyCollection
      occurrence.sourceNode sourceMember
      occurrence.owningCollection collectionMember

private theorem every_collection_targets_of_unordered_valid
    {nodes : List (CanonicalNode schema)}
    (valid : EveryUnorderedTargetListSortedWithMultiplicity nodes) :
    EveryCollectionTargetsNormalized nodes := by
  intro node nodeMember collection collectionMember
  cases collection with
  | ordered =>
      rfl
  | unordered label direction expected targets =>
      rcases List.get_of_mem nodeMember with
        ⟨nodeIndex, nodeExact⟩
      rcases List.get_of_mem collectionMember with
        ⟨collectionIndex, collectionExact⟩
      let occurrence : CanonicalCollectionOccurrence nodes :=
        { sourceNodeIndex := nodeIndex.val
          sourceNode := node
          sourceNodeLookup :=
            (list_get?_eq_get nodes nodeIndex).trans
              (congrArg some nodeExact)
          owningCollectionIndex := collectionIndex.val
          owningCollection :=
            .unordered label direction expected targets
          owningCollectionLookup :=
            (list_get?_eq_get
              node.edgeCollections collectionIndex).trans
              (congrArg some collectionExact) }
      exact valid occurrence rfl

private def validateAllTargetsNormalized :
    (nodes : List (CanonicalNode schema)) →
      GraphDecodeM (AllTargetsNormalizedWitness nodes)
  | [] =>
      .ok
        { everyCollection := by
            intro node nodeMember
            simp at nodeMember
          valid := by
            intro occurrence
            have impossible :=
              list_get?_some_bound occurrence.sourceNodeLookup
            simp at impossible }
  | head :: tail =>
      match validateCollectionTargetsNormalized head.edgeCollections with
      | .error residue =>
          .error residue
      | .ok headNormalized =>
          match validateAllTargetsNormalized tail with
          | .error residue =>
              .error residue
          | .ok tailNormalized =>
              let everyCollection :
                  EveryCollectionTargetsNormalized (head :: tail) := by
                intro node nodeMember collection collectionMember
                simp only [List.mem_cons] at nodeMember
                rcases nodeMember with nodeExact | tailMember
                · subst node
                  exact
                    headNormalized.valid collection collectionMember
                · exact
                    tailNormalized.everyCollection
                      node tailMember collection collectionMember
              .ok
                { everyCollection
                  valid := by
                    intro occurrence _unordered
                    have sourceBound :
                        occurrence.sourceNodeIndex <
                          (head :: tail).length :=
                      list_get?_some_bound occurrence.sourceNodeLookup
                    let sourceIndex : Fin (head :: tail).length :=
                      ⟨occurrence.sourceNodeIndex, sourceBound⟩
                    have sourceExact :
                        (head :: tail).get sourceIndex =
                          occurrence.sourceNode :=
                      Option.some.inj
                        ((list_get?_eq_get
                          (head :: tail) sourceIndex).symm.trans
                          occurrence.sourceNodeLookup)
                    have sourceMember :
                        occurrence.sourceNode ∈ head :: tail := by
                      rw [← sourceExact]
                      exact list_get_mem_fin (head :: tail) sourceIndex
                    have collectionBound :
                        occurrence.owningCollectionIndex <
                          occurrence.sourceNode.edgeCollections.length :=
                      list_get?_some_bound
                        occurrence.owningCollectionLookup
                    let collectionIndex :
                        Fin
                          occurrence.sourceNode.edgeCollections.length :=
                      ⟨occurrence.owningCollectionIndex,
                        collectionBound⟩
                    have collectionExact :
                        occurrence.sourceNode.edgeCollections.get
                            collectionIndex =
                          occurrence.owningCollection :=
                      Option.some.inj
                        ((list_get?_eq_get
                          occurrence.sourceNode.edgeCollections
                          collectionIndex).symm.trans
                          occurrence.owningCollectionLookup)
                    have collectionMember :
                        occurrence.owningCollection ∈
                          occurrence.sourceNode.edgeCollections := by
                      rw [← collectionExact]
                      exact
                        list_get_mem_fin
                          occurrence.sourceNode.edgeCollections
                          collectionIndex
                    exact
                      everyCollection
                        occurrence.sourceNode sourceMember
                        occurrence.owningCollection collectionMember }

private theorem validate_all_targets_of_every_collection_complete :
    ∀ {nodes : List (CanonicalNode schema)},
      EveryCollectionTargetsNormalized nodes →
      ∃ witness,
        validateAllTargetsNormalized nodes = .ok witness
  | [], _ =>
      ⟨{ everyCollection := by
            intro node nodeMember
            simp at nodeMember,
          valid := by
            intro occurrence
            have impossible :=
              list_get?_some_bound occurrence.sourceNodeLookup
            simp at impossible },
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          ∀ collection, collection ∈ head.edgeCollections →
            normalizeTargetList collection = collection.targets :=
        valid head (by simp)
      have tailValid : EveryCollectionTargetsNormalized tail := by
        intro node nodeMember
        exact valid node (List.mem_cons_of_mem _ nodeMember)
      rcases
          validate_collection_targets_normalized_complete headValid with
        ⟨headWitness, headExact⟩
      rcases
          validate_all_targets_of_every_collection_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [validateAllTargetsNormalized, headExact, tailExact]
      let everyCollection :
          EveryCollectionTargetsNormalized (head :: tail) :=
        valid
      exact
        ⟨{ everyCollection
           valid :=
             unordered_targets_valid_of_every_collection everyCollection },
          rfl⟩

private theorem validate_all_targets_normalized_complete
    {nodes : List (CanonicalNode schema)}
    (valid : EveryUnorderedTargetListSortedWithMultiplicity nodes) :
    ∃ witness,
      validateAllTargetsNormalized nodes = .ok witness :=
  validate_all_targets_of_every_collection_complete
    (every_collection_targets_of_unordered_valid valid)

private def EveryCollectionLocalReferenceBound
    (nodeCount : Nat)
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Prop :=
  ∀ collection, collection ∈ collections →
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ collection.targets →
      localIndex < nodeCount

private structure CollectionLocalReferenceBoundWitness
    (nodeCount : Nat)
    (collection :
      EdgeCollection schema (ExternalRef schema)) : Type where
  valid :
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ collection.targets →
      localIndex < nodeCount

private structure TargetLocalReferenceBoundWitness
    (nodeCount : Nat)
    (targets : List (Foundation.GraphRef (ExternalRef schema))) : Type where
  valid :
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ targets →
      localIndex < nodeCount

private def validateTargetLocalReferenceBound
    (nodeCount : Nat)
    : (targets : List (Foundation.GraphRef (ExternalRef schema))) →
      GraphDecodeM
        (TargetLocalReferenceBoundWitness nodeCount targets)
  | [] =>
      .ok ⟨by
        intro localIndex targetMember
        simp at targetMember⟩
  | .external ref :: tail =>
      match validateTargetLocalReferenceBound nodeCount tail with
      | .error residue =>
          .error residue
      | .ok tailBound =>
          .ok ⟨by
            intro localIndex targetMember
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetExact | tailMember
            · cases targetExact
            · exact tailBound.valid localIndex tailMember⟩
  | .local storedIndex :: tail =>
      if storedBound : storedIndex < nodeCount then
        match validateTargetLocalReferenceBound nodeCount tail with
        | .error residue =>
            .error residue
        | .ok tailBound =>
            .ok ⟨by
              intro localIndex targetMember
              simp only [List.mem_cons] at targetMember
              rcases targetMember with targetExact | tailMember
              · cases targetExact
                exact storedBound
              · exact tailBound.valid localIndex tailMember⟩
      else
        .error .localIndexOutOfBounds

private def validateCollectionLocalReferenceBound
    (nodeCount : Nat)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    GraphDecodeM
      (CollectionLocalReferenceBoundWitness nodeCount collection) :=
  match
      validateTargetLocalReferenceBound
        nodeCount collection.targets with
  | .error residue =>
      .error residue
  | .ok targetsBound =>
      .ok ⟨targetsBound.valid⟩

private theorem validate_target_local_reference_bound_complete
    (nodeCount : Nat) :
    ∀ {targets : List (Foundation.GraphRef (ExternalRef schema))},
      (∀ localIndex,
        Foundation.GraphRef.local localIndex ∈ targets →
        localIndex < nodeCount) →
      ∃ witness,
        validateTargetLocalReferenceBound nodeCount targets =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro localIndex targetMember
          simp at targetMember⟩,
        rfl⟩
  | .external ref :: tail, valid => by
      have tailValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ tail →
            localIndex < nodeCount := by
        intro localIndex targetMember
        exact valid localIndex (List.mem_cons_of_mem _ targetMember)
      rcases
          validate_target_local_reference_bound_complete
            nodeCount tailValid with
        ⟨tailWitness, tailExact⟩
      rw [validateTargetLocalReferenceBound, tailExact]
      exact
        ⟨⟨by
            intro localIndex targetMember
            exact valid localIndex targetMember⟩,
          rfl⟩
  | .local storedIndex :: tail, valid => by
      have storedBound : storedIndex < nodeCount :=
        valid storedIndex (by simp)
      have tailValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ tail →
            localIndex < nodeCount := by
        intro localIndex targetMember
        exact valid localIndex (List.mem_cons_of_mem _ targetMember)
      rcases
          validate_target_local_reference_bound_complete
            nodeCount tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateTargetLocalReferenceBound,
        dif_pos storedBound,
        tailExact
      ]
      exact
        ⟨⟨by
            intro localIndex targetMember
            exact valid localIndex targetMember⟩,
          rfl⟩

private theorem validate_collection_local_reference_bound_complete
    (nodeCount : Nat)
    (collection :
      EdgeCollection schema (ExternalRef schema))
    (valid :
      ∀ localIndex,
        Foundation.GraphRef.local localIndex ∈ collection.targets →
        localIndex < nodeCount) :
    ∃ witness,
      validateCollectionLocalReferenceBound nodeCount collection =
        .ok witness := by
  rcases
      validate_target_local_reference_bound_complete
        nodeCount valid with
    ⟨targetWitness, targetExact⟩
  rw [validateCollectionLocalReferenceBound, targetExact]
  exact ⟨⟨targetWitness.valid⟩, rfl⟩

private structure CollectionsLocalReferenceBoundWitness
    (nodeCount : Nat)
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Type where
  valid : EveryCollectionLocalReferenceBound nodeCount collections

private def validateCollectionsLocalReferenceBound
    (nodeCount : Nat) :
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) →
      GraphDecodeM
        (CollectionsLocalReferenceBoundWitness nodeCount collections)
  | [] =>
      .ok ⟨by
        intro collection collectionMember
        simp at collectionMember⟩
  | head :: tail =>
      match validateCollectionLocalReferenceBound nodeCount head with
      | .error residue =>
          .error residue
      | .ok headBound =>
          match validateCollectionsLocalReferenceBound nodeCount tail with
          | .error residue =>
              .error residue
          | .ok tailBound =>
              .ok ⟨by
                intro collection collectionMember
                simp only [List.mem_cons] at collectionMember
                rcases collectionMember with collectionExact | tailMember
                · subst collection
                  exact headBound.valid
                · exact tailBound.valid collection tailMember⟩

private def EveryNodeLocalReferenceBound
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ node, node ∈ nodes →
    EveryCollectionLocalReferenceBound
      nodes.length node.edgeCollections

private structure NodesLocalReferenceBoundWitness
    (nodeCount : Nat)
    (nodes : List (CanonicalNode schema)) : Type where
  valid :
    ∀ node, node ∈ nodes →
      EveryCollectionLocalReferenceBound
        nodeCount node.edgeCollections

private structure LocalReferenceBoundWitness
    (nodes : List (CanonicalNode schema)) : Type where
  everyNode : EveryNodeLocalReferenceBound nodes
  valid : EveryLocalReferenceBound nodes

private def validateNodesLocalReferenceBound
    (nodeCount : Nat) :
    (nodes : List (CanonicalNode schema)) →
      GraphDecodeM
        (NodesLocalReferenceBoundWitness nodeCount nodes)
  | [] =>
      .ok ⟨by
        intro node nodeMember
        simp at nodeMember⟩
  | head :: tail =>
      match
          validateCollectionsLocalReferenceBound
            nodeCount head.edgeCollections with
      | .error residue =>
          .error residue
      | .ok headBound =>
          match validateNodesLocalReferenceBound nodeCount tail with
          | .error residue =>
              .error residue
          | .ok tailBound =>
              .ok ⟨by
                intro node nodeMember
                simp only [List.mem_cons] at nodeMember
                rcases nodeMember with nodeExact | tailMember
                · subst node
                  exact headBound.valid
                · exact tailBound.valid node tailMember⟩

private def validateLocalReferenceBound
    (nodes : List (CanonicalNode schema)) :
    GraphDecodeM (LocalReferenceBoundWitness nodes) :=
  match validateNodesLocalReferenceBound nodes.length nodes with
  | .error residue =>
      .error residue
  | .ok everyNode =>
      .ok
        { everyNode := everyNode.valid
          valid := by
            intro occurrence
            have sourceBound :
                occurrence.sourceNodeIndex < nodes.length :=
              list_get?_some_bound occurrence.sourceNodeLookup
            let sourceIndex : Fin nodes.length :=
              ⟨occurrence.sourceNodeIndex, sourceBound⟩
            have sourceExact :
                nodes.get sourceIndex = occurrence.sourceNode :=
              Option.some.inj
                ((list_get?_eq_get nodes sourceIndex).symm.trans
                  occurrence.sourceNodeLookup)
            have sourceMember : occurrence.sourceNode ∈ nodes := by
              rw [← sourceExact]
              exact list_get_mem_fin nodes sourceIndex
            have collectionBound :
                occurrence.owningCollectionIndex <
                  occurrence.sourceNode.edgeCollections.length :=
              list_get?_some_bound occurrence.owningCollectionLookup
            let collectionIndex :
                Fin occurrence.sourceNode.edgeCollections.length :=
              ⟨occurrence.owningCollectionIndex, collectionBound⟩
            have collectionExact :
                occurrence.sourceNode.edgeCollections.get collectionIndex =
                  occurrence.owningCollection :=
              Option.some.inj
                ((list_get?_eq_get
                  occurrence.sourceNode.edgeCollections
                  collectionIndex).symm.trans
                  occurrence.owningCollectionLookup)
            have collectionMember :
                occurrence.owningCollection ∈
                  occurrence.sourceNode.edgeCollections := by
              rw [← collectionExact]
              exact
                list_get_mem_fin
                  occurrence.sourceNode.edgeCollections collectionIndex
            have targetBound :
                occurrence.targetPosition <
                  occurrence.owningCollection.targets.length :=
              list_get?_some_bound occurrence.targetExact
            let targetIndex :
                Fin occurrence.owningCollection.targets.length :=
              ⟨occurrence.targetPosition, targetBound⟩
            have targetExact :
                occurrence.owningCollection.targets.get targetIndex =
                  Foundation.GraphRef.local occurrence.localIndex :=
              Option.some.inj
                ((list_get?_eq_get
                  occurrence.owningCollection.targets
                  targetIndex).symm.trans occurrence.targetExact)
            have targetMember :
                Foundation.GraphRef.local occurrence.localIndex ∈
                  occurrence.owningCollection.targets := by
              rw [← targetExact]
              exact
                list_get_mem_fin
                  occurrence.owningCollection.targets targetIndex
            exact
              everyNode.valid
                occurrence.sourceNode sourceMember
                occurrence.owningCollection collectionMember
                occurrence.localIndex targetMember }

private theorem validate_collections_local_reference_bound_complete
    (nodeCount : Nat) :
    ∀ {collections :
        List (EdgeCollection schema (ExternalRef schema))},
      EveryCollectionLocalReferenceBound nodeCount collections →
      ∃ witness,
        validateCollectionsLocalReferenceBound nodeCount collections =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro collection collectionMember
          simp at collectionMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ head.targets →
            localIndex < nodeCount :=
        valid head (by simp)
      have tailValid :
          EveryCollectionLocalReferenceBound nodeCount tail := by
        intro collection collectionMember
        exact valid collection (List.mem_cons_of_mem _ collectionMember)
      rcases
          validate_collection_local_reference_bound_complete
            nodeCount head headValid with
        ⟨headWitness, headExact⟩
      rcases
          validate_collections_local_reference_bound_complete
            nodeCount tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateCollectionsLocalReferenceBound,
        headExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro collection collectionMember
            exact valid collection collectionMember⟩,
          rfl⟩

private theorem validate_nodes_local_reference_bound_complete
    (nodeCount : Nat) :
    ∀ {nodes : List (CanonicalNode schema)},
      (∀ node, node ∈ nodes →
        EveryCollectionLocalReferenceBound
          nodeCount node.edgeCollections) →
      ∃ witness,
        validateNodesLocalReferenceBound nodeCount nodes =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro node nodeMember
          simp at nodeMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          EveryCollectionLocalReferenceBound
            nodeCount head.edgeCollections :=
        valid head (by simp)
      have tailValid :
          ∀ node, node ∈ tail →
            EveryCollectionLocalReferenceBound
              nodeCount node.edgeCollections := by
        intro node nodeMember
        exact valid node (List.mem_cons_of_mem _ nodeMember)
      rcases
          validate_collections_local_reference_bound_complete
            nodeCount headValid with
        ⟨headWitness, headExact⟩
      rcases
          validate_nodes_local_reference_bound_complete
            nodeCount tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateNodesLocalReferenceBound,
        headExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro node nodeMember
            exact valid node nodeMember⟩,
          rfl⟩

private theorem every_node_local_reference_bound_of_valid
    {nodes : List (CanonicalNode schema)}
    (valid : EveryLocalReferenceBound nodes) :
    EveryNodeLocalReferenceBound nodes := by
  intro node nodeMember collection collectionMember
      localIndex targetMember
  rcases List.get_of_mem nodeMember with
    ⟨nodeIndex, nodeExact⟩
  rcases List.get_of_mem collectionMember with
    ⟨collectionIndex, collectionExact⟩
  rcases List.get_of_mem targetMember with
    ⟨targetIndex, targetExact⟩
  let occurrence : LocalReferenceOccurrence nodes :=
    { sourceNodeIndex := nodeIndex.val
      sourceNode := node
      sourceNodeLookup :=
        (list_get?_eq_get nodes nodeIndex).trans
          (congrArg some nodeExact)
      owningCollectionIndex := collectionIndex.val
      owningCollection := collection
      owningCollectionLookup :=
        (list_get?_eq_get node.edgeCollections collectionIndex).trans
          (congrArg some collectionExact)
      targetPosition := targetIndex.val
      localIndex
      targetExact :=
        (list_get?_eq_get collection.targets targetIndex).trans
          (congrArg some targetExact) }
  exact valid occurrence

private theorem validate_local_reference_bound_complete
    {nodes : List (CanonicalNode schema)}
    (valid : EveryLocalReferenceBound nodes) :
    ∃ witness,
      validateLocalReferenceBound nodes = .ok witness := by
  let everyNode := every_node_local_reference_bound_of_valid valid
  rcases
      validate_nodes_local_reference_bound_complete
        nodes.length everyNode with
    ⟨nodesWitness, nodesExact⟩
  rw [validateLocalReferenceBound, nodesExact]
  exact
    ⟨{ everyNode := nodesWitness.valid
       valid },
      rfl⟩

private def EveryCollectionLocalReferenceKindExact
    (kind : schema.Kind)
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Prop :=
  ∀ collection, collection ∈ collections →
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ collection.targets →
      collection.expectedTargetKind = kind

private structure TargetLocalReferenceKindExactWitness
    (kind : schema.Kind)
    (collection :
      EdgeCollection schema (ExternalRef schema))
    (targets : List (Foundation.GraphRef (ExternalRef schema))) : Type where
  valid :
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ targets →
      collection.expectedTargetKind = kind

private def validateTargetLocalReferenceKindExact
    (kind : schema.Kind)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    (targets : List (Foundation.GraphRef (ExternalRef schema))) →
    GraphDecodeM
      (TargetLocalReferenceKindExactWitness
        kind collection targets)
  | [] =>
      .ok ⟨by
        intro localIndex targetMember
        simp at targetMember⟩
  | .external ref :: tail =>
      match validateTargetLocalReferenceKindExact kind collection tail with
      | .error residue =>
          .error residue
      | .ok tailExact =>
          .ok ⟨by
            intro localIndex targetMember
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetExact | tailMember
            · cases targetExact
            · exact tailExact.valid localIndex tailMember⟩
  | .local storedIndex :: tail =>
      if kindExact :
          collection.expectedTargetKind = kind then
        match validateTargetLocalReferenceKindExact kind collection tail with
        | .error residue =>
            .error residue
        | .ok tailExact =>
            .ok ⟨by
              intro localIndex targetMember
              simp only [List.mem_cons] at targetMember
              rcases targetMember with targetExact | tailMember
              · exact kindExact
              · exact tailExact.valid localIndex tailMember⟩
      else
        .error .localTargetKindMismatch

private def validateCollectionLocalReferenceKindExact
    (kind : schema.Kind)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    GraphDecodeM
      (TargetLocalReferenceKindExactWitness
        kind collection collection.targets) :=
  validateTargetLocalReferenceKindExact
    kind collection collection.targets

private theorem validate_target_local_reference_kind_complete
    (kind : schema.Kind)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    ∀ {targets : List (Foundation.GraphRef (ExternalRef schema))},
      (∀ localIndex,
        Foundation.GraphRef.local localIndex ∈ targets →
        collection.expectedTargetKind = kind) →
      ∃ witness,
        validateTargetLocalReferenceKindExact
            kind collection targets =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro localIndex targetMember
          simp at targetMember⟩,
        rfl⟩
  | .external ref :: tail, valid => by
      have tailValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ tail →
            collection.expectedTargetKind = kind := by
        intro localIndex targetMember
        exact valid localIndex (List.mem_cons_of_mem _ targetMember)
      rcases
          validate_target_local_reference_kind_complete
            kind collection tailValid with
        ⟨tailWitness, tailExact⟩
      rw [validateTargetLocalReferenceKindExact, tailExact]
      exact
        ⟨⟨by
            intro localIndex targetMember
            exact valid localIndex targetMember⟩,
          rfl⟩
  | .local storedIndex :: tail, valid => by
      have kindExact : collection.expectedTargetKind = kind :=
        valid storedIndex (by simp)
      have tailValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ tail →
            collection.expectedTargetKind = kind := by
        intro localIndex targetMember
        exact valid localIndex (List.mem_cons_of_mem _ targetMember)
      rcases
          validate_target_local_reference_kind_complete
            kind collection tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateTargetLocalReferenceKindExact,
        dif_pos kindExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro localIndex targetMember
            exact valid localIndex targetMember⟩,
          rfl⟩

private theorem validate_collection_local_reference_kind_complete
    (kind : schema.Kind)
    (collection :
      EdgeCollection schema (ExternalRef schema))
    (valid :
      ∀ localIndex,
        Foundation.GraphRef.local localIndex ∈ collection.targets →
        collection.expectedTargetKind = kind) :
    ∃ witness,
      validateCollectionLocalReferenceKindExact kind collection =
        .ok witness := by
  exact
    validate_target_local_reference_kind_complete
      kind collection valid

private structure CollectionsLocalReferenceKindExactWitness
    (kind : schema.Kind)
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Type where
  valid : EveryCollectionLocalReferenceKindExact kind collections

private def validateCollectionsLocalReferenceKindExact
    (kind : schema.Kind) :
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) →
      GraphDecodeM
        (CollectionsLocalReferenceKindExactWitness kind collections)
  | [] =>
      .ok ⟨by
        intro collection collectionMember
        simp at collectionMember⟩
  | head :: tail =>
      match validateCollectionLocalReferenceKindExact kind head with
      | .error residue =>
          .error residue
      | .ok headExact =>
          match validateCollectionsLocalReferenceKindExact kind tail with
          | .error residue =>
              .error residue
          | .ok tailExact =>
              .ok ⟨by
                intro collection collectionMember
                simp only [List.mem_cons] at collectionMember
                rcases collectionMember with collectionExact | tailMember
                · subst collection
                  exact headExact.valid
                · exact tailExact.valid collection tailMember⟩

private theorem validate_collections_local_reference_kind_complete
    (kind : schema.Kind) :
    ∀ {collections :
        List (EdgeCollection schema (ExternalRef schema))},
      EveryCollectionLocalReferenceKindExact kind collections →
      ∃ witness,
        validateCollectionsLocalReferenceKindExact kind collections =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro collection collectionMember
          simp at collectionMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ head.targets →
            head.expectedTargetKind = kind :=
        valid head (by simp)
      have tailValid :
          EveryCollectionLocalReferenceKindExact kind tail := by
        intro collection collectionMember
        exact valid collection (List.mem_cons_of_mem _ collectionMember)
      rcases
          validate_collection_local_reference_kind_complete
            kind head headValid with
        ⟨headWitness, headExact⟩
      rcases
          validate_collections_local_reference_kind_complete
            kind tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateCollectionsLocalReferenceKindExact,
        headExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro collection collectionMember
            exact valid collection collectionMember⟩,
          rfl⟩

private def EveryNodeLocalReferenceKindExact
    (kind : schema.Kind)
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ node, node ∈ nodes →
    EveryCollectionLocalReferenceKindExact
      kind node.edgeCollections

private structure NodesLocalReferenceKindExactWitness
    (kind : schema.Kind)
    (nodes : List (CanonicalNode schema)) : Type where
  valid : EveryNodeLocalReferenceKindExact kind nodes

private structure LocalReferenceKindExactWitness
    (kind : schema.Kind)
    (nodes : List (CanonicalNode schema)) : Type where
  everyNode : EveryNodeLocalReferenceKindExact kind nodes
  valid : EveryLocalReferenceExpectedKindExact kind nodes

private def validateNodesLocalReferenceKindExact
    (kind : schema.Kind) :
    (nodes : List (CanonicalNode schema)) →
      GraphDecodeM
        (NodesLocalReferenceKindExactWitness kind nodes)
  | [] =>
      .ok ⟨by
        intro node nodeMember
        simp at nodeMember⟩
  | head :: tail =>
      match
          validateCollectionsLocalReferenceKindExact
            kind head.edgeCollections with
      | .error residue =>
          .error residue
      | .ok headExact =>
          match validateNodesLocalReferenceKindExact kind tail with
          | .error residue =>
              .error residue
          | .ok tailExact =>
              .ok ⟨by
                intro node nodeMember
                simp only [List.mem_cons] at nodeMember
                rcases nodeMember with nodeExact | tailMember
                · subst node
                  exact headExact.valid
                · exact tailExact.valid node tailMember⟩

private def validateLocalReferenceKindExact
    (kind : schema.Kind)
    (nodes : List (CanonicalNode schema)) :
    GraphDecodeM (LocalReferenceKindExactWitness kind nodes) :=
  match validateNodesLocalReferenceKindExact kind nodes with
  | .error residue =>
      .error residue
  | .ok everyNode =>
      .ok
        { everyNode := everyNode.valid
          valid := by
            intro occurrence
            have sourceBound :
                occurrence.sourceNodeIndex < nodes.length :=
              list_get?_some_bound occurrence.sourceNodeLookup
            let sourceIndex : Fin nodes.length :=
              ⟨occurrence.sourceNodeIndex, sourceBound⟩
            have sourceExact :
                nodes.get sourceIndex = occurrence.sourceNode :=
              Option.some.inj
                ((list_get?_eq_get nodes sourceIndex).symm.trans
                  occurrence.sourceNodeLookup)
            have sourceMember : occurrence.sourceNode ∈ nodes := by
              rw [← sourceExact]
              exact list_get_mem_fin nodes sourceIndex
            have collectionBound :
                occurrence.owningCollectionIndex <
                  occurrence.sourceNode.edgeCollections.length :=
              list_get?_some_bound occurrence.owningCollectionLookup
            let collectionIndex :
                Fin occurrence.sourceNode.edgeCollections.length :=
              ⟨occurrence.owningCollectionIndex, collectionBound⟩
            have collectionExact :
                occurrence.sourceNode.edgeCollections.get collectionIndex =
                  occurrence.owningCollection :=
              Option.some.inj
                ((list_get?_eq_get
                  occurrence.sourceNode.edgeCollections
                  collectionIndex).symm.trans
                  occurrence.owningCollectionLookup)
            have collectionMember :
                occurrence.owningCollection ∈
                  occurrence.sourceNode.edgeCollections := by
              rw [← collectionExact]
              exact
                list_get_mem_fin
                  occurrence.sourceNode.edgeCollections collectionIndex
            have targetBound :
                occurrence.targetPosition <
                  occurrence.owningCollection.targets.length :=
              list_get?_some_bound occurrence.targetExact
            let targetIndex :
                Fin occurrence.owningCollection.targets.length :=
              ⟨occurrence.targetPosition, targetBound⟩
            have targetExact :
                occurrence.owningCollection.targets.get targetIndex =
                  Foundation.GraphRef.local occurrence.localIndex :=
              Option.some.inj
                ((list_get?_eq_get
                  occurrence.owningCollection.targets
                  targetIndex).symm.trans occurrence.targetExact)
            have targetMember :
                Foundation.GraphRef.local occurrence.localIndex ∈
                  occurrence.owningCollection.targets := by
              rw [← targetExact]
              exact
                list_get_mem_fin
                  occurrence.owningCollection.targets targetIndex
            exact
              everyNode.valid
                occurrence.sourceNode sourceMember
                occurrence.owningCollection collectionMember
                occurrence.localIndex targetMember }

private theorem validate_nodes_local_reference_kind_complete
    (kind : schema.Kind) :
    ∀ {nodes : List (CanonicalNode schema)},
      EveryNodeLocalReferenceKindExact kind nodes →
      ∃ witness,
        validateNodesLocalReferenceKindExact kind nodes =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro node nodeMember
          simp at nodeMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          EveryCollectionLocalReferenceKindExact
            kind head.edgeCollections :=
        valid head (by simp)
      have tailValid :
          EveryNodeLocalReferenceKindExact kind tail := by
        intro node nodeMember
        exact valid node (List.mem_cons_of_mem _ nodeMember)
      rcases
          validate_collections_local_reference_kind_complete
            kind headValid with
        ⟨headWitness, headExact⟩
      rcases
          validate_nodes_local_reference_kind_complete
            kind tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateNodesLocalReferenceKindExact,
        headExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro node nodeMember
            exact valid node nodeMember⟩,
          rfl⟩

private theorem every_node_local_reference_kind_of_valid
    {kind : schema.Kind}
    {nodes : List (CanonicalNode schema)}
    (valid : EveryLocalReferenceExpectedKindExact kind nodes) :
    EveryNodeLocalReferenceKindExact kind nodes := by
  intro node nodeMember collection collectionMember
      localIndex targetMember
  rcases List.get_of_mem nodeMember with
    ⟨nodeIndex, nodeExact⟩
  rcases List.get_of_mem collectionMember with
    ⟨collectionIndex, collectionExact⟩
  rcases List.get_of_mem targetMember with
    ⟨targetIndex, targetExact⟩
  let occurrence : LocalReferenceOccurrence nodes :=
    { sourceNodeIndex := nodeIndex.val
      sourceNode := node
      sourceNodeLookup :=
        (list_get?_eq_get nodes nodeIndex).trans
          (congrArg some nodeExact)
      owningCollectionIndex := collectionIndex.val
      owningCollection := collection
      owningCollectionLookup :=
        (list_get?_eq_get node.edgeCollections collectionIndex).trans
          (congrArg some collectionExact)
      targetPosition := targetIndex.val
      localIndex
      targetExact :=
        (list_get?_eq_get collection.targets targetIndex).trans
          (congrArg some targetExact) }
  exact valid occurrence

private theorem validate_local_reference_kind_complete
    {kind : schema.Kind}
    {nodes : List (CanonicalNode schema)}
    (valid : EveryLocalReferenceExpectedKindExact kind nodes) :
    ∃ witness,
      validateLocalReferenceKindExact kind nodes = .ok witness := by
  let everyNode :=
    every_node_local_reference_kind_of_valid valid
  rcases
      validate_nodes_local_reference_kind_complete
        kind everyNode with
    ⟨nodesWitness, nodesExact⟩
  rw [validateLocalReferenceKindExact, nodesExact]
  exact
    ⟨{ everyNode := nodesWitness.valid
       valid },
      rfl⟩

private def EveryCollectionHasNoLocalReference
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Prop :=
  ∀ collection, collection ∈ collections →
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ collection.targets →
      False

private structure TargetHasNoLocalReferenceWitness
    (targets : List (Foundation.GraphRef (ExternalRef schema))) : Type where
  valid :
    ∀ localIndex,
      Foundation.GraphRef.local localIndex ∈ targets →
      False

private def validateTargetsHaveNoLocalReference :
    (targets : List (Foundation.GraphRef (ExternalRef schema))) →
      GraphDecodeM (TargetHasNoLocalReferenceWitness targets)
  | [] =>
      .ok ⟨by
        intro localIndex targetMember
        simp at targetMember⟩
  | .external ref :: tail =>
      match validateTargetsHaveNoLocalReference tail with
      | .error residue =>
          .error residue
      | .ok tailExternal =>
          .ok ⟨by
            intro localIndex targetMember
            simp only [List.mem_cons] at targetMember
            rcases targetMember with targetExact | tailMember
            · cases targetExact
            · exact tailExternal.valid localIndex tailMember⟩
  | .local _ :: _ =>
      .error .localRefInDag

private theorem validate_targets_have_no_local_complete :
    ∀ {targets : List (Foundation.GraphRef (ExternalRef schema))},
      (∀ localIndex,
        Foundation.GraphRef.local localIndex ∈ targets →
        False) →
      ∃ witness,
        validateTargetsHaveNoLocalReference targets = .ok witness
  | [], _ =>
      ⟨⟨by
          intro localIndex targetMember
          simp at targetMember⟩,
        rfl⟩
  | .external ref :: tail, valid => by
      have tailValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ tail →
            False := by
        intro localIndex targetMember
        exact valid localIndex (List.mem_cons_of_mem _ targetMember)
      rcases
          validate_targets_have_no_local_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [validateTargetsHaveNoLocalReference, tailExact]
      exact
        ⟨⟨by
            intro localIndex targetMember
            exact valid localIndex targetMember⟩,
          rfl⟩
  | .local storedIndex :: tail, valid =>
      False.elim (valid storedIndex (by simp))

private structure CollectionsHaveNoLocalReferenceWitness
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) : Type where
  valid : EveryCollectionHasNoLocalReference collections

private def validateCollectionsHaveNoLocalReference :
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) →
      GraphDecodeM
        (CollectionsHaveNoLocalReferenceWitness collections)
  | [] =>
      .ok ⟨by
        intro collection collectionMember
        simp at collectionMember⟩
  | head :: tail =>
      match validateTargetsHaveNoLocalReference head.targets with
      | .error residue =>
          .error residue
      | .ok headExternal =>
          match validateCollectionsHaveNoLocalReference tail with
          | .error residue =>
              .error residue
          | .ok tailExternal =>
              .ok ⟨by
                intro collection collectionMember
                simp only [List.mem_cons] at collectionMember
                rcases collectionMember with collectionExact | tailMember
                · subst collection
                  exact headExternal.valid
                · exact
                    tailExternal.valid collection tailMember⟩

private theorem validate_collections_have_no_local_complete :
    ∀ {collections :
        List (EdgeCollection schema (ExternalRef schema))},
      EveryCollectionHasNoLocalReference collections →
      ∃ witness,
        validateCollectionsHaveNoLocalReference collections =
          .ok witness
  | [], _ =>
      ⟨⟨by
          intro collection collectionMember
          simp at collectionMember⟩,
        rfl⟩
  | head :: tail, valid => by
      have headValid :
          ∀ localIndex,
            Foundation.GraphRef.local localIndex ∈ head.targets →
            False :=
        valid head (by simp)
      have tailValid : EveryCollectionHasNoLocalReference tail := by
        intro collection collectionMember
        exact valid collection (List.mem_cons_of_mem _ collectionMember)
      rcases validate_targets_have_no_local_complete headValid with
        ⟨headWitness, headExact⟩
      rcases validate_collections_have_no_local_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [
        validateCollectionsHaveNoLocalReference,
        headExact,
        tailExact
      ]
      exact
        ⟨⟨by
            intro collection collectionMember
            exact valid collection collectionMember⟩,
          rfl⟩

private def EveryNodeHasNoLocalReference
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ node, node ∈ nodes →
    EveryCollectionHasNoLocalReference node.edgeCollections

private structure NoLocalReferenceWitness
    (nodes : List (CanonicalNode schema)) : Type where
  everyNode : EveryNodeHasNoLocalReference nodes
  valid : NoLocalReference nodes

private def validateNoLocalReference :
    (nodes : List (CanonicalNode schema)) →
      GraphDecodeM (NoLocalReferenceWitness nodes)
  | [] =>
      .ok
        { everyNode := by
            intro node nodeMember
            simp at nodeMember
          valid := by
            intro occurrence
            have impossible :=
              list_get?_some_bound occurrence.sourceNodeLookup
            simp at impossible }
  | head :: tail =>
      match validateCollectionsHaveNoLocalReference head.edgeCollections with
      | .error residue =>
          .error residue
      | .ok headExternal =>
          match validateNoLocalReference tail with
          | .error residue =>
              .error residue
          | .ok tailExternal =>
              let everyNode :
                  EveryNodeHasNoLocalReference (head :: tail) := by
                intro node nodeMember
                simp only [List.mem_cons] at nodeMember
                rcases nodeMember with nodeExact | tailMember
                · subst node
                  exact headExternal.valid
                · exact tailExternal.everyNode node tailMember
              .ok
                { everyNode
                  valid := by
                    intro occurrence
                    have sourceBound :
                        occurrence.sourceNodeIndex <
                          (head :: tail).length :=
                      list_get?_some_bound occurrence.sourceNodeLookup
                    let sourceIndex : Fin (head :: tail).length :=
                      ⟨occurrence.sourceNodeIndex, sourceBound⟩
                    have sourceExact :
                        (head :: tail).get sourceIndex =
                          occurrence.sourceNode :=
                      Option.some.inj
                        ((list_get?_eq_get
                          (head :: tail) sourceIndex).symm.trans
                          occurrence.sourceNodeLookup)
                    have sourceMember :
                        occurrence.sourceNode ∈ head :: tail := by
                      rw [← sourceExact]
                      exact list_get_mem_fin (head :: tail) sourceIndex
                    have collectionBound :
                        occurrence.owningCollectionIndex <
                          occurrence.sourceNode.edgeCollections.length :=
                      list_get?_some_bound
                        occurrence.owningCollectionLookup
                    let collectionIndex :
                        Fin
                          occurrence.sourceNode.edgeCollections.length :=
                      ⟨occurrence.owningCollectionIndex,
                        collectionBound⟩
                    have collectionExact :
                        occurrence.sourceNode.edgeCollections.get
                            collectionIndex =
                          occurrence.owningCollection :=
                      Option.some.inj
                        ((list_get?_eq_get
                          occurrence.sourceNode.edgeCollections
                          collectionIndex).symm.trans
                          occurrence.owningCollectionLookup)
                    have collectionMember :
                        occurrence.owningCollection ∈
                          occurrence.sourceNode.edgeCollections := by
                      rw [← collectionExact]
                      exact
                        list_get_mem_fin
                          occurrence.sourceNode.edgeCollections
                          collectionIndex
                    have targetBound :
                        occurrence.targetPosition <
                          occurrence.owningCollection.targets.length :=
                      list_get?_some_bound occurrence.targetExact
                    let targetIndex :
                        Fin occurrence.owningCollection.targets.length :=
                      ⟨occurrence.targetPosition, targetBound⟩
                    have targetExact :
                        occurrence.owningCollection.targets.get
                            targetIndex =
                          Foundation.GraphRef.local
                            occurrence.localIndex :=
                      Option.some.inj
                        ((list_get?_eq_get
                          occurrence.owningCollection.targets
                          targetIndex).symm.trans
                          occurrence.targetExact)
                    have targetMember :
                        Foundation.GraphRef.local occurrence.localIndex ∈
                          occurrence.owningCollection.targets := by
                      rw [← targetExact]
                      exact
                        list_get_mem_fin
                          occurrence.owningCollection.targets targetIndex
                    exact
                      everyNode
                        occurrence.sourceNode sourceMember
                        occurrence.owningCollection collectionMember
                        occurrence.localIndex targetMember }

private theorem no_local_reference_of_every_node
    {nodes : List (CanonicalNode schema)}
    (everyNode : EveryNodeHasNoLocalReference nodes) :
    NoLocalReference nodes := by
  intro occurrence
  have sourceBound :
      occurrence.sourceNodeIndex < nodes.length :=
    list_get?_some_bound occurrence.sourceNodeLookup
  let sourceIndex : Fin nodes.length :=
    ⟨occurrence.sourceNodeIndex, sourceBound⟩
  have sourceExact :
      nodes.get sourceIndex = occurrence.sourceNode :=
    Option.some.inj
      ((list_get?_eq_get nodes sourceIndex).symm.trans
        occurrence.sourceNodeLookup)
  have sourceMember : occurrence.sourceNode ∈ nodes := by
    rw [← sourceExact]
    exact list_get_mem_fin nodes sourceIndex
  have collectionBound :
      occurrence.owningCollectionIndex <
        occurrence.sourceNode.edgeCollections.length :=
    list_get?_some_bound occurrence.owningCollectionLookup
  let collectionIndex :
      Fin occurrence.sourceNode.edgeCollections.length :=
    ⟨occurrence.owningCollectionIndex, collectionBound⟩
  have collectionExact :
      occurrence.sourceNode.edgeCollections.get collectionIndex =
        occurrence.owningCollection :=
    Option.some.inj
      ((list_get?_eq_get
        occurrence.sourceNode.edgeCollections collectionIndex).symm.trans
        occurrence.owningCollectionLookup)
  have collectionMember :
      occurrence.owningCollection ∈
        occurrence.sourceNode.edgeCollections := by
    rw [← collectionExact]
    exact
      list_get_mem_fin
        occurrence.sourceNode.edgeCollections collectionIndex
  have targetBound :
      occurrence.targetPosition <
        occurrence.owningCollection.targets.length :=
    list_get?_some_bound occurrence.targetExact
  let targetIndex :
      Fin occurrence.owningCollection.targets.length :=
    ⟨occurrence.targetPosition, targetBound⟩
  have targetExact :
      occurrence.owningCollection.targets.get targetIndex =
        Foundation.GraphRef.local occurrence.localIndex :=
    Option.some.inj
      ((list_get?_eq_get
        occurrence.owningCollection.targets targetIndex).symm.trans
        occurrence.targetExact)
  have targetMember :
      Foundation.GraphRef.local occurrence.localIndex ∈
        occurrence.owningCollection.targets := by
    rw [← targetExact]
    exact
      list_get_mem_fin
        occurrence.owningCollection.targets targetIndex
  exact
    everyNode
      occurrence.sourceNode sourceMember
      occurrence.owningCollection collectionMember
      occurrence.localIndex targetMember

private theorem every_node_has_no_local_of_valid
    {nodes : List (CanonicalNode schema)}
    (valid : NoLocalReference nodes) :
    EveryNodeHasNoLocalReference nodes := by
  intro node nodeMember collection collectionMember
      localIndex targetMember
  rcases List.get_of_mem nodeMember with
    ⟨nodeIndex, nodeExact⟩
  rcases List.get_of_mem collectionMember with
    ⟨collectionIndex, collectionExact⟩
  rcases List.get_of_mem targetMember with
    ⟨targetIndex, targetExact⟩
  let occurrence : LocalReferenceOccurrence nodes :=
    { sourceNodeIndex := nodeIndex.val
      sourceNode := node
      sourceNodeLookup :=
        (list_get?_eq_get nodes nodeIndex).trans
          (congrArg some nodeExact)
      owningCollectionIndex := collectionIndex.val
      owningCollection := collection
      owningCollectionLookup :=
        (list_get?_eq_get node.edgeCollections collectionIndex).trans
          (congrArg some collectionExact)
      targetPosition := targetIndex.val
      localIndex
      targetExact :=
        (list_get?_eq_get collection.targets targetIndex).trans
          (congrArg some targetExact) }
  exact valid occurrence

private theorem validate_no_local_reference_complete :
    ∀ {nodes : List (CanonicalNode schema)},
      NoLocalReference nodes →
      ∃ witness,
        validateNoLocalReference nodes = .ok witness
  | [], valid =>
      ⟨{ everyNode :=
            every_node_has_no_local_of_valid valid,
          valid },
        rfl⟩
  | head :: tail, valid => by
      let everyNode := every_node_has_no_local_of_valid valid
      have headValid :
          EveryCollectionHasNoLocalReference head.edgeCollections :=
        everyNode head (by simp)
      have tailEveryNode : EveryNodeHasNoLocalReference tail := by
        intro node nodeMember
        exact everyNode node (List.mem_cons_of_mem _ nodeMember)
      have tailValid : NoLocalReference tail :=
        no_local_reference_of_every_node tailEveryNode
      rcases
          validate_collections_have_no_local_complete headValid with
        ⟨headWitness, headExact⟩
      rcases validate_no_local_reference_complete tailValid with
        ⟨tailWitness, tailExact⟩
      rw [validateNoLocalReference, headExact, tailExact]
      exact
        ⟨{ everyNode,
           valid },
          rfl⟩

private structure CanonicalBlockWellFormedWitness
    (block : CanonicalBlock schema kind) : Type where
  valid : CanonicalBlockWellFormed block

private def validateCanonicalBlockWellFormed
    (schema : GraphKindSchema)
    (kind : schema.Kind) :
    (block : CanonicalBlock schema kind) →
      GraphDecodeM (CanonicalBlockWellFormedWitness block)
  | block@(.dagSingleton node) =>
      match validateNoLocalReference [node] with
      | .error residue =>
          .error residue
      | .ok noLocal =>
          match validateLocalReferenceBound [node] with
          | .error residue =>
              .error residue
          | .ok localBound =>
              match validateLocalReferenceKindExact kind [node] with
              | .error residue =>
                  .error residue
              | .ok localKind =>
                  match validateAllTargetsNormalized [node] with
                  | .error residue =>
                      .error residue
                  | .ok targetsNormalized =>
                      match validateOuterCollectionsNormalized [node] with
                      | .error residue =>
                          .error residue
                      | .ok collectionsNormalized =>
                          .ok ⟨
                            { form := noLocal.valid
                              localReferencesBound := localBound.valid
                              localReferenceKindsExact := localKind.valid
                              unorderedTargetsNormalized :=
                                targetsNormalized.valid
                              outerCollectionsNormalized :=
                                collectionsNormalized.valid
                              canonicalTLV :=
                                decode_encode_canonical_block
                                  schema kind
                                    (.dagSingleton node) }⟩
  | .cyclic [] =>
      .error .localConnectivityRefused
  | block@(.cyclic (head :: tail)) =>
      match validateLocalReferenceBound (head :: tail) with
      | .error residue =>
          .error residue
      | .ok localBound =>
          match validateLocalReferenceKindExact kind (head :: tail) with
          | .error residue =>
              .error residue
          | .ok localKind =>
              match validateAllTargetsNormalized (head :: tail) with
              | .error residue =>
                  .error residue
              | .ok targetsNormalized =>
                  match
                      validateOuterCollectionsNormalized (head :: tail) with
                  | .error residue =>
                      .error residue
                  | .ok collectionsNormalized =>
                      .ok ⟨
                        { form := by simp
                          localReferencesBound := localBound.valid
                          localReferenceKindsExact := localKind.valid
                          unorderedTargetsNormalized :=
                            targetsNormalized.valid
                          outerCollectionsNormalized :=
                            collectionsNormalized.valid
                          canonicalTLV :=
                            decode_encode_canonical_block
                              schema kind
                                (.cyclic (head :: tail)) }⟩

private theorem validate_canonical_block_well_formed_complete
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (block : CanonicalBlock schema kind)
    (wellFormed : CanonicalBlockWellFormed block) :
    ∃ witness,
      validateCanonicalBlockWellFormed schema kind block =
        .ok witness := by
  cases block with
  | dagSingleton node =>
      have localBoundValid : EveryLocalReferenceBound [node] := by
        simpa using wellFormed.localReferencesBound
      have localKindValid :
          EveryLocalReferenceExpectedKindExact kind [node] := by
        simpa using wellFormed.localReferenceKindsExact
      have targetsValid :
          EveryUnorderedTargetListSortedWithMultiplicity [node] := by
        simpa using wellFormed.unorderedTargetsNormalized
      have collectionsValid :
          EveryOuterCollectionListSortedWithMultiplicity [node] := by
        simpa using wellFormed.outerCollectionsNormalized
      rcases
          validate_no_local_reference_complete wellFormed.form with
        ⟨noLocal, noLocalExact⟩
      rcases
          validate_local_reference_bound_complete
            localBoundValid with
        ⟨localBound, localBoundExact⟩
      rcases
          validate_local_reference_kind_complete
            localKindValid with
        ⟨localKind, localKindExact⟩
      rcases
          validate_all_targets_normalized_complete
            targetsValid with
        ⟨targetsNormalized, targetsExact⟩
      rcases
          validate_outer_collections_normalized_complete
            collectionsValid with
        ⟨collectionsNormalized, collectionsExact⟩
      rw [
        validateCanonicalBlockWellFormed,
        noLocalExact,
        localBoundExact,
        localKindExact,
        targetsExact,
        collectionsExact
      ]
      exact ⟨⟨wellFormed⟩, rfl⟩
  | cyclic nodes =>
      cases nodes with
      | nil =>
          exact False.elim (wellFormed.form rfl)
      | cons head tail =>
          have localBoundValid :
              EveryLocalReferenceBound (head :: tail) := by
            simpa using wellFormed.localReferencesBound
          have localKindValid :
              EveryLocalReferenceExpectedKindExact
                kind (head :: tail) := by
            simpa using wellFormed.localReferenceKindsExact
          have targetsValid :
              EveryUnorderedTargetListSortedWithMultiplicity
                (head :: tail) := by
            simpa using wellFormed.unorderedTargetsNormalized
          have collectionsValid :
              EveryOuterCollectionListSortedWithMultiplicity
                (head :: tail) := by
            simpa using wellFormed.outerCollectionsNormalized
          rcases
              validate_local_reference_bound_complete
                localBoundValid with
            ⟨localBound, localBoundExact⟩
          rcases
              validate_local_reference_kind_complete
                localKindValid with
            ⟨localKind, localKindExact⟩
          rcases
              validate_all_targets_normalized_complete
                targetsValid with
            ⟨targetsNormalized, targetsExact⟩
          rcases
              validate_outer_collections_normalized_complete
                collectionsValid with
            ⟨collectionsNormalized, collectionsExact⟩
          rw [
            validateCanonicalBlockWellFormed,
            localBoundExact,
            localKindExact,
            targetsExact,
            collectionsExact
          ]
          exact ⟨⟨wellFormed⟩, rfl⟩

private structure CanonicalRegistryWellFormedWitness
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Type where
  valid : CanonicalRegistryWellFormed context registry

private def validateCanonicalRegistryWellFormed
    (context : GraphCodecContext) :
    (registry : List (SomeCanonicalBlock context)) →
      GraphDecodeM
        (CanonicalRegistryWellFormedWitness context registry)
  | [] =>
      .ok ⟨
        { blocks := by
            intro index
            exact False.elim (Nat.not_lt_zero index.val index.isLt) }⟩
  | head :: tail =>
      match
          validateCanonicalBlockWellFormed
            context.kindSchema head.kind head.block with
      | .error residue =>
          .error residue
      | .ok headWellFormed =>
          match validateCanonicalRegistryWellFormed context tail with
          | .error residue =>
              .error residue
          | .ok tailWellFormed =>
              .ok ⟨
                { blocks := by
                    intro index
                    cases index with
                    | mk value bound =>
                        cases value with
                        | zero =>
                            exact headWellFormed.valid
                        | succ value =>
                            have tailBound : value < tail.length :=
                              Nat.succ_lt_succ_iff.mp bound
                            exact
                              tailWellFormed.valid.blocks
                                ⟨value, tailBound⟩ }⟩

private theorem validate_canonical_registry_well_formed_complete
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (wellFormed : CanonicalRegistryWellFormed context registry) :
    ∃ witness,
      validateCanonicalRegistryWellFormed context registry =
        .ok witness := by
  induction registry with
  | nil =>
      exact
        ⟨⟨
          { blocks := by
              intro index
              exact
                False.elim
                  (Nat.not_lt_zero index.val index.isLt) }⟩,
          rfl⟩
  | cons head tail tailIH =>
      have headWellFormed :
          CanonicalBlockWellFormed head.block :=
        wellFormed.blocks ⟨0, by simp⟩
      have tailWellFormed :
          CanonicalRegistryWellFormed context tail :=
        { blocks := by
            intro index
            exact
              wellFormed.blocks
                ⟨index.val.succ,
                  Nat.succ_lt_succ index.isLt⟩ }
      rcases
          validate_canonical_block_well_formed_complete
            context.kindSchema head.kind head.block headWellFormed with
        ⟨headWitness, headExact⟩
      rcases tailIH tailWellFormed with
        ⟨tailWitness, tailExact⟩
      rw [
        validateCanonicalRegistryWellFormed,
        headExact,
        tailExact
      ]
      exact ⟨_, rfl⟩

private theorem resolve_public_occurrence_list_complete_from_table
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    ∀ occurrences : List (PublicReferenceOccurrence registry),
      ∃ edges,
        resolvePublicOccurrenceList keysUnique occurrences =
          .ok edges := by
  intro occurrences
  induction occurrences with
  | nil =>
      exact ⟨[], rfl⟩
  | cons occurrence remaining remainingIH =>
      simp only [resolvePublicOccurrenceList]
      split
      · rename_i residue resolutionExact
        rcases table.complete occurrence with
          ⟨edge, _edgeMember, edgeOccurrenceExact⟩
        cases edgeOccurrenceExact
        have edgeResolutionExact := edge.resolutionExact
        rw [resolutionExact] at edgeResolutionExact
        cases edgeResolutionExact
      · rcases remainingIH with
          ⟨remainingEdges, remainingExact⟩
        rw [remainingExact]
        exact ⟨_, rfl⟩

private theorem validate_public_occurrences_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    ∃ validated,
      validatePublicOccurrences registry keysUnique =
        .ok validated := by
  rcases
      resolve_public_occurrence_list_complete_from_table table
        (enumeratePublicReferenceOccurrences registry) with
    ⟨edges, edgesExact⟩
  unfold validatePublicOccurrences
  split
  · rename_i residue resolvedExact
    rw [resolvedExact] at edgesExact
    cases edgesExact
  · exact ⟨_, rfl⟩

private theorem validate_resolved_edges_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysNoDup :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysNoDup) :
    ∃ validated,
      validateResolvedEdges registry keysNoDup =
        .ok validated := by
  rcases validate_public_occurrences_complete table with
    ⟨validatedTable, validatedExact⟩
  unfold validateResolvedEdges
  split
  · exact ⟨_, rfl⟩
  · rename_i residue validationFailure
    rw [validationFailure] at validatedExact
    cases validatedExact

private def pureMinimizingPermutations
    (block : CanonicalBlock schema kind) :
    List (PermutationWitness block.nodes.length) :=
  (permutationWitnesses block.nodes.length).filter fun permutation =>
    decide
      (encodeCanonicalBlock
          (pureMaterializeCanonicalBlock block permutation) =
        lexicographicMinimum
          (pureCanonicalCandidateBytes block)
          (pure_candidate_bytes_nonempty block))

private theorem pure_minimizing_permutation_mem_iff
    (block : CanonicalBlock schema kind)
    (permutation : PermutationWitness block.nodes.length) :
    permutation ∈ pureMinimizingPermutations block ↔
      permutation ∈ permutationWitnesses block.nodes.length ∧
      encodeCanonicalBlock
          (pureMaterializeCanonicalBlock block permutation) =
        lexicographicMinimum
          (pureCanonicalCandidateBytes block)
          (pure_candidate_bytes_nonempty block) := by
  simp [pureMinimizingPermutations]

private theorem encode_canonical_block_injective_local
    {left right : CanonicalBlock schema kind}
    (encodedExact :
      encodeCanonicalBlock left = encodeCanonicalBlock right) :
    left = right := by
  have decodedExact :=
    congrArg
      (decodeCanonicalBlockDetailed schema kind)
      encodedExact
  simpa [
    decode_encode_canonical_block schema kind left,
    decode_encode_canonical_block schema kind right
  ] using decodedExact

private structure BlockCanonicalMinimumWitness
    (block : CanonicalBlock schema kind) : Type where
  valid : BlockStoredAtCanonicalMinimum block

private def validateCyclicBlockCanonicalMinimum
    (nodes : List (CanonicalNode schema))
    (wellFormed :
      CanonicalBlockWellFormed
        (.cyclic nodes : CanonicalBlock schema kind)) :
    GraphDecodeM
      (BlockCanonicalMinimumWitness
        (.cyclic nodes : CanonicalBlock schema kind)) :=
  let block : CanonicalBlock schema kind := .cyclic nodes
  match uniqueExact : pureMinimizingPermutations block with
  | [permutation] =>
      let selectedMaterialization :=
        pureMaterializeCanonicalBlock block permutation
      if storedMinimum :
          encodeCanonicalBlock block =
            encodeCanonicalBlock selectedMaterialization then
        have selectedMember :
            permutation ∈ pureMinimizingPermutations block := by
          rw [uniqueExact]
          simp
        have selectedMinimum :
            encodeCanonicalBlock selectedMaterialization =
              lexicographicMinimum
                (pureCanonicalCandidateBytes block)
                (pure_candidate_bytes_nonempty block) :=
          (pure_minimizing_permutation_mem_iff
            block permutation).mp selectedMember |>.2
        have storedEquals :
            block = selectedMaterialization :=
          encode_canonical_block_injective_local storedMinimum
        .ok ⟨.cyclicSelected wellFormed
          { selectedPermutation := permutation
            allCandidateBytes := pureCanonicalCandidateBytes block
            allCandidateBytesExact := rfl
            selectedMaterialization := selectedMaterialization
            selectedMaterializationExact := rfl
            selectedBytesAreMinimum := selectedMinimum
            selectedPermutationUniqueProducer := by
              intro other otherExact
              have otherMinimum :
                  encodeCanonicalBlock
                      (pureMaterializeCanonicalBlock block other) =
                    lexicographicMinimum
                      (pureCanonicalCandidateBytes block)
                      (pure_candidate_bytes_nonempty block) :=
                otherExact.trans selectedMinimum
              have otherMember :
                  other ∈ pureMinimizingPermutations block :=
                (pure_minimizing_permutation_mem_iff
                  block other).mpr
                    ⟨permutation_witnesses_complete other,
                      otherMinimum⟩
              rw [uniqueExact] at otherMember
              simpa using otherMember
            storedEqualsSelectedMinimum := storedEquals }⟩
      else
        .error .blockNotCanonicalMinimum
  | _ =>
      .error .ambiguousCanonicalLabel

private def validateBlockCanonicalMinimum :
    (block : CanonicalBlock schema kind) →
      CanonicalBlockWellFormed block →
      GraphDecodeM (BlockCanonicalMinimumWitness block)
  | .dagSingleton node, wellFormed =>
      .ok ⟨.dagTrivial node rfl wellFormed⟩
  | .cyclic nodes, wellFormed =>
      validateCyclicBlockCanonicalMinimum nodes wellFormed

private theorem pure_minimizing_permutations_eq_singleton
    (block : CanonicalBlock schema kind)
    (certificate : StoredAtCanonicalMinimum block) :
    pureMinimizingPermutations block =
      [certificate.selectedPermutation] := by
  have selectedMinimum :
      encodeCanonicalBlock
          (pureMaterializeCanonicalBlock
            block certificate.selectedPermutation) =
        lexicographicMinimum
          (pureCanonicalCandidateBytes block)
          (pure_candidate_bytes_nonempty block) := by
    simpa [
      certificate.allCandidateBytesExact,
      certificate.selectedMaterializationExact
    ] using certificate.selectedBytesAreMinimum
  have selectedMember :
      certificate.selectedPermutation ∈
        pureMinimizingPermutations block :=
    (pure_minimizing_permutation_mem_iff
      block certificate.selectedPermutation).mpr
        ⟨permutation_witnesses_complete _,
          selectedMinimum⟩
  have everyMemberExact :
      ∀ permutation,
        permutation ∈ pureMinimizingPermutations block →
          permutation = certificate.selectedPermutation := by
    intro permutation permutationMember
    have permutationMinimum :=
      (pure_minimizing_permutation_mem_iff
        block permutation).mp permutationMember |>.2
    exact
      certificate.selectedPermutationUniqueProducer
        permutation
        ((permutationMinimum.trans selectedMinimum.symm).trans
          (congrArg encodeCanonicalBlock
            certificate.selectedMaterializationExact.symm))
  have minimizersNoDuplicates :
      NoDuplicates (pureMinimizingPermutations block) := by
    unfold pureMinimizingPermutations
    exact
      (permutation_witnesses_no_duplicates block.nodes.length).filter _
  cases minimizersExact :
      pureMinimizingPermutations block with
  | nil =>
      rw [minimizersExact] at selectedMember
      simp at selectedMember
  | cons first rest =>
      have firstExact :
          first = certificate.selectedPermutation :=
        everyMemberExact first (by
          rw [minimizersExact]
          simp)
      have restEmpty : rest = [] := by
        cases rest with
        | nil =>
            rfl
        | cons second tail =>
            have secondMember :
                second ∈ pureMinimizingPermutations block := by
              rw [minimizersExact]
              exact
                List.mem_cons.mpr
                  (Or.inr
                    (List.mem_cons.mpr (Or.inl rfl)))
            have secondExact :
                second = certificate.selectedPermutation :=
              everyMemberExact second secondMember
            rw [minimizersExact] at minimizersNoDuplicates
            have firstNeSecond : first ≠ second :=
              (List.pairwise_cons.mp minimizersNoDuplicates).1
                second
                (List.mem_cons.mpr (Or.inl rfl))
            exact
              False.elim
                (firstNeSecond
                  (firstExact.trans secondExact.symm))
      rw [firstExact, restEmpty]

private theorem validate_block_canonical_minimum_complete
    (block : CanonicalBlock schema kind)
    (wellFormed : CanonicalBlockWellFormed block)
    (minimum : BlockStoredAtCanonicalMinimum block) :
    ∃ witness,
      validateBlockCanonicalMinimum block wellFormed =
        .ok witness := by
  cases block with
  | dagSingleton node =>
      exact ⟨_, rfl⟩
  | cyclic nodes =>
      cases minimum with
      | dagTrivial node blockExact _ =>
          cases blockExact
      | cyclicSelected _ certificate =>
          have uniqueExact :=
            pure_minimizing_permutations_eq_singleton
              (.cyclic nodes) certificate
          have storedMinimum :
              encodeCanonicalBlock
                  (.cyclic nodes :
                    CanonicalBlock schema kind) =
                encodeCanonicalBlock
                  (pureMaterializeCanonicalBlock
                    (.cyclic nodes :
                      CanonicalBlock schema kind)
                    certificate.selectedPermutation) := by
            apply congrArg encodeCanonicalBlock
            exact
              certificate.storedEqualsSelectedMinimum.trans
                certificate.selectedMaterializationExact
          simp only [validateBlockCanonicalMinimum]
          unfold validateCyclicBlockCanonicalMinimum
          dsimp only
          split
          · rename_i permutation minimizingExact
            have permutationExact :
                permutation =
                  certificate.selectedPermutation := by
              have singletonExact :=
                uniqueExact.symm.trans minimizingExact
              simpa using singletonExact.symm
            subst permutation
            split
            · exact ⟨_, rfl⟩
            · rename_i notStoredMinimum
              exact False.elim (notStoredMinimum storedMinimum)
          · rename_i noSingleton
            exact
              False.elim
                (noSingleton
                  certificate.selectedPermutation uniqueExact)

private structure RegistryCanonicalMinimaWitness
    (registry : List (SomeCanonicalBlock context)) : Type where
  valid : EveryBlockStoredAtCanonicalMinimum registry

private def validateRegistryCanonicalMinima
    (context : GraphCodecContext) :
    (registry : List (SomeCanonicalBlock context)) →
      CanonicalRegistryWellFormed context registry →
      GraphDecodeM (RegistryCanonicalMinimaWitness registry)
  | [], _ =>
      .ok ⟨by
        intro entry entryMember
        simp at entryMember⟩
  | head :: tail, wellFormed =>
      let headWellFormed :
          CanonicalBlockWellFormed head.block :=
        wellFormed.blocks ⟨0, by simp⟩
      let tailWellFormed :
          CanonicalRegistryWellFormed context tail :=
        { blocks := by
            intro index
            exact
              wellFormed.blocks
                ⟨index.val.succ,
                  Nat.succ_lt_succ index.isLt⟩ }
      match
          validateBlockCanonicalMinimum
            head.block headWellFormed with
      | .error residue =>
          .error residue
      | .ok headMinimum =>
          match
              validateRegistryCanonicalMinima
                context tail tailWellFormed with
          | .error residue =>
              .error residue
          | .ok tailMinimum =>
              .ok ⟨by
                intro entry entryMember
                simp only [List.mem_cons] at entryMember
                rcases entryMember with entryExact | tailMember
                · subst entry
                  exact headMinimum.valid
                · exact tailMinimum.valid entry tailMember⟩

private theorem validate_registry_canonical_minima_complete
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (wellFormed : CanonicalRegistryWellFormed context registry)
    (minimum : EveryBlockStoredAtCanonicalMinimum registry) :
    ∃ witness,
      validateRegistryCanonicalMinima
          context registry wellFormed =
        .ok witness := by
  induction registry with
  | nil =>
      exact
        ⟨⟨by
          intro entry entryMember
          simp at entryMember⟩,
          rfl⟩
  | cons head tail tailIH =>
      let headWellFormed :
          CanonicalBlockWellFormed head.block :=
        wellFormed.blocks ⟨0, by simp⟩
      let tailWellFormed :
          CanonicalRegistryWellFormed context tail :=
        { blocks := by
            intro index
            exact
              wellFormed.blocks
                ⟨index.val.succ,
                  Nat.succ_lt_succ index.isLt⟩ }
      have headMinimum :
          BlockStoredAtCanonicalMinimum head.block :=
        minimum head (by simp)
      have tailMinimum :
          EveryBlockStoredAtCanonicalMinimum tail := by
        intro entry entryMember
        exact minimum entry (by simp [entryMember])
      rcases
          validate_block_canonical_minimum_complete
            head.block headWellFormed headMinimum with
        ⟨headWitness, headExact⟩
      rcases
          tailIH tailWellFormed tailMinimum with
        ⟨tailWitness, tailExact⟩
      simp only [validateRegistryCanonicalMinima]
      split
      · rename_i residue headFailure
        rw [headFailure] at headExact
        cases headExact
      · split
        · rename_i residue tailFailure
          rw [tailFailure] at tailExact
          cases tailExact
        · exact ⟨_, rfl⟩

private structure ValidatedCanonicalGraph
    (context : GraphCodecContext) : Type where
  graph : ClosedRootedGraph context
  resolvedEdgeTable :
    validatePublicOccurrences
      graph.canonicalRegistry graph.registryKeysNoDup =
        .ok graph.resolvedEdges
  dependencyExact :
    buildDependencyCertificate graph.resolvedEdges =
      .ok graph.dependency

private def decodeCanonicalGraphValidated
    (context : GraphCodecContext)
    (_injective : GraphDigestInjective context)
    (bytes : GraphBytes) :
    Except GraphDecodeResidue (ValidatedCanonicalGraph context) := do
  let parsed ← parseCanonicalGraphSyntax context bytes
  let registryOrder ←
    validateRegistryOrder context parsed.registry
  let registryWellFormed ←
    validateCanonicalRegistryWellFormed context parsed.registry
  let resolvedEdges ←
    validateResolvedEdges
      parsed.registry registryOrder.keysNoDup
  let connectivity ←
    validateConnectivity parsed.registry
  let dependency ←
    validateDependency resolvedEdges.table
  let canonicalMinima ←
    validateRegistryCanonicalMinima
      context parsed.registry registryWellFormed.valid
  let blockAddresses ←
    validateBlockAddressesDerived context parsed.registry
  let canonicalRoot ←
    validateRootPointer context parsed.registry parsed.root
  let graph : ClosedRootedGraph context :=
    { canonicalRegistry := parsed.registry
      canonicalRoot
      registryStrictlySorted := registryOrder.strictlySorted
      registryKeysNoDup := registryOrder.keysNoDup
      registryWellFormed := registryWellFormed.valid
      connectivity := connectivity.valid
      resolvedEdges := resolvedEdges.table
      dependency := dependency.certificate
      blockAddressesDerived := blockAddresses.valid
      canonicalMinima := canonicalMinima.valid }
  .ok
    { graph
      resolvedEdgeTable := resolvedEdges.exact
      dependencyExact := dependency.exact }

private theorem decode_canonical_graph_validated_encode
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context) :
    ∃ validated,
      decodeCanonicalGraphValidated context injective
          (encodeCanonicalGraph context graph) =
        .ok validated ∧
      serializedCanonicalProjection validated.graph =
        serializedCanonicalProjection graph := by
  have parsedExact :=
    parse_canonical_graph_syntax_encode context graph
  rcases
      validate_registry_order_complete
        context graph.canonicalRegistry
          graph.registryKeysNoDup
          graph.registryStrictlySorted with
    ⟨registryOrder, registryOrderExact⟩
  rcases
      validate_canonical_registry_well_formed_complete
        context graph.canonicalRegistry
          graph.registryWellFormed with
    ⟨registryWellFormed, registryWellFormedExact⟩
  rcases
      validate_resolved_edges_complete graph.resolvedEdges with
    ⟨resolvedEdges, resolvedEdgesExact⟩
  rcases
      validate_connectivity_complete
        graph.canonicalRegistry graph.connectivity with
    ⟨connectivity, connectivityExact⟩
  rcases
      rebuild_dependency_from_equivalent_table
        graph.resolvedEdges graph.dependency
          resolvedEdges.table with
    ⟨rebuiltDependency, rebuiltDependencyExact⟩
  rcases
      validate_dependency_complete
        resolvedEdges.table rebuiltDependency
          rebuiltDependencyExact with
    ⟨dependency, dependencyExact⟩
  rcases
      validate_registry_canonical_minima_complete
        context graph.canonicalRegistry
          graph.registryWellFormed graph.canonicalMinima with
    ⟨canonicalMinima, canonicalMinimaExact⟩
  rcases
      validate_block_addresses_derived_complete
        context graph.canonicalRegistry
          graph.blockAddressesDerived with
    ⟨blockAddresses, blockAddressesExact⟩
  rcases
      validate_root_pointer_complete
        context graph.registryKeysNoDup
          graph.canonicalRoot with
    ⟨canonicalRoot, canonicalRootExact,
      rootBlockExact, rootLocalExact⟩
  unfold decodeCanonicalGraphValidated
  simp only [Bind.bind, Except.bind]
  rw [parsedExact]
  simp only
  rw [registryOrderExact]
  simp only
  rw [registryWellFormedExact]
  simp only
  rw [resolvedEdgesExact]
  simp only
  rw [connectivityExact]
  simp only
  rw [dependencyExact]
  simp only
  rw [canonicalMinimaExact]
  simp only
  rw [blockAddressesExact]
  simp only
  rw [canonicalRootExact]
  refine ⟨_, rfl, ?_⟩
  simp [
    serializedCanonicalProjection,
    rootBlockExact,
    rootLocalExact
  ]

def decodeCanonicalGraphDetailed
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (bytes : GraphBytes) :
    Except GraphDecodeResidue (ClosedRootedGraph context) :=
  match decodeCanonicalGraphValidated context injective bytes with
  | .error residue =>
      .error residue
  | .ok validated =>
      if encodeCanonicalGraph context validated.graph = bytes then
        .ok validated.graph
      else
        .error .noncanonicalReencoding

theorem decode_detailed_encode_observation
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context) :
    ∃ decoded,
      decodeCanonicalGraphDetailed context injective
          (encodeCanonicalGraph context graph) = .ok decoded ∧
      serializedCanonicalProjection decoded =
        serializedCanonicalProjection graph := by
  rcases
      decode_canonical_graph_validated_encode context injective graph with
    ⟨validated, validatedExact, observationExact⟩
  have reencodedExact :
      encodeCanonicalGraph context validated.graph =
        encodeCanonicalGraph context graph :=
    encode_canonical_graph_factors_serialized_projection observationExact
  refine ⟨validated.graph, ?_, observationExact⟩
  unfold decodeCanonicalGraphDetailed
  rw [validatedExact]
  simp [reencodedExact]

theorem decode_encode_never_duplicate_refusal
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context) :
    decodeCanonicalGraphDetailed context injective
        (encodeCanonicalGraph context graph) ≠
      .error .duplicateRegistryKey := by
  rcases
      decode_detailed_encode_observation context injective graph with
    ⟨decoded, accepted, _⟩
  rw [accepted]
  simp

theorem decode_detailed_reencodes_exact
    {context : GraphCodecContext}
    {injective : GraphDigestInjective context}
    {bytes : GraphBytes}
    {graph : ClosedRootedGraph context}
    (accepted :
      decodeCanonicalGraphDetailed context injective bytes = .ok graph) :
    encodeCanonicalGraph context graph = bytes := by
  unfold decodeCanonicalGraphDetailed at accepted
  cases validated :
      decodeCanonicalGraphValidated context injective bytes with
  | error residue =>
      simp [validated] at accepted
  | ok decoded =>
      simp only [validated] at accepted
      split at accepted
      next canonicalExact =>
        cases accepted
        exact canonicalExact
      next canonicalDifferent =>
        contradiction

theorem decode_graph_bytes_ambient_free
    {context : GraphCodecContext}
    {injective : GraphDigestInjective context}
    {bytes : GraphBytes}
    {graph : ClosedRootedGraph context}
    (accepted :
      decodeCanonicalGraphDetailed context injective bytes = .ok graph) :
    PureDecodeWitness context bytes graph := by
  unfold decodeCanonicalGraphDetailed at accepted
  cases validatedExact :
      decodeCanonicalGraphValidated context injective bytes with
  | error residue =>
      simp [validatedExact] at accepted
  | ok validated =>
      simp only [validatedExact] at accepted
      split at accepted
      next canonicalExact =>
        cases accepted
        exact
          { canonicalRegistryWellFormed :=
              validated.graph.registryWellFormed
            resolvedEdgeTable := validated.resolvedEdgeTable
            internalReferentialClosure :=
              ⟨validated.graph.resolvedEdges,
                validated.resolvedEdgeTable⟩
            computedConnectivity :=
              validated.graph.connectivity
            computedDependency :=
              ⟨validated.graph.dependency,
                validated.dependencyExact, rfl⟩
            recomputedAddresses :=
              validated.graph.blockAddressesDerived
            canonicalReencoding := canonicalExact }
      next canonicalDifferent =>
        contradiction

theorem decode_encode_domain_exact
    (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
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
        decoded.canonicalRegistry := by
  rcases
      decode_detailed_encode_observation context injective graph with
    ⟨decoded, accepted, _⟩
  have witness := decode_graph_bytes_ambient_free accepted
  exact
    ⟨decoded, accepted,
      witness.canonicalRegistryWellFormed,
      witness.resolvedEdgeTable,
      decoded.canonicalMinima⟩

end Residua.RCC.Addressing.AddressedGraph


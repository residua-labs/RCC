import RCC.AddressedGraphConnectivity

/-!
# RCC addressed-graph whole-registry closure

AK-6A validates a finite raw rooted graph after AK-5 address resolution and
before AK-6B canonicalization.  Raw candidate bounds and resolved canonical
bounds deliberately remain independent: AK-6B, rather than this module, owns
the canonicalization bridge.
-/

open Residua.RCC.Addressing

namespace Residua.RCC.Addressing.AddressedGraph.Closure

/-! ## Raw addressed registry -/

structure RawRegistryKey
    (schema : GraphKindSchema) (kind : schema.Kind) where
  claimedBlockQ : GraphWireAddress (schema.toAddressKind kind)

structure RawInRegistryRef (schema : GraphKindSchema) where
  kind : schema.Kind
  targetKey : RawRegistryKey schema kind
  rawTargetMemberIndex : Nat

abbrev RawGraphRef (schema : GraphKindSchema) :=
  GraphRef (RawInRegistryRef schema)

abbrev RawNode (schema : GraphKindSchema) :=
  GraphNode schema (RawInRegistryRef schema)

inductive RawBlockCandidate
    (schema : GraphKindSchema) (sourceKind : schema.Kind)
  | dagSingleton :
      RawNode schema → RawBlockCandidate schema sourceKind
  | cyclic :
      (nodes : List (RawNode schema)) →
      Option (ConnectivityCertificate nodes) →
      RawBlockCandidate schema sourceKind

def RawBlockCandidate.nodes :
    RawBlockCandidate schema sourceKind → List (RawNode schema)
  | .dagSingleton node => [node]
  | .cyclic nodes _ => nodes

def RawBlockCandidate.nodeCount :
    RawBlockCandidate schema sourceKind → Nat
  | .dagSingleton _ => 1
  | .cyclic nodes _ => nodes.length

structure RawBlockEntry
    (schema : GraphKindSchema) (kind : schema.Kind) where
  claimedBlockQ : GraphWireAddress (schema.toAddressKind kind)
  dependencyRank : Nat
  candidate : RawBlockCandidate schema kind

structure SomeRawBlockEntry (schema : GraphKindSchema) where
  kind : schema.Kind
  entry : RawBlockEntry schema kind

structure RawRootedGraph (schema : GraphKindSchema) where
  blockRegistry : List (SomeRawBlockEntry schema)
  root : RawInRegistryRef schema

structure RawKeyIdentity where
  kindCode : Nat
  algorithm : GraphText
  domainQ : GraphText
  schemaQ : GraphText
  digest : GraphText
  deriving DecidableEq, Repr

def rawKeyIdentity
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (key : RawRegistryKey schema kind) :
    RawKeyIdentity :=
  { kindCode := schema.kindCode kind
    algorithm := key.claimedBlockQ.algorithm
    domainQ := key.claimedBlockQ.domainQ
    schemaQ := key.claimedBlockQ.schemaQ
    digest := key.claimedBlockQ.digest }

def registryEntryKeyIdentity
    (schema : GraphKindSchema)
    (wrapped : SomeRawBlockEntry schema) :
    RawKeyIdentity :=
  rawKeyIdentity schema wrapped.kind
    ⟨wrapped.entry.claimedBlockQ⟩

structure TypedRegistryMember
    (registry : List (SomeRawBlockEntry schema))
    (key : RawRegistryKey schema kind)
    (entry : RawBlockEntry schema kind) : Type where
  wrapped : SomeRawBlockEntry schema
  wrappedMember : wrapped ∈ registry
  kindEq : wrapped.kind = kind
  entryEq : HEq wrapped.entry entry
  keyEq : entry.claimedBlockQ = key.claimedBlockQ

def normalizedTypedRegistryEntry
    (entry : RawBlockEntry schema kind) :
    SomeRawBlockEntry schema :=
  { kind := kind
    entry := entry }

theorem typed_registry_member_wrapped_eq_normalized
    (member : TypedRegistryMember registry key entry) :
    member.wrapped = normalizedTypedRegistryEntry entry := by
  rcases member with
    ⟨wrapped, wrappedMember, kindEq, entryEq, keyEq⟩
  cases kindEq
  cases entryEq
  rfl

theorem normalized_typed_registry_entry_mem
    (member : TypedRegistryMember registry key entry) :
    normalizedTypedRegistryEntry entry ∈ registry := by
  rw [← typed_registry_member_wrapped_eq_normalized member]
  exact member.wrappedMember

theorem typed_registry_member_key_identity
    {schema : GraphKindSchema}
    {kind : schema.Kind}
    {registry : List (SomeRawBlockEntry schema)}
    {key : RawRegistryKey schema kind}
    {entry : RawBlockEntry schema kind}
    (member : TypedRegistryMember registry key entry) :
    registryEntryKeyIdentity schema member.wrapped =
      rawKeyIdentity schema kind key := by
  rcases member with
    ⟨wrapped, wrappedMember, kindEq, entryEq, keyEq⟩
  cases kindEq
  cases entryEq
  simp [registryEntryKeyIdentity, keyEq]

private def liftTypedRegistryMember
    (head : SomeRawBlockEntry schema)
    (member : TypedRegistryMember tail key entry) :
    TypedRegistryMember (head :: tail) key entry where
  wrapped := member.wrapped
  wrappedMember := List.mem_cons_of_mem head member.wrappedMember
  kindEq := member.kindEq
  entryEq := member.entryEq
  keyEq := member.keyEq

def findTypedRegistryMember
    (registry : List (SomeRawBlockEntry schema))
    (key : RawRegistryKey schema kind) :
    Option (Σ entry, TypedRegistryMember registry key entry) :=
  letI : DecidableEq schema.Kind := schema.decideKindEq
  match registry with
  | [] => none
  | head :: tail =>
      if kindEqual : head.kind = kind then
        let entry : RawBlockEntry schema kind :=
          kindEqual ▸ head.entry
        if keyEqual :
            entry.claimedBlockQ = key.claimedBlockQ then
          have entryEqual : HEq head.entry entry := by
            cases kindEqual
            rfl
          some
            ⟨entry,
              { wrapped := head
                wrappedMember := by simp
                kindEq := kindEqual
                entryEq := entryEqual
                keyEq := keyEqual }⟩
        else
          (findTypedRegistryMember tail key).map fun result =>
            ⟨result.1, liftTypedRegistryMember head result.2⟩
      else
        (findTypedRegistryMember tail key).map fun result =>
          ⟨result.1, liftTypedRegistryMember head result.2⟩

def rawTargetCandidateNodeCount
    (graph : RawRootedGraph schema)
    (ref : RawInRegistryRef schema) : Option Nat :=
  match findTypedRegistryMember graph.blockRegistry ref.targetKey with
  | none => none
  | some target => some target.1.candidate.nodeCount

structure RawTargetMember
    (graph : RawRootedGraph schema)
    (ref : RawInRegistryRef schema) : Type where
  targetEntry : RawBlockEntry schema ref.kind
  targetEntryMember :
    TypedRegistryMember graph.blockRegistry ref.targetKey targetEntry
  targetNodeCountLookup :
    rawTargetCandidateNodeCount graph ref =
      some targetEntry.candidate.nodeCount

def RawTargetMemberBound
    (target : RawTargetMember graph ref) : Prop :=
  ref.rawTargetMemberIndex <
    target.targetEntry.candidate.nodeCount

/-! ## Owned external occurrences -/

structure RawExternalOccurrence (schema : GraphKindSchema) where
  ownerKind : schema.Kind
  ownerKey : RawRegistryKey schema ownerKind
  ownerRank : Nat
  expectedTargetKind : schema.Kind
  ref : RawInRegistryRef schema

private def externalOccurrencesInTargets
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat)
    (expectedKind : schema.Kind) :
    List (RawGraphRef schema) → List (RawExternalOccurrence schema)
  | [] => []
  | .local _ :: rest =>
      externalOccurrencesInTargets
        ownerKind ownerKey ownerRank expectedKind rest
  | .external ref :: rest =>
      { ownerKind := ownerKind
        ownerKey := ownerKey
        ownerRank := ownerRank
        expectedTargetKind := expectedKind
        ref := ref } ::
      externalOccurrencesInTargets
        ownerKind ownerKey ownerRank expectedKind rest

private def externalOccurrencesInCollections
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat) :
    List (EdgeCollection schema (RawInRegistryRef schema)) →
      List (RawExternalOccurrence schema)
  | [] => []
  | collection :: rest =>
      externalOccurrencesInTargets
          ownerKind ownerKey ownerRank
          collection.expectedTargetKind collection.targets ++
        externalOccurrencesInCollections ownerKind ownerKey ownerRank rest

private def externalOccurrencesInNodes
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat) :
    List (RawNode schema) → List (RawExternalOccurrence schema)
  | [] => []
  | node :: rest =>
      externalOccurrencesInCollections
          ownerKind ownerKey ownerRank node.edgeCollections ++
        externalOccurrencesInNodes ownerKind ownerKey ownerRank rest

private def externalOccurrencesInEntry
    (kind : schema.Kind) (entry : RawBlockEntry schema kind) :
    List (RawExternalOccurrence schema) :=
  externalOccurrencesInNodes kind
    ⟨entry.claimedBlockQ⟩ entry.dependencyRank entry.candidate.nodes

def rawExternalOccurrences
    (graph : RawRootedGraph schema) :
    List (RawExternalOccurrence schema) :=
  graph.blockRegistry.flatMap fun wrapped =>
    externalOccurrencesInEntry wrapped.kind wrapped.entry

def RawReferenceOccurs
    (graph : RawRootedGraph schema)
    (ref : RawInRegistryRef schema) : Prop :=
  ref ∈ (rawExternalOccurrences graph).map RawExternalOccurrence.ref

theorem raw_reference_occurs_of_occurrence_member
    (graph : RawRootedGraph schema)
    (occurrence : RawExternalOccurrence schema)
    (member : occurrence ∈ rawExternalOccurrences graph) :
    RawReferenceOccurs graph occurrence.ref := by
  unfold RawReferenceOccurs
  apply List.mem_map.mpr
  exact ⟨occurrence, member, rfl⟩

private theorem external_occurrences_in_targets_complete
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat)
    (expectedKind : schema.Kind)
    (ref : RawInRegistryRef schema) :
    ∀ (targets : List (RawGraphRef schema)) (targetPosition : Nat),
      targets[targetPosition]? =
          some (.external ref : RawGraphRef schema) →
      { ownerKind := ownerKind
        ownerKey := ownerKey
        ownerRank := ownerRank
        expectedTargetKind := expectedKind
        ref := ref } ∈
        externalOccurrencesInTargets
          ownerKind ownerKey ownerRank expectedKind targets := by
  intro targets
  induction targets with
  | nil =>
      intro targetPosition lookup
      simp at lookup
  | cons head tail ih =>
      intro targetPosition lookup
      cases targetPosition with
      | zero =>
          cases head with
          | «local» index =>
              simp at lookup
          | external target =>
              simp at lookup
              subst target
              simp [externalOccurrencesInTargets]
      | succ prior =>
          cases head with
          | «local» index =>
              simp [externalOccurrencesInTargets]
              apply ih prior
              simpa using lookup
          | external target =>
              simp [externalOccurrencesInTargets]
              apply Or.inr
              apply ih prior
              simpa using lookup

private theorem external_occurrences_in_collections_complete
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat)
    (collection :
      EdgeCollection schema (RawInRegistryRef schema))
    (collectionMember : collection ∈ collections)
    (targetPosition : Nat)
    (ref : RawInRegistryRef schema)
    (targetLookup :
      collection.targets[targetPosition]? =
        some (.external ref : RawGraphRef schema)) :
    { ownerKind := ownerKind
      ownerKey := ownerKey
      ownerRank := ownerRank
      expectedTargetKind := collection.expectedTargetKind
      ref := ref } ∈
      externalOccurrencesInCollections
        ownerKind ownerKey ownerRank collections := by
  induction collections with
  | nil =>
      simp at collectionMember
  | cons head tail ih =>
      rcases List.mem_cons.mp collectionMember with
        equal | tailMember
      · subst collection
        apply List.mem_append.mpr
        exact Or.inl
          (external_occurrences_in_targets_complete
            ownerKind ownerKey ownerRank head.expectedTargetKind
            ref head.targets targetPosition targetLookup)
      · apply List.mem_append.mpr
        exact Or.inr (ih tailMember)

private theorem external_occurrences_in_nodes_complete
    (ownerKind : schema.Kind)
    (ownerKey : RawRegistryKey schema ownerKind)
    (ownerRank : Nat)
    (node : RawNode schema)
    (nodeMember : node ∈ nodes)
    (collection :
      EdgeCollection schema (RawInRegistryRef schema))
    (collectionMember : collection ∈ node.edgeCollections)
    (targetPosition : Nat)
    (ref : RawInRegistryRef schema)
    (targetLookup :
      collection.targets[targetPosition]? =
        some (.external ref : RawGraphRef schema)) :
    { ownerKind := ownerKind
      ownerKey := ownerKey
      ownerRank := ownerRank
      expectedTargetKind := collection.expectedTargetKind
      ref := ref } ∈
      externalOccurrencesInNodes
        ownerKind ownerKey ownerRank nodes := by
  induction nodes with
  | nil =>
      simp at nodeMember
  | cons head tail ih =>
      rcases List.mem_cons.mp nodeMember with
        equal | tailMember
      · subst node
        apply List.mem_append.mpr
        exact Or.inl
          (external_occurrences_in_collections_complete
            ownerKind ownerKey ownerRank collection
            collectionMember targetPosition ref targetLookup)
      · apply List.mem_append.mpr
        exact Or.inr (ih tailMember)

theorem raw_external_occurrence_mem_of_exact_position
    (graph : RawRootedGraph schema)
    (source : SomeRawBlockEntry schema)
    (sourceMember : source ∈ graph.blockRegistry)
    (sourceNodeIndex owningCollectionIndex targetPosition : Nat)
    (node : RawNode schema)
    (collection :
      EdgeCollection schema (RawInRegistryRef schema))
    (ref : RawInRegistryRef schema)
    (nodeLookup :
      source.entry.candidate.nodes[sourceNodeIndex]? = some node)
    (collectionLookup :
      node.edgeCollections[owningCollectionIndex]? = some collection)
    (targetLookup :
      collection.targets[targetPosition]? =
        some (.external ref : RawGraphRef schema)) :
    { ownerKind := source.kind
      ownerKey := ⟨source.entry.claimedBlockQ⟩
      ownerRank := source.entry.dependencyRank
      expectedTargetKind := collection.expectedTargetKind
      ref := ref } ∈
      rawExternalOccurrences graph := by
  unfold rawExternalOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨source, sourceMember, ?_⟩
  unfold externalOccurrencesInEntry
  have nodeMember :
      node ∈ source.entry.candidate.nodes :=
    List.mem_iff_getElem.mpr
      ⟨sourceNodeIndex,
        List.getElem?_eq_some_iff.mp nodeLookup⟩
  have collectionMember :
      collection ∈ node.edgeCollections :=
    List.mem_iff_getElem.mpr
      ⟨owningCollectionIndex,
        List.getElem?_eq_some_iff.mp collectionLookup⟩
  exact external_occurrences_in_nodes_complete
    source.kind ⟨source.entry.claimedBlockQ⟩
    source.entry.dependencyRank node nodeMember collection
    collectionMember targetPosition ref targetLookup

theorem raw_reference_occurs_of_exact_position
    (graph : RawRootedGraph schema)
    (source : SomeRawBlockEntry schema)
    (sourceMember : source ∈ graph.blockRegistry)
    (sourceNodeIndex owningCollectionIndex targetPosition : Nat)
    (node : RawNode schema)
    (collection :
      EdgeCollection schema (RawInRegistryRef schema))
    (ref : RawInRegistryRef schema)
    (nodeLookup :
      source.entry.candidate.nodes[sourceNodeIndex]? = some node)
    (collectionLookup :
      node.edgeCollections[owningCollectionIndex]? = some collection)
    (targetLookup :
      collection.targets[targetPosition]? =
        some (.external ref : RawGraphRef schema)) :
    RawReferenceOccurs graph ref := by
  apply raw_reference_occurs_of_occurrence_member graph
    { ownerKind := source.kind
      ownerKey := ⟨source.entry.claimedBlockQ⟩
      ownerRank := source.entry.dependencyRank
      expectedTargetKind := collection.expectedTargetKind
      ref := ref }
  exact raw_external_occurrence_mem_of_exact_position
    graph source sourceMember sourceNodeIndex owningCollectionIndex
    targetPosition node collection ref nodeLookup collectionLookup
    targetLookup

/-! ## Validation residues and AK-5 evidence -/

inductive GraphValidationResidue
  | emptyRegistry
  | duplicateBlockKey
  | rootNotInRegistry
  | unreachableRegistryBlock
  | localRefInDag
  | emptyCyclicBlock
  | connectivityCertificateMissing
  | localConnectivityRefused
  | localIndexOutOfBounds
  | externalBlockNotFound
  | externalRehashMismatch
  | externalDecodeRefused
  | externalNoncanonicalBytes
  | externalTargetNotInRegistry
  | rawTargetMemberIndexOutOfBounds
  | resolvedCanonicalMemberIndexOutOfBounds
  | targetKindMismatch
  | crossBlockRankNotStrict
  deriving DecidableEq, Repr

def mapExternalResolution :
    StoreResolveResult α → Except GraphValidationResidue α
  | .resolved value => .ok value
  | .notFound => .error .externalBlockNotFound
  | .rehashMismatch => .error .externalRehashMismatch
  | .decodeRefused => .error .externalDecodeRefused
  | .noncanonicalBytes => .error .externalNoncanonicalBytes

private theorem map_external_resolution_ok_iff
    (result : StoreResolveResult α) (value : α) :
    mapExternalResolution result = .ok value ↔
      result = .resolved value := by
  cases result <;> simp [mapExternalResolution]

structure ResolvedRawTarget
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (ref : RawInRegistryRef context.kindSchema) : Type where
  canonicalBlock : CanonicalBlock context.kindSchema ref.kind
  resolvedByAK5 :
    resolveAddressed
      (context.blockBinding ref.kind)
      (ingest.blockRuntimeCodec ref.kind)
      (ingest.blockStore ref.kind)
      ref.targetKey.claimedBlockQ.toAddress = .resolved canonicalBlock
  resolvedCanonicalIndexBound :
    ref.rawTargetMemberIndex < canonicalBlock.nodes.length

structure ResolvedTargetEvidence
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema)
    (ref : RawInRegistryRef context.kindSchema) : Type where
  target : RawTargetMember graph ref
  rawBound : RawTargetMemberBound target
  resolved : ResolvedRawTarget context ingest ref

theorem raw_ingest_noncanonical_unreachable
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (kind : context.kindSchema.Kind)
    (requested :
      Address (context.kindSchema.toAddressKind kind)) :
    resolveAddressed
        (context.blockBinding kind)
        (ingest.blockRuntimeCodec kind)
        (ingest.blockStore kind)
        requested ≠ .noncanonicalBytes := by
  intro noncanonical
  cases stored :
      ingest.blockStore kind requested with
  | none =>
      simp [resolveAddressed, stored] at noncanonical
  | some bytes =>
      by_cases rehashed :
          (context.blockBinding kind).address bytes = requested
      · cases decoded :
          (ingest.blockRuntimeCodec kind).decode bytes with
        | none =>
            simp [resolveAddressed, stored, rehashed, decoded] at noncanonical
        | some block =>
            have exactDecoded :
                (constructiveBlockCodec context.kindSchema kind).decode bytes =
                  some block := by
              rw [← (ingest.blockRuntimeRefines kind).decode_eq]
              exact decoded
            have exactReencoded :
                (constructiveBlockCodec context.kindSchema kind).encode block =
                  bytes :=
              (constructiveBlockCodec context.kindSchema kind
                ).encode_decode_canonical bytes block exactDecoded
            have runtimeReencoded :
                (ingest.blockRuntimeCodec kind).encode block = bytes := by
              rw [(ingest.blockRuntimeRefines kind).encode_eq]
              exact exactReencoded
            simp [resolveAddressed, stored, rehashed, decoded,
              runtimeReencoded] at noncanonical
      · simp [resolveAddressed, stored, rehashed] at noncanonical

/-! ## Proof-producing local block checks -/

inductive LocalTargetsEvidence
    (schema : GraphKindSchema)
    (sourceKind expectedKind : schema.Kind)
    (nodeCount : Nat) :
    List (GraphRef (RawInRegistryRef schema)) → Type
  | nil :
      LocalTargetsEvidence schema sourceKind expectedKind nodeCount []
  | external :
      LocalTargetsEvidence schema sourceKind expectedKind nodeCount rest →
      LocalTargetsEvidence schema sourceKind expectedKind nodeCount
        (.external ref :: rest)
  | local :
      expectedKind = sourceKind →
      index < nodeCount →
      LocalTargetsEvidence schema sourceKind expectedKind nodeCount rest →
      LocalTargetsEvidence schema sourceKind expectedKind nodeCount
        (.local index :: rest)

inductive DagTargetsEvidence
    (schema : GraphKindSchema) :
    List (GraphRef (RawInRegistryRef schema)) → Type
  | nil : DagTargetsEvidence schema []
  | external :
      DagTargetsEvidence schema rest →
      DagTargetsEvidence schema (.external ref :: rest)

inductive LocalCollectionsEvidence
    (schema : GraphKindSchema)
    (sourceKind : schema.Kind)
    (nodeCount : Nat) :
    List (EdgeCollection schema (RawInRegistryRef schema)) → Type
  | nil :
      LocalCollectionsEvidence schema sourceKind nodeCount []
  | cons :
      LocalTargetsEvidence schema sourceKind
        collection.expectedTargetKind nodeCount collection.targets →
      LocalCollectionsEvidence schema sourceKind nodeCount rest →
      LocalCollectionsEvidence schema sourceKind nodeCount
        (collection :: rest)

inductive DagCollectionsEvidence
    (schema : GraphKindSchema) :
    List (EdgeCollection schema (RawInRegistryRef schema)) → Type
  | nil : DagCollectionsEvidence schema []
  | cons :
      DagTargetsEvidence schema collection.targets →
      DagCollectionsEvidence schema rest →
      DagCollectionsEvidence schema (collection :: rest)

inductive LocalNodesEvidence
    (schema : GraphKindSchema)
    (sourceKind : schema.Kind)
    (nodeCount : Nat) :
    List (RawNode schema) → Type
  | nil : LocalNodesEvidence schema sourceKind nodeCount []
  | cons :
      LocalCollectionsEvidence schema sourceKind nodeCount
        node.edgeCollections →
      LocalNodesEvidence schema sourceKind nodeCount rest →
      LocalNodesEvidence schema sourceKind nodeCount (node :: rest)

inductive CandidateLocalEvidence
    (schema : GraphKindSchema) (kind : schema.Kind) :
    RawBlockCandidate schema kind → Type
  | dag :
      DagCollectionsEvidence schema node.edgeCollections →
      CandidateLocalEvidence schema kind (.dagSingleton node)
  | cyclic :
      LocalNodesEvidence schema kind nodes.length nodes →
      CandidateLocalEvidence schema kind (.cyclic nodes supplied)

inductive RegistryLocalEvidence
    (schema : GraphKindSchema) :
    List (SomeRawBlockEntry schema) → Type
  | nil : RegistryLocalEvidence schema []
  | cons :
      CandidateLocalEvidence schema wrapped.kind wrapped.entry.candidate →
      RegistryLocalEvidence schema rest →
      RegistryLocalEvidence schema (wrapped :: rest)

theorem candidate_local_evidence_of_member
    (evidence : RegistryLocalEvidence schema registry)
    (source : SomeRawBlockEntry schema)
    (sourceMember : source ∈ registry) :
    Nonempty
      (CandidateLocalEvidence
        schema source.kind source.entry.candidate) := by
  induction evidence with
  | nil =>
      simp at sourceMember
  | cons head tail ih =>
      rcases List.mem_cons.mp sourceMember with
        equal | tailMember
      · subst source
        exact ⟨head⟩
      · exact ih tailMember

private def validateLocalTargets
    (schema : GraphKindSchema)
    (sourceKind expectedKind : schema.Kind)
    (nodeCount : Nat) :
    (targets : List (GraphRef (RawInRegistryRef schema))) →
      Except GraphValidationResidue
        (LocalTargetsEvidence
          schema sourceKind expectedKind nodeCount targets)
  | [] => .ok .nil
  | .external _ :: rest =>
      match
          validateLocalTargets
            schema sourceKind expectedKind nodeCount rest with
      | .error residue => .error residue
      | .ok evidence => .ok (.external evidence)
  | .local index :: rest =>
      letI : DecidableEq schema.Kind := schema.decideKindEq
      if kindEqual : expectedKind = sourceKind then
        if indexBound : index < nodeCount then
          match
              validateLocalTargets
                schema sourceKind expectedKind nodeCount rest with
          | .error residue => .error residue
          | .ok evidence =>
              .ok (.local kindEqual indexBound evidence)
        else
          .error .localIndexOutOfBounds
      else
        .error .targetKindMismatch

private def validateDagTargets
    (schema : GraphKindSchema) :
    (targets : List (GraphRef (RawInRegistryRef schema))) →
      Except GraphValidationResidue (DagTargetsEvidence schema targets)
  | [] => .ok .nil
  | .local _ :: _ => .error .localRefInDag
  | .external _ :: rest =>
      match validateDagTargets schema rest with
      | .error residue => .error residue
      | .ok evidence => .ok (.external evidence)

private def validateLocalCollections
    (schema : GraphKindSchema)
    (sourceKind : schema.Kind)
    (nodeCount : Nat) :
    (collections :
      List (EdgeCollection schema (RawInRegistryRef schema))) →
      Except GraphValidationResidue
        (LocalCollectionsEvidence
          schema sourceKind nodeCount collections)
  | [] => .ok .nil
  | collection :: rest =>
      match
          validateLocalTargets schema sourceKind
            collection.expectedTargetKind nodeCount collection.targets with
      | .error residue => .error residue
      | .ok targets =>
          match
              validateLocalCollections
                schema sourceKind nodeCount rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons targets tail)

private def validateDagCollections
    (schema : GraphKindSchema) :
    (collections :
      List (EdgeCollection schema (RawInRegistryRef schema))) →
      Except GraphValidationResidue
        (DagCollectionsEvidence schema collections)
  | [] => .ok .nil
  | collection :: rest =>
      match validateDagTargets schema collection.targets with
      | .error residue => .error residue
      | .ok targets =>
          match validateDagCollections schema rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons targets tail)

private def validateLocalNodes
    (schema : GraphKindSchema)
    (sourceKind : schema.Kind)
    (nodeCount : Nat) :
    (nodes : List (RawNode schema)) →
      Except GraphValidationResidue
        (LocalNodesEvidence schema sourceKind nodeCount nodes)
  | [] => .ok .nil
  | node :: rest =>
      match
          validateLocalCollections
            schema sourceKind nodeCount node.edgeCollections with
      | .error residue => .error residue
      | .ok nodeEvidence =>
          match
              validateLocalNodes schema sourceKind nodeCount rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons nodeEvidence tail)

private def validateLocalEntry
    (schema : GraphKindSchema)
    (kind : schema.Kind)
    (entry : RawBlockEntry schema kind) :
    Except GraphValidationResidue
      (CandidateLocalEvidence schema kind entry.candidate) :=
  match entry.candidate with
  | .dagSingleton node =>
      match validateDagCollections schema node.edgeCollections with
      | .error residue => .error residue
      | .ok evidence => .ok (.dag evidence)
  | .cyclic nodes _supplied =>
      match validateLocalNodes schema kind nodes.length nodes with
      | .error residue => .error residue
      | .ok evidence => .ok (.cyclic evidence)

private def validateLocalRegistry
    (schema : GraphKindSchema) :
    (registry : List (SomeRawBlockEntry schema)) →
      Except GraphValidationResidue
        (RegistryLocalEvidence schema registry)
  | [] => .ok .nil
  | wrapped :: rest =>
      match validateLocalEntry schema wrapped.kind wrapped.entry with
      | .error residue => .error residue
      | .ok head =>
          match validateLocalRegistry schema rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons head tail)

inductive CandidateConnectivityEvidence
    (schema : GraphKindSchema) (kind : schema.Kind) :
    RawBlockCandidate schema kind → Type
  | dag :
      CandidateConnectivityEvidence schema kind (.dagSingleton node)
  | cyclic :
      (supplied : ConnectivityCertificate nodes) →
      (computed : ConnectivityCertificate nodes) →
      CandidateConnectivityEvidence schema kind
        (.cyclic nodes (some supplied))

inductive RegistryConnectivityEvidence
    (schema : GraphKindSchema) :
    List (SomeRawBlockEntry schema) → Type
  | nil : RegistryConnectivityEvidence schema []
  | cons :
      CandidateConnectivityEvidence
        schema wrapped.kind wrapped.entry.candidate →
      RegistryConnectivityEvidence schema rest →
      RegistryConnectivityEvidence schema (wrapped :: rest)

private def validateConnectivityEntry
    (entry : RawBlockEntry schema kind) :
    Except GraphValidationResidue
      (CandidateConnectivityEvidence schema kind entry.candidate) :=
  match entry.candidate with
  | .dagSingleton _ => .ok .dag
  | .cyclic [] _ => .error .emptyCyclicBlock
  | .cyclic nodes supplied =>
      match buildConnectivityCertificate nodes with
      | .error _ => .error .localConnectivityRefused
      | .ok computed =>
          match supplied with
          | none => .error .connectivityCertificateMissing
          | some suppliedCert =>
              .ok (.cyclic suppliedCert computed)

private def validateConnectivityRegistry
    (schema : GraphKindSchema) :
    (registry : List (SomeRawBlockEntry schema)) →
      Except GraphValidationResidue
        (RegistryConnectivityEvidence schema registry)
  | [] => .ok .nil
  | wrapped :: rest =>
      match validateConnectivityEntry wrapped.entry with
      | .error residue => .error residue
      | .ok head =>
          match validateConnectivityRegistry schema rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons head tail)

def AllLocalReferencesBoundAndTyped
    (graph : RawRootedGraph schema) : Prop :=
  Nonempty (RegistryLocalEvidence schema graph.blockRegistry)

def AllCyclicBlocksComputedConnected
    (graph : RawRootedGraph schema) : Prop :=
  Nonempty (RegistryConnectivityEvidence schema graph.blockRegistry)

/-! ## Typed key and occurrence validation -/

inductive HeadKeyDistinct
    (schema : GraphKindSchema)
    (head : SomeRawBlockEntry schema) :
    List (SomeRawBlockEntry schema) → Type
  | nil : HeadKeyDistinct schema head []
  | cons :
      registryEntryKeyIdentity schema head ≠
        registryEntryKeyIdentity schema next →
      HeadKeyDistinct schema head rest →
      HeadKeyDistinct schema head (next :: rest)

inductive RegistryKeysUniqueEvidence
    (schema : GraphKindSchema) :
    List (SomeRawBlockEntry schema) → Type
  | nil : RegistryKeysUniqueEvidence schema []
  | cons :
      HeadKeyDistinct schema head rest →
      RegistryKeysUniqueEvidence schema rest →
      RegistryKeysUniqueEvidence schema (head :: rest)

private theorem head_key_distinct_not_mem
    (evidence : HeadKeyDistinct schema head rest) :
    registryEntryKeyIdentity schema head ∉
      rest.map (registryEntryKeyIdentity schema) := by
  induction evidence with
  | nil =>
      simp
  | @cons next tail different tailEvidence ih =>
      intro member
      simp only [List.map, List.mem_cons] at member
      rcases member with equal | tailMember
      · exact different equal
      · exact ih tailMember

theorem registry_keys_unique_no_duplicates
    (evidence : RegistryKeysUniqueEvidence schema registry) :
    (registry.map
      (registryEntryKeyIdentity schema)).Nodup := by
  induction evidence with
  | nil =>
      simp
  | @cons head rest headDistinct tailUnique ih =>
      apply List.nodup_cons.mpr
      exact
        ⟨head_key_distinct_not_mem headDistinct, ih⟩

private theorem eq_of_mem_of_mem_of_map_nodup
    {α β : Type}
    (encode : α → β)
    (values : List α)
    {left right : α}
    (noDuplicates : (values.map encode).Nodup)
    (leftMember : left ∈ values)
    (rightMember : right ∈ values)
    (encodedExact : encode left = encode right) :
    left = right := by
  induction values generalizing left right with
  | nil =>
      simp at leftMember
  | cons head tail ih =>
      have distinct :=
        List.nodup_cons.mp noDuplicates
      rcases List.mem_cons.mp leftMember with
        leftHead | leftTail
      · subst left
        rcases List.mem_cons.mp rightMember with
          rightHead | rightTail
        · exact rightHead.symm
        · exfalso
          apply distinct.1
          apply List.mem_map.mpr
          exact ⟨right, rightTail, encodedExact.symm⟩
      · rcases List.mem_cons.mp rightMember with
          rightHead | rightTail
        · subst right
          exfalso
          apply distinct.1
          apply List.mem_map.mpr
          exact ⟨left, leftTail, encodedExact⟩
        · exact ih distinct.2 leftTail rightTail encodedExact

theorem typed_registry_member_wrapped_eq
    (unique : RegistryKeysUniqueEvidence schema registry)
    (left : TypedRegistryMember registry key leftEntry)
    (right : TypedRegistryMember registry key rightEntry) :
    left.wrapped = right.wrapped := by
  apply eq_of_mem_of_mem_of_map_nodup
    (registryEntryKeyIdentity schema)
    registry
    (registry_keys_unique_no_duplicates unique)
    left.wrappedMember right.wrappedMember
  exact
    (typed_registry_member_key_identity left).trans
      (typed_registry_member_key_identity right).symm

private theorem some_raw_block_entry_entry_heq_of_eq
    (left right : SomeRawBlockEntry schema)
    (exact : left = right) :
    HEq left.entry right.entry := by
  subst right
  rfl

theorem typed_registry_member_entry_eq
    (unique : RegistryKeysUniqueEvidence schema registry)
    (left : TypedRegistryMember registry key leftEntry)
    (right : TypedRegistryMember registry key rightEntry) :
    leftEntry = rightEntry := by
  have wrappedExact :=
    typed_registry_member_wrapped_eq unique left right
  have wrappedEntryExact :=
    some_raw_block_entry_entry_heq_of_eq
      left.wrapped right.wrapped wrappedExact
  exact
    eq_of_heq
      (left.entryEq.symm.trans (wrappedEntryExact.trans right.entryEq))

theorem registry_member_eq_of_key_identity
    (unique : RegistryKeysUniqueEvidence schema registry)
    (left right : SomeRawBlockEntry schema)
    (leftMember : left ∈ registry)
    (rightMember : right ∈ registry)
    (keyExact :
      registryEntryKeyIdentity schema left =
        registryEntryKeyIdentity schema right) :
    left = right := by
  exact
    eq_of_mem_of_mem_of_map_nodup
      (registryEntryKeyIdentity schema)
      registry
      (registry_keys_unique_no_duplicates unique)
      leftMember rightMember keyExact

theorem registry_member_eq_normalized_typed
    {schema : GraphKindSchema}
    {kind : schema.Kind}
    {registry : List (SomeRawBlockEntry schema)}
    {key : RawRegistryKey schema kind}
    {entry : RawBlockEntry schema kind}
    (unique : RegistryKeysUniqueEvidence schema registry)
    (left : SomeRawBlockEntry schema)
    (leftMember : left ∈ registry)
    (right : TypedRegistryMember registry key entry)
    (keyExact :
      registryEntryKeyIdentity schema left =
        rawKeyIdentity schema kind key) :
    left = normalizedTypedRegistryEntry entry := by
  have wrappedExact :
      left = right.wrapped := by
    apply registry_member_eq_of_key_identity
      unique left right.wrapped leftMember
      right.wrappedMember
    exact keyExact.trans
      (typed_registry_member_key_identity right).symm
  exact wrappedExact.trans
    (typed_registry_member_wrapped_eq_normalized right)

private def validateHeadKeyDistinct
    (schema : GraphKindSchema)
    (head : SomeRawBlockEntry schema) :
    (rest : List (SomeRawBlockEntry schema)) →
      Except GraphValidationResidue
        (HeadKeyDistinct schema head rest)
  | [] => .ok .nil
  | next :: tail =>
      if equal :
          registryEntryKeyIdentity schema head =
            registryEntryKeyIdentity schema next then
        .error .duplicateBlockKey
      else
        match validateHeadKeyDistinct schema head tail with
        | .error residue => .error residue
        | .ok evidence => .ok (.cons equal evidence)

private def validateRegistryKeysUnique
    (schema : GraphKindSchema) :
    (registry : List (SomeRawBlockEntry schema)) →
      Except GraphValidationResidue
        (RegistryKeysUniqueEvidence schema registry)
  | [] => .ok .nil
  | head :: rest =>
      match validateHeadKeyDistinct schema head rest with
      | .error residue => .error residue
      | .ok headDistinct =>
          match validateRegistryKeysUnique schema rest with
          | .error residue => .error residue
          | .ok restUnique => .ok (.cons headDistinct restUnique)

private def resolveRawTarget
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema)
    (ref : RawInRegistryRef context.kindSchema) :
    Except GraphValidationResidue
      (ResolvedTargetEvidence context ingest graph ref) :=
  let resolution :=
      resolveAddressed
        (context.blockBinding ref.kind)
        (ingest.blockRuntimeCodec ref.kind)
        (ingest.blockStore ref.kind)
        ref.targetKey.claimedBlockQ.toAddress
  match adapterEquation : mapExternalResolution resolution with
  | .error residue => .error residue
  | .ok canonicalBlock =>
      have resolvedEquation :
          resolveAddressed
              (context.blockBinding ref.kind)
              (ingest.blockRuntimeCodec ref.kind)
              (ingest.blockStore ref.kind)
              ref.targetKey.claimedBlockQ.toAddress =
            .resolved canonicalBlock := by
        exact
          (map_external_resolution_ok_iff
            resolution canonicalBlock).1 adapterEquation
      match memberEquation :
          findTypedRegistryMember graph.blockRegistry ref.targetKey with
      | none => .error .externalTargetNotInRegistry
      | some found =>
          let target : RawTargetMember graph ref :=
            { targetEntry := found.1
              targetEntryMember := found.2
              targetNodeCountLookup := by
                simp [rawTargetCandidateNodeCount, memberEquation] }
          if rawBound :
              ref.rawTargetMemberIndex <
                target.targetEntry.candidate.nodeCount then
            if resolvedBound :
                ref.rawTargetMemberIndex < canonicalBlock.nodes.length then
              .ok
                { target := target
                  rawBound := rawBound
                  resolved :=
                    { canonicalBlock := canonicalBlock
                      resolvedByAK5 := resolvedEquation
                      resolvedCanonicalIndexBound := resolvedBound } }
            else
              .error .resolvedCanonicalMemberIndexOutOfBounds
          else
            .error .rawTargetMemberIndexOutOfBounds

structure ValidatedOccurrence
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema)
    (occurrence : RawExternalOccurrence context.kindSchema) : Type where
  target :
    ResolvedTargetEvidence context ingest graph occurrence.ref
  resolveEquation :
    resolveRawTarget context ingest graph occurrence.ref = .ok target
  rankStrict :
    target.target.targetEntry.dependencyRank < occurrence.ownerRank

private def validateOccurrence
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema)
    (occurrence : RawExternalOccurrence context.kindSchema) :
    Except GraphValidationResidue
      (ValidatedOccurrence context ingest graph occurrence) :=
  letI : DecidableEq context.kindSchema.Kind :=
    context.kindSchema.decideKindEq
  if _kindEqual :
      occurrence.expectedTargetKind = occurrence.ref.kind then
    match targetEquation :
        resolveRawTarget context ingest graph occurrence.ref with
    | .error residue => .error residue
    | .ok target =>
        if rankStrict :
            target.target.targetEntry.dependencyRank < occurrence.ownerRank then
          .ok
            { target := target
              resolveEquation := targetEquation
              rankStrict := rankStrict }
        else
          .error .crossBlockRankNotStrict
  else
    .error .targetKindMismatch

inductive ValidatedOccurrences
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema) :
    List (RawExternalOccurrence context.kindSchema) → Type
  | nil : ValidatedOccurrences context ingest graph []
  | cons :
      ValidatedOccurrence context ingest graph occurrence →
      ValidatedOccurrences context ingest graph rest →
      ValidatedOccurrences context ingest graph (occurrence :: rest)

private def validateOccurrences
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context)
    (graph : RawRootedGraph context.kindSchema) :
    (occurrences : List (RawExternalOccurrence context.kindSchema)) →
      Except GraphValidationResidue
        (ValidatedOccurrences context ingest graph occurrences)
  | [] => .ok .nil
  | occurrence :: rest =>
      match validateOccurrence context ingest graph occurrence with
      | .error residue => .error residue
      | .ok head =>
          match validateOccurrences context ingest graph rest with
          | .error residue => .error residue
          | .ok tail => .ok (.cons head tail)

def AllCrossBlockRanksStrict
    (graph : RawRootedGraph schema) : Prop :=
  ∀ occurrence,
    occurrence ∈ rawExternalOccurrences graph →
      ∃ target : RawTargetMember graph occurrence.ref,
        target.targetEntry.dependencyRank < occurrence.ownerRank

private theorem validatedOccurrencesStrictAux
    (validated :
      ValidatedOccurrences context ingest graph
        occurrences) :
    ∀ occurrence,
      occurrence ∈ occurrences →
        ∃ target : RawTargetMember graph occurrence.ref,
          target.targetEntry.dependencyRank < occurrence.ownerRank := by
  induction validated with
  | nil =>
      intro occurrence member
      simp at member
  | @cons head rest headValidated tailValidated inductionHypothesis =>
      intro occurrence member
      simp only [List.mem_cons] at member
      cases member with
      | inl equal =>
          cases equal
          exact
            ⟨headValidated.target.target, headValidated.rankStrict⟩
      | inr tailMember =>
          exact inductionHypothesis occurrence tailMember

private theorem validatedOccurrencesStrict
    (validated :
      ValidatedOccurrences context ingest graph
        (rawExternalOccurrences graph)) :
    AllCrossBlockRanksStrict graph :=
  validatedOccurrencesStrictAux validated

private theorem validatedOccurrencesNotErrorAux
    (validated :
      ValidatedOccurrences context ingest graph
        occurrences) :
    ∀ ref,
      ref ∈ occurrences.map RawExternalOccurrence.ref →
      ∀ residue,
        resolveRawTarget context ingest graph ref ≠ .error residue := by
  induction validated with
  | nil =>
      intro ref occurs
      simp at occurs
  | @cons head rest headValidated tailValidated inductionHypothesis =>
      intro ref occurs residue refused
      simp only [List.map, List.mem_cons] at occurs
      cases occurs with
      | inl equal =>
          cases equal
          rw [headValidated.resolveEquation] at refused
          contradiction
      | inr tailOccurs =>
          exact inductionHypothesis ref tailOccurs residue refused

private theorem validatedOccurrencesNotError
    (validated :
      ValidatedOccurrences context ingest graph
        (rawExternalOccurrences graph)) :
    ∀ ref, RawReferenceOccurs graph ref →
      ∀ residue,
        resolveRawTarget context ingest graph ref ≠ .error residue :=
  validatedOccurrencesNotErrorAux validated

private def exceptGetOk
    (result : Except ε α)
    (notError : ∀ residue, result ≠ .error residue) : α :=
  match result with
  | .ok value => value
  | .error residue => False.elim (notError residue rfl)

private theorem except_get_ok_eq_of_ok
    (result : Except ε α)
    (notError : ∀ residue, result ≠ .error residue)
    (target : α)
    (resolved : result = .ok target) :
    exceptGetOk result notError = target := by
  cases result with
  | ok value =>
      simp at resolved
      subst target
      rfl
  | error residue =>
      simp at resolved

private theorem except_get_ok_proof_irrelevant
    (result : Except ε α)
    (left right : ∀ residue, result ≠ .error residue) :
    exceptGetOk result left = exceptGetOk result right := by
  have proofsExact : left = right := Subsingleton.elim left right
  subst right
  rfl

private def validatedOccurrencesResolveAux
    (validated :
      ValidatedOccurrences context ingest graph
        occurrences) :
    ∀ ref, ref ∈ occurrences.map RawExternalOccurrence.ref →
      ResolvedTargetEvidence context ingest graph ref :=
  fun ref occurs =>
    exceptGetOk
      (resolveRawTarget context ingest graph ref)
      (validatedOccurrencesNotErrorAux validated ref occurs)

private def validatedOccurrencesResolve
    (validated :
      ValidatedOccurrences context ingest graph
        (rawExternalOccurrences graph)) :
    ∀ ref, RawReferenceOccurs graph ref →
      ResolvedTargetEvidence context ingest graph ref :=
  validatedOccurrencesResolveAux validated

private theorem validated_occurrences_resolve_aux_eq_of_ok
    (validated :
      ValidatedOccurrences context ingest graph occurrences)
    (ref : RawInRegistryRef context.kindSchema)
    (occurs : ref ∈ occurrences.map RawExternalOccurrence.ref)
    (target : ResolvedTargetEvidence context ingest graph ref)
    (resolved :
      resolveRawTarget context ingest graph ref = .ok target) :
    validatedOccurrencesResolveAux validated ref occurs = target := by
  exact except_get_ok_eq_of_ok
    (resolveRawTarget context ingest graph ref)
    (validatedOccurrencesNotErrorAux validated ref occurs)
    target resolved

private theorem validated_occurrences_resolved_strict_aux
    (validated :
      ValidatedOccurrences context ingest graph occurrences) :
    ∀ occurrence
      (member : occurrence ∈ occurrences),
      let occurs :=
        List.mem_map.mpr ⟨occurrence, member, rfl⟩
      (validatedOccurrencesResolveAux validated
          occurrence.ref occurs).target.targetEntry.dependencyRank <
        occurrence.ownerRank := by
  induction validated with
  | nil =>
      intro occurrence member
      simp at member
  | @cons head rest headValidated tailValidated ih =>
      intro occurrence member
      rcases List.mem_cons.mp member with equal | tailMember
      · subst occurrence
        simpa [validatedOccurrencesResolveAux,
          headValidated.resolveEquation] using
            headValidated.rankStrict
      · have valueExact :
            validatedOccurrencesResolveAux
                (.cons headValidated tailValidated)
                occurrence.ref
                (List.mem_map.mpr
                  ⟨occurrence, member, rfl⟩) =
              validatedOccurrencesResolveAux
                tailValidated occurrence.ref
                (List.mem_map.mpr
                  ⟨occurrence, tailMember, rfl⟩) := by
          unfold validatedOccurrencesResolveAux
          apply except_get_ok_proof_irrelevant
        dsimp only
        rw [valueExact]
        exact ih occurrence tailMember

private theorem validated_occurrences_resolved_strict
    (validated :
      ValidatedOccurrences context ingest graph
        (rawExternalOccurrences graph)) :
    ∀ occurrence
      (member : occurrence ∈ rawExternalOccurrences graph),
      let occurs :
          RawReferenceOccurs graph occurrence.ref :=
        raw_reference_occurs_of_occurrence_member
          graph occurrence member
      (validatedOccurrencesResolve validated
          occurrence.ref occurs).target.targetEntry.dependencyRank <
        occurrence.ownerRank :=
  validated_occurrences_resolved_strict_aux validated

/-! ## Proof-producing root reachability -/

private def rootKeyIdentity
    (graph : RawRootedGraph schema) : RawKeyIdentity :=
  rawKeyIdentity schema graph.root.kind graph.root.targetKey

private def occurrenceOwnerIdentity
    (occurrence : RawExternalOccurrence schema) : RawKeyIdentity :=
  rawKeyIdentity schema occurrence.ownerKind occurrence.ownerKey

private def occurrenceTargetIdentity
    (occurrence : RawExternalOccurrence schema) : RawKeyIdentity :=
  rawKeyIdentity schema occurrence.ref.kind occurrence.ref.targetKey

private def registryKeyIdentities
    (registry : List (SomeRawBlockEntry schema)) :
    List RawKeyIdentity :=
  registry.map fun wrapped =>
    rawKeyIdentity schema wrapped.kind
      ⟨wrapped.entry.claimedBlockQ⟩

inductive RegistryPathEvidence
    (graph : RawRootedGraph schema) : RawKeyIdentity → Type
  | root :
      RegistryPathEvidence graph (rootKeyIdentity graph)
  | step
      (occurrence : RawExternalOccurrence schema) :
      occurrence ∈ rawExternalOccurrences graph →
      RegistryPathEvidence graph
        (occurrenceOwnerIdentity occurrence) →
      RegistryPathEvidence graph
        (occurrenceTargetIdentity occurrence)

inductive ReachableKeyListEvidence
    (graph : RawRootedGraph schema) :
    List RawKeyIdentity → Type
  | nil : ReachableKeyListEvidence graph []
  | cons :
      RegistryPathEvidence graph key →
      ReachableKeyListEvidence graph rest →
      ReachableKeyListEvidence graph (key :: rest)

private def findReachabilityEvidence
    (key : RawKeyIdentity) :
    {keys : List RawKeyIdentity} →
      ReachableKeyListEvidence graph keys →
      Option (RegistryPathEvidence graph key)
  | [], .nil => none
  | head :: _tail, .cons headEvidence tailEvidence =>
      if equal : head = key then
        some (equal ▸ headEvidence)
      else
        findReachabilityEvidence key tailEvidence

structure ReachableKeySet
    (graph : RawRootedGraph schema) where
  keys : List RawKeyIdentity
  evidence : ReachableKeyListEvidence graph keys

private def insertReachableKey
    (key : RawKeyIdentity)
    (keyEvidence : RegistryPathEvidence graph key)
    (reachable : ReachableKeySet graph) :
    ReachableKeySet graph :=
  match findReachabilityEvidence key reachable.evidence with
  | some _ => reachable
  | none =>
      { keys := key :: reachable.keys
        evidence := .cons keyEvidence reachable.evidence }

private def expandReachableOnce
    (graph : RawRootedGraph schema) :
    (occurrences : List (RawExternalOccurrence schema)) →
    (contained :
      ∀ occurrence, occurrence ∈ occurrences →
        occurrence ∈ rawExternalOccurrences graph) →
    ReachableKeySet graph → ReachableKeySet graph
  | [], _, reachable => reachable
  | occurrence :: rest, contained, reachable =>
      let next :=
        match
            findReachabilityEvidence
              (occurrenceOwnerIdentity occurrence) reachable.evidence with
        | none => reachable
        | some ownerEvidence =>
            insertReachableKey
              (occurrenceTargetIdentity occurrence)
              (.step occurrence (contained occurrence (by simp)) ownerEvidence)
              reachable
      expandReachableOnce graph rest
        (fun candidate member =>
          contained candidate (List.mem_cons_of_mem occurrence member))
        next

private def expandReachable
    (graph : RawRootedGraph schema) :
    Nat → ReachableKeySet graph → ReachableKeySet graph
  | 0, reachable => reachable
  | fuel + 1, reachable =>
      expandReachable graph fuel
        (expandReachableOnce graph (rawExternalOccurrences graph)
          (fun _ member => member) reachable)

private def collectReachabilityEvidence
    (graph : RawRootedGraph schema)
    (reachable : ReachableKeySet graph) :
    (keys : List RawKeyIdentity) →
      Option (ReachableKeyListEvidence graph keys)
  | [] => some .nil
  | key :: rest =>
      match findReachabilityEvidence key reachable.evidence with
      | none => none
      | some head =>
          match collectReachabilityEvidence graph reachable rest with
          | none => none
          | some tail => some (.cons head tail)

def RegistryReachabilityEvidence
    (graph : RawRootedGraph schema) : Type :=
  ReachableKeyListEvidence graph
    (registryKeyIdentities graph.blockRegistry)

private def validateRegistryReachability
    (graph : RawRootedGraph schema) :
    Except GraphValidationResidue
      (RegistryReachabilityEvidence graph) :=
  let initial : ReachableKeySet graph :=
    { keys := [rootKeyIdentity graph]
      evidence := .cons .root .nil }
  let reachable :=
    expandReachable graph graph.blockRegistry.length initial
  match
      collectReachabilityEvidence graph reachable
        (registryKeyIdentities graph.blockRegistry) with
  | none => .error .unreachableRegistryBlock
  | some evidence => .ok evidence

def EveryRegistryBlockReachable
    (graph : RawRootedGraph schema) : Prop :=
  Nonempty (RegistryReachabilityEvidence graph)

/-! ## Closed carrier and top-level validator -/

structure StructurallyClosedRootedGraph
    (context : GraphCodecContext)
    (ingest : RawIngestProfile context) where
  rawGraph : RawRootedGraph context.kindSchema
  rootMember : RawTargetMember rawGraph rawGraph.root
  rootRawBound : RawTargetMemberBound rootMember
  rootResolved : ResolvedRawTarget context ingest rawGraph.root
  resolvedTarget :
    ∀ ref, RawReferenceOccurs rawGraph ref →
      ResolvedTargetEvidence context ingest rawGraph ref
  uniqueKeys :
    RegistryKeysUniqueEvidence
      context.kindSchema rawGraph.blockRegistry
  localWitness :
    RegistryLocalEvidence context.kindSchema rawGraph.blockRegistry
  connectivityWitness :
    RegistryConnectivityEvidence
      context.kindSchema rawGraph.blockRegistry
  reachabilityWitness : RegistryReachabilityEvidence rawGraph
  localBoundsAndKinds : AllLocalReferencesBoundAndTyped rawGraph
  computedConnectivity : AllCyclicBlocksComputedConnected rawGraph
  strictRank : AllCrossBlockRanksStrict rawGraph
  resolvedStrictRank :
    ∀ occurrence
      (member : occurrence ∈ rawExternalOccurrences rawGraph),
      let occurs :
          RawReferenceOccurs rawGraph occurrence.ref :=
        raw_reference_occurs_of_occurrence_member
          rawGraph occurrence member
      (resolvedTarget occurrence.ref
          occurs).target.targetEntry.dependencyRank <
        occurrence.ownerRank
  reachable : EveryRegistryBlockReachable rawGraph

def validateRawRootedGraph
    (context : GraphCodecContext)
    (_injective : GraphDigestInjective context)
    (ingest : RawIngestProfile context)
    (raw : RawRootedGraph context.kindSchema) :
    Except GraphValidationResidue
      (StructurallyClosedRootedGraph context ingest) :=
  match raw.blockRegistry with
  | [] => .error .emptyRegistry
  | _ :: _ =>
      match _uniqueEvidence :
          validateRegistryKeysUnique
            context.kindSchema raw.blockRegistry with
      | .error residue => .error residue
      | .ok uniqueEvidence =>
        match _rootLookup :
            findTypedRegistryMember
              raw.blockRegistry raw.root.targetKey with
        | none => .error .rootNotInRegistry
        | some _ =>
            match _connectivityEquation :
                validateConnectivityRegistry
                  context.kindSchema raw.blockRegistry with
            | .error residue => .error residue
            | .ok connectivityEvidence =>
                match _localEquation :
                    validateLocalRegistry
                      context.kindSchema raw.blockRegistry with
                | .error residue => .error residue
                | .ok localEvidence =>
                    match _rootEvidence :
                        resolveRawTarget context ingest raw raw.root with
                    | .error residue => .error residue
                    | .ok root =>
                        match _occurrenceEvidence :
                            validateOccurrences context ingest raw
                              (rawExternalOccurrences raw) with
                        | .error residue => .error residue
                        | .ok occurrences =>
                            match _reachabilityEquation :
                                validateRegistryReachability raw with
                            | .error residue => .error residue
                            | .ok reachabilityEvidence =>
                              .ok
                                { rawGraph := raw
                                  rootMember := root.target
                                  rootRawBound := root.rawBound
                                  rootResolved := root.resolved
                                  resolvedTarget :=
                                    validatedOccurrencesResolve occurrences
                                  uniqueKeys := uniqueEvidence
                                  localWitness := localEvidence
                                  connectivityWitness :=
                                    connectivityEvidence
                                  reachabilityWitness :=
                                    reachabilityEvidence
                                  localBoundsAndKinds :=
                                    ⟨localEvidence⟩
                                  computedConnectivity :=
                                    ⟨connectivityEvidence⟩
                                  strictRank :=
                                    validatedOccurrencesStrict occurrences
                                  resolvedStrictRank :=
                                    validated_occurrences_resolved_strict
                                      occurrences
                                  reachable :=
                                    ⟨reachabilityEvidence⟩ }

end Residua.RCC.Addressing.AddressedGraph.Closure


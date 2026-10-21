import RCC.AddressedGraphCanonical

/-!
# RCC addressed-graph closed carrier

This module promotes a finalized canonical registry into the pure, resolved
carrier consumed by the store-free graph codec.  The first layer below fixes
the canonical pointer and registry-key laws before any reference resolution or
dependency construction is introduced.
-/

namespace Residua.RCC.Addressing.AddressedGraph

open Residua.RCC.Addressing

def listGet? : List α → Nat → Option α
  | [], _ =>
      none
  | head :: _, 0 =>
      some head
  | _ :: tail, index + 1 =>
      listGet? tail index

structure CanonicalNodePointer
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) where
  blockIndex : Nat
  blockBound : blockIndex < registry.length
  localIndex : Nat
  localBound :
    localIndex <
      (registry.get ⟨blockIndex, blockBound⟩).block.nodes.length

def CanonicalRegistryStrictOrder
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Prop :=
  registry.Pairwise
    (fun left right =>
      compareGraphBytes
        (encodeCanonicalRegistryKey context left.key)
        (encodeCanonicalRegistryKey context right.key) = .lt)

def canonicalRegistryKeyRawIdentity
    (context : GraphCodecContext)
    (key : CanonicalRegistryKey context.kindSchema) :
    Closure.RawKeyIdentity :=
  { kindCode := context.kindSchema.kindCode key.kind
    algorithm := key.blockQ.algorithm
    domainQ := key.blockQ.domainQ
    schemaQ := key.blockQ.schemaQ
    digest := key.blockQ.digest }

theorem encode_canonical_registry_key_eq_raw_identity
    (context : GraphCodecContext)
    (key : CanonicalRegistryKey context.kindSchema) :
    encodeCanonicalRegistryKey context key =
      encodeRawKeyIdentity
        (canonicalRegistryKeyRawIdentity context key) :=
  rfl

theorem canonical_registry_key_raw_identity_injective
    {context : GraphCodecContext}
    {left right : CanonicalRegistryKey context.kindSchema}
    (identityExact :
      canonicalRegistryKeyRawIdentity context left =
        canonicalRegistryKeyRawIdentity context right) :
    left = right := by
  rcases left with ⟨leftKind, leftAddress⟩
  rcases right with ⟨rightKind, rightAddress⟩
  have kindCodeExact :
      context.kindSchema.kindCode leftKind =
        context.kindSchema.kindCode rightKind :=
    congrArg Closure.RawKeyIdentity.kindCode identityExact
  have kindExact : leftKind = rightKind :=
    context.kindSchema.kindCodeInjective kindCodeExact
  subst rightKind
  rcases leftAddress with
    ⟨leftAlgorithm, leftDomain, leftSchema, leftDigest⟩
  rcases rightAddress with
    ⟨rightAlgorithm, rightDomain, rightSchema, rightDigest⟩
  simp only [canonicalRegistryKeyRawIdentity] at identityExact
  cases identityExact
  rfl

theorem encode_canonical_registry_key_injective
    {context : GraphCodecContext}
    {left right : CanonicalRegistryKey context.kindSchema}
    (encodedExact :
      encodeCanonicalRegistryKey context left =
        encodeCanonicalRegistryKey context right) :
    left = right := by
  rw [
    encode_canonical_registry_key_eq_raw_identity,
    encode_canonical_registry_key_eq_raw_identity
  ] at encodedExact
  exact
    canonical_registry_key_raw_identity_injective
      (encode_raw_key_identity_injective encodedExact)

theorem canonical_registry_strict_order_implies_keys_no_dup
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    (strict : CanonicalRegistryStrictOrder context registry) :
    CanonicalRegistryKeysNoDup context registry := by
  unfold CanonicalRegistryKeysNoDup NoDuplicates
  rw [List.pairwise_map]
  exact strict.imp (by
    intro left right ordered encodedExact
    rw [encodedExact, compare_graph_bytes_self] at ordered
    contradiction)

def EveryCyclicBlockHasComputedConnectivity
    (registry : List (SomeCanonicalBlock context)) : Prop :=
  ∀ entry, entry ∈ registry →
    ∀ nodes, entry.block = .cyclic nodes →
      ∃ certificate,
        Closure.buildConnectivityCertificate nodes = .ok certificate

structure PublicReferenceOccurrence
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context)) where
  sourceBlockIndex : Nat
  sourceBlockBound : sourceBlockIndex < registry.length
  sourceBlock : SomeCanonicalBlock context
  sourceBlockLookup :
    listGet? registry sourceBlockIndex = some sourceBlock
  sourceNodeIndex : Nat
  sourceNodeBound : sourceNodeIndex < sourceBlock.block.nodes.length
  sourceNode : CanonicalNode context.kindSchema
  sourceNodeLookup :
    listGet? sourceBlock.block.nodes sourceNodeIndex = some sourceNode
  owningCollectionIndex : Nat
  owningCollection :
    EdgeCollection context.kindSchema
      (ExternalRef context.kindSchema)
  owningCollectionLookup :
    listGet? sourceNode.edgeCollections owningCollectionIndex =
      some owningCollection
  expectedTargetKind : context.kindSchema.Kind
  expectedTargetKindExact :
    owningCollection.expectedTargetKind = expectedTargetKind
  ref : ExternalRef context.kindSchema
  targetPosition : Nat
  targetOccurrence :
    listGet? owningCollection.targets targetPosition =
      some
        (Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
          ref)

inductive PublicReferenceResolutionResidue
  | targetKindMismatch
  | targetMissing
  | canonicalMemberIndexOutOfBounds
  deriving DecidableEq, Repr

structure CanonicalRegistryLookup
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context))
    (targetKey : CanonicalRegistryKey context.kindSchema) where
  targetBlockIndex : Nat
  targetBlockBound : targetBlockIndex < registry.length
  targetBlock : SomeCanonicalBlock context
  targetLookup :
    listGet? registry targetBlockIndex = some targetBlock
  targetKeyExact : targetBlock.key = targetKey

def findCanonicalRegistryLookup
    (context : GraphCodecContext)
    (targetKey : CanonicalRegistryKey context.kindSchema) :
    (registry : List (SomeCanonicalBlock context)) →
      Option (CanonicalRegistryLookup context registry targetKey)
  | [] =>
      none
  | head :: tail =>
      if keyExact :
          encodeCanonicalRegistryKey context head.key =
            encodeCanonicalRegistryKey context targetKey then
        some
          { targetBlockIndex := 0
            targetBlockBound := by simp
            targetBlock := head
            targetLookup := rfl
            targetKeyExact :=
              encode_canonical_registry_key_injective keyExact }
      else
        match findCanonicalRegistryLookup context targetKey tail with
        | none =>
            none
        | some found =>
            some
              { targetBlockIndex := found.targetBlockIndex.succ
                targetBlockBound :=
                  Nat.succ_lt_succ found.targetBlockBound
                targetBlock := found.targetBlock
                targetLookup := by
                  simpa using found.targetLookup
                targetKeyExact := found.targetKeyExact }

private theorem canonical_registry_key_kind_eq
    {context : GraphCodecContext}
    {left right : CanonicalRegistryKey context.kindSchema}
    (exact : left = right) :
    left.kind = right.kind := by
  cases exact
  rfl

private theorem canonical_registry_key_address_heq
    {context : GraphCodecContext}
    {left right : CanonicalRegistryKey context.kindSchema}
    (exact : left = right) :
    HEq left.blockQ right.blockQ := by
  cases exact
  rfl

structure ResolvedPublicReference
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    (occurrence : PublicReferenceOccurrence registry) where
  targetBlockIndex : Nat
  targetBlockBound : targetBlockIndex < registry.length
  targetBlock : SomeCanonicalBlock context
  targetLookup :
    listGet? registry targetBlockIndex = some targetBlock
  registryKeysUnique :
    CanonicalRegistryKeysNoDup context registry
  expectedTargetKind :
    occurrence.expectedTargetKind = occurrence.ref.kind
  targetKind : targetBlock.kind = occurrence.ref.kind
  targetAddress :
    HEq targetBlock.blockQ occurrence.ref.target.blockQ
  targetNodeIndex : Fin targetBlock.block.nodes.length
  targetNodeIndexExact :
    targetNodeIndex.val =
      occurrence.ref.target.canonicalLocalIndex

def resolvePublicReferenceOccurrence
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry)
    (occurrence : PublicReferenceOccurrence registry) :
    Except PublicReferenceResolutionResidue
      (ResolvedPublicReference occurrence) :=
  if expectedKindExact :
      occurrence.expectedTargetKind = occurrence.ref.kind then
    let targetKey : CanonicalRegistryKey context.kindSchema :=
      { kind := occurrence.ref.kind
        blockQ := occurrence.ref.target.blockQ }
    match
        findCanonicalRegistryLookup context targetKey registry with
    | none =>
        .error .targetMissing
    | some found =>
        if targetBound :
            occurrence.ref.target.canonicalLocalIndex <
              found.targetBlock.block.nodes.length then
          .ok
            { targetBlockIndex := found.targetBlockIndex
              targetBlockBound := found.targetBlockBound
              targetBlock := found.targetBlock
              targetLookup := found.targetLookup
              registryKeysUnique := keysUnique
              expectedTargetKind := expectedKindExact
              targetKind :=
                canonical_registry_key_kind_eq
                  found.targetKeyExact
              targetAddress :=
                canonical_registry_key_address_heq
                  found.targetKeyExact
              targetNodeIndex :=
                ⟨occurrence.ref.target.canonicalLocalIndex,
                  targetBound⟩
              targetNodeIndexExact := rfl }
        else
          .error .canonicalMemberIndexOutOfBounds
  else
    .error .targetKindMismatch

structure ResolvedEdge
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) where
  occurrence : PublicReferenceOccurrence registry
  resolved : ResolvedPublicReference occurrence
  resolutionExact :
    resolvePublicReferenceOccurrence keysUnique occurrence =
      .ok resolved

structure PublicOccurrenceIdentity where
  sourceBlockIndex : Nat
  sourceNodeIndex : Nat
  owningCollectionIndex : Nat
  targetPosition : Nat
  deriving DecidableEq, Repr

def PublicReferenceOccurrence.identity
    (occurrence : PublicReferenceOccurrence registry) :
    PublicOccurrenceIdentity :=
  { sourceBlockIndex := occurrence.sourceBlockIndex
    sourceNodeIndex := occurrence.sourceNodeIndex
    owningCollectionIndex := occurrence.owningCollectionIndex
    targetPosition := occurrence.targetPosition }

theorem list_get?_eq_get
    (values : List α)
    (index : Fin values.length) :
    listGet? values index.val = some (values.get index) := by
  induction values with
  | nil =>
      exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | cons head tail ih =>
      cases index with
      | mk value bound =>
          cases value with
          | zero =>
              rfl
          | succ value =>
              have tailBound : value < tail.length :=
                Nat.succ_lt_succ_iff.mp bound
              simpa [listGet?] using
                ih ⟨value, tailBound⟩

theorem list_get_mem_fin
    (values : List α)
    (index : Fin values.length) :
    values.get index ∈ values := by
  induction values with
  | nil =>
      exact False.elim (Nat.not_lt_zero index.val index.isLt)
  | cons head tail ih =>
      cases index with
      | mk value bound =>
          cases value with
          | zero =>
              simp
          | succ value =>
              have tailBound : value < tail.length :=
                Nat.succ_lt_succ_iff.mp bound
              exact
                List.mem_cons_of_mem head
                  (ih ⟨value, tailBound⟩)

theorem list_get?_some_bound
    {values : List α}
    {index : Nat}
    {value : α}
    (found : listGet? values index = some value) :
    index < values.length := by
  induction values generalizing index with
  | nil =>
      simp [listGet?] at found
  | cons head tail ih =>
      cases index with
      | zero =>
          simp
      | succ index =>
          simp only [listGet?] at found
          exact Nat.succ_lt_succ (ih found)

theorem list_get?_map
    (transform : α → β) :
    ∀ (values : List α) (index : Nat),
      listGet? (values.map transform) index =
        (listGet? values index).map transform := by
  intro values
  induction values with
  | nil =>
      intro index
      cases index <;> rfl
  | cons head tail ih =>
      intro index
      cases index with
      | zero =>
          rfl
      | succ index =>
          exact ih index

theorem list_get?_replicate
    (count : Nat)
    (value : α)
    (index : Nat)
    (indexBound : index < count) :
    listGet? (List.replicate count value) index = some value := by
  induction count generalizing index with
  | zero =>
      exact False.elim (Nat.not_lt_zero index indexBound)
  | succ count ih =>
      cases index with
      | zero =>
          rfl
      | succ index =>
          exact
            ih index
              (Nat.lt_of_succ_lt_succ indexBound)

theorem list_get?_finite_indices
    (n : Nat)
    (index : Fin n) :
    listGet? (finiteIndices n) index.val = some index := by
  let listIndex :
      Fin (finiteIndices n).length :=
    ⟨index.val, by
      rw [finite_indices_length]
      exact index.isLt⟩
  have lookup :=
    list_get?_eq_get (finiteIndices n) listIndex
  have valueExact :
      (finiteIndices n).get listIndex = index := by
    simpa [listIndex] using finite_indices_get n index
  rw [valueExact] at lookup
  exact lookup

theorem finite_indices_no_duplicates (n : Nat) :
    NoDuplicates (finiteIndices n) := by
  unfold NoDuplicates
  induction n with
  | zero =>
      simp [finiteIndices]
  | succ n ih =>
      rw [finiteIndices, List.pairwise_cons]
      constructor
      · intro shifted shiftedMember equal
        rcases List.mem_map.mp shiftedMember with
          ⟨prior, priorMember, shiftedExact⟩
        have shiftedValueExact :=
          congrArg Fin.val shiftedExact
        have zeroValueExact :=
          congrArg Fin.val equal
        have impossible :
            0 = prior.val + 1 :=
          zeroValueExact.trans shiftedValueExact.symm
        exact Nat.noConfusion impossible
      · rw [List.pairwise_map]
        exact ih.imp (by
          intro left right different shiftedExact
          apply different
          apply Fin.ext
          have valuesExact := congrArg Fin.val shiftedExact
          exact Nat.succ.inj valuesExact)

theorem filter_map_member_has_source
    (transform : α → Option β)
    {output : β} :
    ∀ {values : List α},
      output ∈ values.filterMap transform →
        ∃ input, input ∈ values ∧ transform input = some output := by
  intro values outputMember
  induction values with
  | nil =>
      simp at outputMember
  | cons head tail ih =>
      cases transformed : transform head with
      | none =>
          simp only [List.filterMap, transformed] at outputMember
          rcases ih outputMember with
            ⟨input, inputMember, inputExact⟩
          exact
            ⟨input, List.mem_cons_of_mem head inputMember,
              inputExact⟩
      | some headOutput =>
          simp only [List.filterMap, transformed,
            List.mem_cons] at outputMember
          rcases outputMember with headExact | tailMember
          · subst headOutput
            exact
              ⟨head, by simp, transformed⟩
          · rcases ih tailMember with
              ⟨input, inputMember, inputExact⟩
            exact
              ⟨input, List.mem_cons_of_mem head inputMember,
                inputExact⟩

theorem pairwise_filter_map_of_pairwise
    (R : α → α → Prop)
    (S : β → β → Prop)
    (transform : α → Option β)
    {values : List α}
    (sourcePairwise : values.Pairwise R)
    (preserves :
      ∀ left right,
        R left right →
        ∀ leftOutput rightOutput,
          transform left = some leftOutput →
          transform right = some rightOutput →
          S leftOutput rightOutput) :
    (values.filterMap transform).Pairwise S := by
  induction values with
  | nil =>
      simp
  | cons head tail ih =>
      rw [List.pairwise_cons] at sourcePairwise
      rcases sourcePairwise with
        ⟨headRelated, tailPairwise⟩
      cases transformed : transform head with
      | none =>
          simp only [List.filterMap, transformed]
          exact ih tailPairwise
      | some headOutput =>
          simp only [List.filterMap, transformed,
            List.pairwise_cons]
          constructor
          · intro output outputMember
            rcases filter_map_member_has_source
                transform outputMember with
              ⟨input, inputMember, inputExact⟩
            exact
              preserves head input
                (headRelated input inputMember)
                headOutput output transformed inputExact
          · exact ih tailPairwise

def publicOccurrencesInCollection
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length)
    (owningCollectionIndex :
      Fin
        ((registry.get sourceBlockIndex).block.nodes.get
          sourceNodeIndex).edgeCollections.length) :
    List (PublicReferenceOccurrence registry) :=
  let sourceBlock := registry.get sourceBlockIndex
  let sourceNode := sourceBlock.block.nodes.get sourceNodeIndex
  let owningCollection :=
    sourceNode.edgeCollections.get owningCollectionIndex
  (finiteIndices owningCollection.targets.length).filterMap
    fun targetIndex =>
      match targetExact :
          owningCollection.targets.get targetIndex with
      | .local _ =>
          none
      | .external ref =>
          some
            { sourceBlockIndex := sourceBlockIndex.val
              sourceBlockBound := sourceBlockIndex.isLt
              sourceBlock := sourceBlock
              sourceBlockLookup :=
                list_get?_eq_get registry sourceBlockIndex
              sourceNodeIndex := sourceNodeIndex.val
              sourceNodeBound := sourceNodeIndex.isLt
              sourceNode := sourceNode
              sourceNodeLookup :=
                list_get?_eq_get sourceBlock.block.nodes
                  sourceNodeIndex
              owningCollectionIndex := owningCollectionIndex.val
              owningCollection := owningCollection
              owningCollectionLookup :=
                list_get?_eq_get sourceNode.edgeCollections
                  owningCollectionIndex
              expectedTargetKind :=
                owningCollection.expectedTargetKind
              expectedTargetKindExact := rfl
              ref := ref
              targetPosition := targetIndex.val
              targetOccurrence := by
                have targetLookup :=
                  list_get?_eq_get owningCollection.targets
                    targetIndex
                rw [targetExact] at targetLookup
                exact targetLookup }

def publicOccurrencesInNode
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length) :
    List (PublicReferenceOccurrence registry) :=
  let sourceNode :=
    (registry.get sourceBlockIndex).block.nodes.get sourceNodeIndex
  (finiteIndices sourceNode.edgeCollections.length).flatMap
    (publicOccurrencesInCollection
      registry sourceBlockIndex sourceNodeIndex)

def publicOccurrencesInBlock
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length) :
    List (PublicReferenceOccurrence registry) :=
  let sourceBlock := registry.get sourceBlockIndex
  (finiteIndices sourceBlock.block.nodes.length).flatMap
    (publicOccurrencesInNode registry sourceBlockIndex)

def enumeratePublicReferenceOccurrences
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context)) :
    List (PublicReferenceOccurrence registry) :=
  (finiteIndices registry.length).flatMap
    (publicOccurrencesInBlock registry)

theorem public_occurrences_in_collection_identity_no_duplicates
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length)
    (owningCollectionIndex :
      Fin
        ((registry.get sourceBlockIndex).block.nodes.get
          sourceNodeIndex).edgeCollections.length) :
    NoDuplicates
      ((publicOccurrencesInCollection registry sourceBlockIndex
        sourceNodeIndex owningCollectionIndex).map
          PublicReferenceOccurrence.identity) := by
  unfold NoDuplicates
  rw [List.pairwise_map]
  unfold publicOccurrencesInCollection
  dsimp only
  apply pairwise_filter_map_of_pairwise
    (R := fun
      left right :
        Fin
          ((((registry.get sourceBlockIndex).block.nodes.get
            sourceNodeIndex).edgeCollections.get
              owningCollectionIndex).targets.length) =>
        left ≠ right)
    (S := fun
      left right : PublicReferenceOccurrence registry =>
        left.identity ≠ right.identity)
  · exact finite_indices_no_duplicates _
  · intro left right different leftOutput rightOutput
      leftExact rightExact identityExact
    split at leftExact
    · contradiction
    · rename_i leftRef leftTargetExact
      split at rightExact
      · contradiction
      · rename_i rightRef rightTargetExact
        have leftOutputExact :=
          Option.some.inj leftExact
        have rightOutputExact :=
          Option.some.inj rightExact
        have positionExact :=
          congrArg PublicOccurrenceIdentity.targetPosition
            identityExact
        rw [← leftOutputExact, ← rightOutputExact] at positionExact
        apply different
        apply Fin.ext
        exact positionExact

theorem public_occurrence_in_collection_has_collection_index
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length)
    (owningCollectionIndex :
      Fin
        ((registry.get sourceBlockIndex).block.nodes.get
          sourceNodeIndex).edgeCollections.length)
    {occurrence : PublicReferenceOccurrence registry}
    (member :
      occurrence ∈
        publicOccurrencesInCollection registry sourceBlockIndex
          sourceNodeIndex owningCollectionIndex) :
    occurrence.owningCollectionIndex =
      owningCollectionIndex.val := by
  unfold publicOccurrencesInCollection at member
  dsimp only at member
  rcases filter_map_member_has_source _ member with
    ⟨targetIndex, _, targetExact⟩
  split at targetExact
  · contradiction
  · have occurrenceExact :=
      Option.some.inj targetExact
    rw [← occurrenceExact]

theorem public_occurrences_in_node_identity_no_duplicates
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length) :
    NoDuplicates
      ((publicOccurrencesInNode registry sourceBlockIndex
        sourceNodeIndex).map
          PublicReferenceOccurrence.identity) := by
  unfold NoDuplicates publicOccurrencesInNode
  dsimp only
  rw [List.map_flatMap, List.pairwise_flatMap]
  constructor
  · intro collectionIndex _
    exact
      public_occurrences_in_collection_identity_no_duplicates
        registry sourceBlockIndex sourceNodeIndex collectionIndex
  · rw [List.Pairwise.imp_mem]
    refine (finite_indices_no_duplicates _).imp ?_
    intro left right different leftMember rightMember
    intro leftIdentity leftIdentityMember
      rightIdentity rightIdentityMember identityExact
    rcases List.mem_map.mp leftIdentityMember with
      ⟨leftOccurrence, leftOccurrenceMember,
        leftIdentityExact⟩
    rcases List.mem_map.mp rightIdentityMember with
      ⟨rightOccurrence, rightOccurrenceMember,
        rightIdentityExact⟩
    have occurrenceIdentityExact :
        leftOccurrence.identity =
          rightOccurrence.identity :=
      leftIdentityExact.trans
        (identityExact.trans rightIdentityExact.symm)
    have collectionIndexExact :=
      congrArg
        PublicOccurrenceIdentity.owningCollectionIndex
        occurrenceIdentityExact
    have leftCollectionIndex :=
      public_occurrence_in_collection_has_collection_index
        registry sourceBlockIndex sourceNodeIndex left
        leftOccurrenceMember
    have rightCollectionIndex :=
      public_occurrence_in_collection_has_collection_index
        registry sourceBlockIndex sourceNodeIndex right
        rightOccurrenceMember
    simp only [PublicReferenceOccurrence.identity] at collectionIndexExact
    rw [leftCollectionIndex, rightCollectionIndex] at collectionIndexExact
    apply different
    exact Fin.ext collectionIndexExact

theorem public_occurrence_in_node_has_node_index
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    (sourceNodeIndex :
      Fin
        (registry.get sourceBlockIndex).block.nodes.length)
    {occurrence : PublicReferenceOccurrence registry}
    (member :
      occurrence ∈
        publicOccurrencesInNode registry sourceBlockIndex
          sourceNodeIndex) :
    occurrence.sourceNodeIndex = sourceNodeIndex.val := by
  unfold publicOccurrencesInNode at member
  dsimp only at member
  rcases List.mem_flatMap.mp member with
    ⟨collectionIndex, _, collectionMember⟩
  unfold publicOccurrencesInCollection at collectionMember
  dsimp only at collectionMember
  rcases filter_map_member_has_source _ collectionMember with
    ⟨targetIndex, _, targetExact⟩
  split at targetExact
  · contradiction
  · have occurrenceExact :=
      Option.some.inj targetExact
    rw [← occurrenceExact]

theorem public_occurrences_in_block_identity_no_duplicates
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length) :
    NoDuplicates
      ((publicOccurrencesInBlock registry sourceBlockIndex).map
        PublicReferenceOccurrence.identity) := by
  unfold NoDuplicates publicOccurrencesInBlock
  dsimp only
  rw [List.map_flatMap, List.pairwise_flatMap]
  constructor
  · intro nodeIndex _
    exact
      public_occurrences_in_node_identity_no_duplicates
        registry sourceBlockIndex nodeIndex
  · rw [List.Pairwise.imp_mem]
    refine (finite_indices_no_duplicates _).imp ?_
    intro left right different leftMember rightMember
    intro leftIdentity leftIdentityMember
      rightIdentity rightIdentityMember identityExact
    rcases List.mem_map.mp leftIdentityMember with
      ⟨leftOccurrence, leftOccurrenceMember,
        leftIdentityExact⟩
    rcases List.mem_map.mp rightIdentityMember with
      ⟨rightOccurrence, rightOccurrenceMember,
        rightIdentityExact⟩
    have occurrenceIdentityExact :
        leftOccurrence.identity =
          rightOccurrence.identity :=
      leftIdentityExact.trans
        (identityExact.trans rightIdentityExact.symm)
    have nodeIndexExact :=
      congrArg PublicOccurrenceIdentity.sourceNodeIndex
        occurrenceIdentityExact
    have leftNodeIndex :=
      public_occurrence_in_node_has_node_index
        registry sourceBlockIndex left leftOccurrenceMember
    have rightNodeIndex :=
      public_occurrence_in_node_has_node_index
        registry sourceBlockIndex right rightOccurrenceMember
    simp only [PublicReferenceOccurrence.identity] at nodeIndexExact
    rw [leftNodeIndex, rightNodeIndex] at nodeIndexExact
    apply different
    exact Fin.ext nodeIndexExact

theorem public_occurrence_in_block_has_block_index
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (sourceBlockIndex : Fin registry.length)
    {occurrence : PublicReferenceOccurrence registry}
    (member :
      occurrence ∈
        publicOccurrencesInBlock registry sourceBlockIndex) :
    occurrence.sourceBlockIndex = sourceBlockIndex.val := by
  unfold publicOccurrencesInBlock at member
  dsimp only at member
  rcases List.mem_flatMap.mp member with
    ⟨nodeIndex, _, nodeMember⟩
  unfold publicOccurrencesInNode at nodeMember
  dsimp only at nodeMember
  rcases List.mem_flatMap.mp nodeMember with
    ⟨collectionIndex, _, collectionMember⟩
  unfold publicOccurrencesInCollection at collectionMember
  dsimp only at collectionMember
  rcases filter_map_member_has_source _ collectionMember with
    ⟨targetIndex, _, targetExact⟩
  split at targetExact
  · contradiction
  · have occurrenceExact :=
      Option.some.inj targetExact
    rw [← occurrenceExact]

theorem enumerate_public_reference_occurrence_identities_no_duplicates
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context)) :
    NoDuplicates
      ((enumeratePublicReferenceOccurrences registry).map
        PublicReferenceOccurrence.identity) := by
  unfold NoDuplicates enumeratePublicReferenceOccurrences
  rw [List.map_flatMap, List.pairwise_flatMap]
  constructor
  · intro blockIndex _
    exact
      public_occurrences_in_block_identity_no_duplicates
        registry blockIndex
  · rw [List.Pairwise.imp_mem]
    refine (finite_indices_no_duplicates _).imp ?_
    intro left right different leftMember rightMember
    intro leftIdentity leftIdentityMember
      rightIdentity rightIdentityMember identityExact
    rcases List.mem_map.mp leftIdentityMember with
      ⟨leftOccurrence, leftOccurrenceMember,
        leftIdentityExact⟩
    rcases List.mem_map.mp rightIdentityMember with
      ⟨rightOccurrence, rightOccurrenceMember,
        rightIdentityExact⟩
    have occurrenceIdentityExact :
        leftOccurrence.identity =
          rightOccurrence.identity :=
      leftIdentityExact.trans
        (identityExact.trans rightIdentityExact.symm)
    have blockIndexExact :=
      congrArg PublicOccurrenceIdentity.sourceBlockIndex
        occurrenceIdentityExact
    have leftBlockIndex :=
      public_occurrence_in_block_has_block_index
        registry left leftOccurrenceMember
    have rightBlockIndex :=
      public_occurrence_in_block_has_block_index
        registry right rightOccurrenceMember
    simp only [PublicReferenceOccurrence.identity] at blockIndexExact
    rw [leftBlockIndex, rightBlockIndex] at blockIndexExact
    apply different
    exact Fin.ext blockIndexExact

def resolvePublicOccurrenceList
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) :
    List (PublicReferenceOccurrence registry) →
      Except PublicReferenceResolutionResidue
        (List (ResolvedEdge registry keysUnique))
  | [] =>
      .ok []
  | occurrence :: remaining =>
      match resolutionExact :
          resolvePublicReferenceOccurrence keysUnique occurrence with
      | .error residue =>
          .error residue
      | .ok resolved =>
          match resolvePublicOccurrenceList keysUnique remaining with
          | .error residue =>
              .error residue
          | .ok edges =>
              .ok
                ({ occurrence := occurrence
                   resolved := resolved
                   resolutionExact := resolutionExact } :: edges)

theorem resolve_public_occurrence_list_preserves_occurrences
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) :
    ∀ {occurrences : List (PublicReferenceOccurrence registry)}
      {edges : List (ResolvedEdge registry keysUnique)},
      resolvePublicOccurrenceList keysUnique occurrences = .ok edges →
        edges.map (fun edge => edge.occurrence) = occurrences := by
  intro occurrences
  induction occurrences with
  | nil =>
      intro edges resolved
      simp only [resolvePublicOccurrenceList] at resolved
      cases resolved
      rfl
  | cons occurrence remaining ih =>
      intro edges resolved
      simp only [resolvePublicOccurrenceList] at resolved
      split at resolved
      · contradiction
      · split at resolved
        · contradiction
        · rename_i resolvedReference resolutionExact
            remainingEdges remainingExact
          cases resolved
          simp only [List.map_cons, List.cons.injEq, true_and]
          exact ih remainingExact

theorem public_reference_occurrence_eq_of_identity_eq
    (left right : PublicReferenceOccurrence registry)
    (identityExact : left.identity = right.identity) :
    left = right := by
  rcases left with
    ⟨leftBlockIndex, leftBlockBound,
      leftBlock, leftBlockLookup,
      leftNodeIndex, leftNodeBound,
      leftNode, leftNodeLookup,
      leftCollectionIndex, leftCollection,
      leftCollectionLookup, leftExpectedKind,
      leftExpectedKindExact, leftRef,
      leftTargetPosition, leftTargetOccurrence⟩
  rcases right with
    ⟨rightBlockIndex, rightBlockBound,
      rightBlock, rightBlockLookup,
      rightNodeIndex, rightNodeBound,
      rightNode, rightNodeLookup,
      rightCollectionIndex, rightCollection,
      rightCollectionLookup, rightExpectedKind,
      rightExpectedKindExact, rightRef,
      rightTargetPosition, rightTargetOccurrence⟩
  simp only [PublicReferenceOccurrence.identity] at identityExact
  have blockIndexExact :
      leftBlockIndex = rightBlockIndex :=
    congrArg PublicOccurrenceIdentity.sourceBlockIndex identityExact
  have nodeIndexExact :
      leftNodeIndex = rightNodeIndex :=
    congrArg PublicOccurrenceIdentity.sourceNodeIndex identityExact
  have collectionIndexExact :
      leftCollectionIndex = rightCollectionIndex :=
    congrArg
      PublicOccurrenceIdentity.owningCollectionIndex identityExact
  have targetPositionExact :
      leftTargetPosition = rightTargetPosition :=
    congrArg PublicOccurrenceIdentity.targetPosition identityExact
  subst rightBlockIndex
  subst rightNodeIndex
  subst rightCollectionIndex
  subst rightTargetPosition
  have blockExact : leftBlock = rightBlock :=
    Option.some.inj
      (leftBlockLookup.symm.trans rightBlockLookup)
  subst rightBlock
  have nodeExact : leftNode = rightNode :=
    Option.some.inj
      (leftNodeLookup.symm.trans rightNodeLookup)
  subst rightNode
  have collectionExact :
      leftCollection = rightCollection :=
    Option.some.inj
      (leftCollectionLookup.symm.trans rightCollectionLookup)
  subst rightCollection
  have expectedKindExact :
      leftExpectedKind = rightExpectedKind :=
    leftExpectedKindExact.symm.trans rightExpectedKindExact
  subst rightExpectedKind
  have targetExact :
      (Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
          leftRef) =
        Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
          rightRef :=
    Option.some.inj
      (leftTargetOccurrence.symm.trans rightTargetOccurrence)
  have refExact : leftRef = rightRef := by
    cases targetExact
    rfl
  subst rightRef
  cases expectedKindExact
  congr

theorem public_reference_occurrence_mem_enumeration
    (occurrence : PublicReferenceOccurrence registry) :
    occurrence ∈ enumeratePublicReferenceOccurrences registry := by
  let blockIndex : Fin registry.length :=
    ⟨occurrence.sourceBlockIndex, occurrence.sourceBlockBound⟩
  have sourceBlockExact :
      registry.get blockIndex = occurrence.sourceBlock :=
    Option.some.inj
      ((list_get?_eq_get registry blockIndex).symm.trans
        occurrence.sourceBlockLookup)
  let nodeIndex :
      Fin (registry.get blockIndex).block.nodes.length :=
    ⟨occurrence.sourceNodeIndex, by
      rw [sourceBlockExact]
      exact occurrence.sourceNodeBound⟩
  have sourceNodeLookup :
      listGet? (registry.get blockIndex).block.nodes
          occurrence.sourceNodeIndex =
        some occurrence.sourceNode := by
    rw [sourceBlockExact]
    exact occurrence.sourceNodeLookup
  have sourceNodeExact :
      (registry.get blockIndex).block.nodes.get nodeIndex =
        occurrence.sourceNode :=
    Option.some.inj
      ((list_get?_eq_get
          (registry.get blockIndex).block.nodes nodeIndex).symm.trans
        sourceNodeLookup)
  have owningCollectionLookup :
      listGet?
          ((registry.get blockIndex).block.nodes.get
            nodeIndex).edgeCollections
          occurrence.owningCollectionIndex =
        some occurrence.owningCollection := by
    rw [sourceNodeExact]
    exact occurrence.owningCollectionLookup
  let collectionIndex :
      Fin
        (((registry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length) :=
    ⟨occurrence.owningCollectionIndex,
      list_get?_some_bound owningCollectionLookup⟩
  have owningCollectionExact :
      ((registry.get blockIndex).block.nodes.get nodeIndex).edgeCollections.get
          collectionIndex =
        occurrence.owningCollection :=
    Option.some.inj
      ((list_get?_eq_get
          ((registry.get blockIndex).block.nodes.get
            nodeIndex).edgeCollections collectionIndex).symm.trans
        owningCollectionLookup)
  have targetOccurrence :
      listGet?
          (((registry.get blockIndex).block.nodes.get
            nodeIndex).edgeCollections.get collectionIndex).targets
          occurrence.targetPosition =
        some
          (Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
            occurrence.ref) := by
    rw [owningCollectionExact]
    exact occurrence.targetOccurrence
  let targetIndex :
      Fin
        ((((registry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex).targets.length) :=
    ⟨occurrence.targetPosition,
      list_get?_some_bound targetOccurrence⟩
  have targetExact :
      (((registry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex).targets.get
          targetIndex =
        Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
          occurrence.ref :=
    Option.some.inj
      ((list_get?_eq_get
          (((registry.get blockIndex).block.nodes.get
            nodeIndex).edgeCollections.get collectionIndex).targets
          targetIndex).symm.trans targetOccurrence)
  unfold enumeratePublicReferenceOccurrences
  apply List.mem_flatMap.mpr
  refine ⟨blockIndex, finite_indices_complete blockIndex, ?_⟩
  unfold publicOccurrencesInBlock
  apply List.mem_flatMap.mpr
  refine ⟨nodeIndex, finite_indices_complete nodeIndex, ?_⟩
  unfold publicOccurrencesInNode
  apply List.mem_flatMap.mpr
  refine
    ⟨collectionIndex, finite_indices_complete collectionIndex, ?_⟩
  unfold publicOccurrencesInCollection
  apply List.mem_filterMap.mpr
  refine ⟨targetIndex, finite_indices_complete targetIndex, ?_⟩
  split
  · rename_i localIndex localExact
    have impossible :
        Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.local
            localIndex =
          Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
            occurrence.ref :=
      localExact.symm.trans targetExact
    cases impossible
  · rename_i foundRef foundExact
    have refExact : foundRef = occurrence.ref := by
      have constructorExact :
          Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
              foundRef =
            Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
              occurrence.ref :=
        foundExact.symm.trans targetExact
      cases constructorExact
      rfl
    subst foundRef
    apply congrArg some
    apply public_reference_occurrence_eq_of_identity_eq
    rfl

def NoDuplicateOccurrenceIdentity
    (edges : List (ResolvedEdge registry keysUnique)) : Prop :=
  NoDuplicates
    (edges.map (fun edge => edge.occurrence.identity))

structure ResolvedEdgeTable
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) where
  edges : List (ResolvedEdge registry keysUnique)
  sound :
    ∀ edge, edge ∈ edges →
      resolvePublicReferenceOccurrence
        keysUnique edge.occurrence = .ok edge.resolved
  complete :
    ∀ occurrence : PublicReferenceOccurrence registry,
      ∃ edge, edge ∈ edges ∧ edge.occurrence = occurrence
  occurrenceNoDuplicates :
    NoDuplicateOccurrenceIdentity edges

/--
Find the unique resolved edge carrying a public-reference occurrence identity.
-/
def ResolvedEdgeTable.findOccurrence?
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    Option (ResolvedEdge registry keysUnique) :=
  table.edges.find? fun edge =>
    decide (edge.occurrence.identity = occurrence.identity)

theorem ResolvedEdgeTable.find_occurrence_ne_none
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    table.findOccurrence? occurrence ≠ none := by
  intro foundNone
  rcases table.complete occurrence with
    ⟨edge, edgeMember, edgeOccurrenceExact⟩
  have rejected :=
    List.find?_eq_none.mp foundNone edge edgeMember
  apply rejected
  simp [edgeOccurrenceExact]

/--
Select the resolved edge for an occurrence constructively from table
completeness.
-/
def ResolvedEdgeTable.edgeForOccurrence
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    ResolvedEdge registry keysUnique :=
  (table.findOccurrence? occurrence).get
    (Option.isSome_iff_ne_none.mpr
      (table.find_occurrence_ne_none occurrence))

theorem ResolvedEdgeTable.edge_for_occurrence_found
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    table.findOccurrence? occurrence =
      some (table.edgeForOccurrence occurrence) := by
  exact
    (Option.some_get
      (Option.isSome_iff_ne_none.mpr
        (table.find_occurrence_ne_none occurrence))).symm

theorem ResolvedEdgeTable.edge_for_occurrence_member
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    table.edgeForOccurrence occurrence ∈ table.edges := by
  exact
    List.mem_of_find?_eq_some
      (table.edge_for_occurrence_found occurrence)

theorem ResolvedEdgeTable.edge_for_occurrence_exact
    (table : ResolvedEdgeTable registry keysUnique)
    (occurrence : PublicReferenceOccurrence registry) :
    (table.edgeForOccurrence occurrence).occurrence = occurrence := by
  apply public_reference_occurrence_eq_of_identity_eq
  have accepted :=
    List.find?_some (table.edge_for_occurrence_found occurrence)
  simpa [ResolvedEdgeTable.findOccurrence?] using
    of_decide_eq_true accepted

/--
Project public-reference resolution to the canonical target coordinates that
depend only on the expected kind and external reference.
-/
def publicReferenceResolutionCoordinates
    (_keysUnique :
      CanonicalRegistryKeysNoDup context registry)
    (occurrence : PublicReferenceOccurrence registry) :
    Except PublicReferenceResolutionResidue (Nat × Nat) :=
  if _expectedKindExact :
      occurrence.expectedTargetKind = occurrence.ref.kind then
    let targetKey : CanonicalRegistryKey context.kindSchema :=
      { kind := occurrence.ref.kind
        blockQ := occurrence.ref.target.blockQ }
    match
        findCanonicalRegistryLookup context targetKey registry with
    | none =>
        .error .targetMissing
    | some found =>
        if _targetBound :
            occurrence.ref.target.canonicalLocalIndex <
              found.targetBlock.block.nodes.length then
          .ok
            (found.targetBlockIndex,
              occurrence.ref.target.canonicalLocalIndex)
        else
          .error .canonicalMemberIndexOutOfBounds
  else
    .error .targetKindMismatch

theorem public_reference_resolution_coordinates_eq
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry)
    (occurrence : PublicReferenceOccurrence registry) :
    publicReferenceResolutionCoordinates keysUnique occurrence =
      match resolvePublicReferenceOccurrence keysUnique occurrence with
      | .error residue => .error residue
      | .ok resolved =>
          .ok
            (resolved.targetBlockIndex,
              resolved.targetNodeIndex.val) := by
  by_cases expectedKindExact :
      occurrence.expectedTargetKind = occurrence.ref.kind
  · cases targetLookup :
        findCanonicalRegistryLookup context
          { kind := occurrence.ref.kind
            blockQ := occurrence.ref.target.blockQ }
          registry with
    | none =>
        simp [
          publicReferenceResolutionCoordinates,
          resolvePublicReferenceOccurrence,
          expectedKindExact,
          targetLookup
        ]
    | some found =>
        by_cases targetBound :
            occurrence.ref.target.canonicalLocalIndex <
              found.targetBlock.block.nodes.length
        · simp [
            publicReferenceResolutionCoordinates,
            resolvePublicReferenceOccurrence,
            expectedKindExact,
            targetLookup,
            targetBound
          ]
        · simp [
            publicReferenceResolutionCoordinates,
            resolvePublicReferenceOccurrence,
            expectedKindExact,
            targetLookup,
            targetBound
          ]
  · simp [
      publicReferenceResolutionCoordinates,
      resolvePublicReferenceOccurrence,
      expectedKindExact
    ]

theorem public_reference_resolution_coordinates_congr
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry)
    (leftOccurrence rightOccurrence :
      PublicReferenceOccurrence registry)
    (expectedKindExact :
      leftOccurrence.expectedTargetKind =
        rightOccurrence.expectedTargetKind)
    (refExact : leftOccurrence.ref = rightOccurrence.ref) :
    publicReferenceResolutionCoordinates
        keysUnique leftOccurrence =
      publicReferenceResolutionCoordinates
        keysUnique rightOccurrence := by
  unfold publicReferenceResolutionCoordinates
  rw [expectedKindExact, refExact]

/--
Resolution coordinates are insensitive to occurrence metadata once expected
kind and external reference agree.
-/
theorem resolved_coordinates_congr
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry)
    {leftOccurrence rightOccurrence :
      PublicReferenceOccurrence registry}
    (leftResolved :
      ResolvedPublicReference leftOccurrence)
    (rightResolved :
      ResolvedPublicReference rightOccurrence)
    (leftResolutionExact :
      resolvePublicReferenceOccurrence
        keysUnique leftOccurrence = .ok leftResolved)
    (rightResolutionExact :
      resolvePublicReferenceOccurrence
        keysUnique rightOccurrence = .ok rightResolved)
    (expectedKindExact :
      leftOccurrence.expectedTargetKind =
        rightOccurrence.expectedTargetKind)
    (refExact : leftOccurrence.ref = rightOccurrence.ref) :
    leftResolved.targetBlockIndex =
        rightResolved.targetBlockIndex ∧
      leftResolved.targetNodeIndex.val =
        rightResolved.targetNodeIndex.val := by
  have coordinatesExact :=
    public_reference_resolution_coordinates_congr
      keysUnique leftOccurrence rightOccurrence
      expectedKindExact refExact
  have leftCoordinates :=
    public_reference_resolution_coordinates_eq
      keysUnique leftOccurrence
  have rightCoordinates :=
    public_reference_resolution_coordinates_eq
      keysUnique rightOccurrence
  rw [leftResolutionExact] at leftCoordinates
  rw [rightResolutionExact] at rightCoordinates
  have pairExact :
      (leftResolved.targetBlockIndex,
          leftResolved.targetNodeIndex.val) =
        (rightResolved.targetBlockIndex,
          rightResolved.targetNodeIndex.val) :=
    Except.ok.inj
      (leftCoordinates.symm.trans
        (coordinatesExact.trans rightCoordinates))
  exact Prod.mk.inj pairExact

/-- Transport resolved-reference data across equality of occurrences. -/
def ResolvedPublicReference.transportOccurrence
    {leftOccurrence rightOccurrence :
      PublicReferenceOccurrence registry}
    (occurrenceExact : leftOccurrence = rightOccurrence)
    (resolved : ResolvedPublicReference leftOccurrence) :
    ResolvedPublicReference rightOccurrence := by
  cases occurrenceExact
  exact resolved

theorem resolve_public_reference_occurrence_transport
    {leftOccurrence rightOccurrence :
      PublicReferenceOccurrence registry}
    (occurrenceExact : leftOccurrence = rightOccurrence)
    (resolved : ResolvedPublicReference leftOccurrence)
    (resolutionExact :
      resolvePublicReferenceOccurrence
          keysUnique leftOccurrence = .ok resolved) :
    resolvePublicReferenceOccurrence
        keysUnique rightOccurrence =
      .ok
        (resolved.transportOccurrence occurrenceExact) := by
  cases occurrenceExact
  exact resolutionExact

def validatePublicOccurrences
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) :
    Except PublicReferenceResolutionResidue
      (ResolvedEdgeTable registry keysUnique) :=
  match resolvedExact :
      resolvePublicOccurrenceList keysUnique
        (enumeratePublicReferenceOccurrences registry) with
  | .error residue =>
      .error residue
  | .ok edges =>
      .ok
        { edges := edges
          sound := by
            intro edge _
            exact edge.resolutionExact
          complete := by
            intro occurrence
            have preserved :=
              resolve_public_occurrence_list_preserves_occurrences
                keysUnique resolvedExact
            have occurrenceMember :
                occurrence ∈ edges.map (fun edge => edge.occurrence) := by
              rw [preserved]
              exact
                public_reference_occurrence_mem_enumeration
                  occurrence
            rcases List.mem_map.mp occurrenceMember with
              ⟨edge, edgeMember, edgeExact⟩
            exact ⟨edge, edgeMember, edgeExact⟩
          occurrenceNoDuplicates := by
            unfold NoDuplicateOccurrenceIdentity
            have preserved :=
              resolve_public_occurrence_list_preserves_occurrences
                keysUnique resolvedExact
            have identityProjection :
                edges.map (fun edge => edge.occurrence.identity) =
                  (enumeratePublicReferenceOccurrences registry).map
                    PublicReferenceOccurrence.identity := by
              simpa only [List.map_map, Function.comp_apply] using
                congrArg
                  (List.map PublicReferenceOccurrence.identity)
                  preserved
            rw [identityProjection]
            exact
              enumerate_public_reference_occurrence_identities_no_duplicates
                registry }

def EveryPublicReferenceOccurrenceResolved
    {context : GraphCodecContext}
    (registry : List (SomeCanonicalBlock context))
    (keysUnique :
      CanonicalRegistryKeysNoDup context registry) : Prop :=
  ∃ table,
    validatePublicOccurrences registry keysUnique = .ok table

def CrossBlockReference
    (table : ResolvedEdgeTable registry keysUnique)
    (source target : Nat) : Prop :=
  ∃ edge, edge ∈ table.edges ∧
    edge.occurrence.sourceBlockIndex = source ∧
    edge.resolved.targetBlockIndex = target

inductive DependencyResidue
  | crossBlockCycle
  deriving DecidableEq, Repr

structure DependencyCertificate
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) where
  height : Nat → Nat
  indexBound :
    ∀ index, index < registry.length →
      height index < registry.length
  decreases :
    ∀ {source target},
      CrossBlockReference table source target →
      height target < height source

def collectTargetHeights
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (heights : List (Option Nat))
    (source : Nat) :
    List (ResolvedEdge registry keysUnique) →
      Option (List Nat)
  | [] =>
      some []
  | edge :: remaining =>
      match collectTargetHeights heights source remaining with
      | none =>
          none
      | some remainingHeights =>
          if edge.occurrence.sourceBlockIndex = source then
            match listGet? heights edge.resolved.targetBlockIndex with
            | some (some targetHeight) =>
                some (targetHeight :: remainingHeights)
            | _ =>
                none
          else
            some remainingHeights

def targetHeightsForSource
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source : Nat) :
    Option (List Nat) :=
  collectTargetHeights heights source table.edges

theorem collect_target_heights_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (heights : List (Option Nat))
    (source : Nat) :
    ∀ (edges : List (ResolvedEdge registry keysUnique)),
      (∀ edge, edge ∈ edges →
        edge.occurrence.sourceBlockIndex = source →
        ∃ targetHeight,
          listGet? heights edge.resolved.targetBlockIndex =
            some (some targetHeight)) →
      ∃ targetHeights,
        collectTargetHeights heights source edges =
          some targetHeights := by
  intro edges allTargetsResolved
  induction edges with
  | nil =>
      exact ⟨[], rfl⟩
  | cons edge remaining ih =>
      have remainingResolved :
          ∀ remainingEdge, remainingEdge ∈ remaining →
            remainingEdge.occurrence.sourceBlockIndex = source →
            ∃ targetHeight,
              listGet? heights
                  remainingEdge.resolved.targetBlockIndex =
                some (some targetHeight) := by
        intro remainingEdge remainingMember sourceExact
        exact
          allTargetsResolved remainingEdge
            (List.mem_cons_of_mem edge remainingMember)
            sourceExact
      rcases ih remainingResolved with
        ⟨remainingHeights, remainingExact⟩
      by_cases sourceExact :
          edge.occurrence.sourceBlockIndex = source
      · rcases
          allTargetsResolved edge (by simp) sourceExact with
          ⟨targetHeight, targetExact⟩
        exact
          ⟨targetHeight :: remainingHeights, by
            simp [collectTargetHeights, remainingExact,
              sourceExact, targetExact]⟩
      · exact
          ⟨remainingHeights, by
            simp [collectTargetHeights, remainingExact,
              sourceExact]⟩

theorem collect_target_heights_contains_edge
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (heights : List (Option Nat))
    (source : Nat) :
    ∀ {edges : List (ResolvedEdge registry keysUnique)}
      {targetHeights : List Nat},
      collectTargetHeights heights source edges =
          some targetHeights →
      ∀ edge, edge ∈ edges →
        edge.occurrence.sourceBlockIndex = source →
        ∃ targetHeight,
          targetHeight ∈ targetHeights ∧
          listGet? heights edge.resolved.targetBlockIndex =
            some (some targetHeight) := by
  intro edges
  induction edges with
  | nil =>
      intro targetHeights collected edge edgeMember
      simp at edgeMember
  | cons head remaining ih =>
      intro targetHeights collected edge edgeMember edgeSource
      cases remainingResult :
          collectTargetHeights heights source remaining with
      | none =>
          simp [collectTargetHeights, remainingResult] at collected
      | some remainingHeights =>
          by_cases headSource :
              head.occurrence.sourceBlockIndex = source
          · cases targetLookup :
                listGet? heights head.resolved.targetBlockIndex with
            | none =>
                simp [collectTargetHeights, remainingResult,
                  headSource, targetLookup] at collected
            | some optionalHeight =>
                cases optionalHeight with
                | none =>
                    simp [collectTargetHeights, remainingResult,
                      headSource, targetLookup] at collected
                | some headHeight =>
                    have targetHeightsExact :
                        targetHeights =
                          headHeight :: remainingHeights := by
                      simpa [collectTargetHeights, remainingResult,
                        headSource, targetLookup] using collected.symm
                    subst targetHeights
                    simp only [List.mem_cons] at edgeMember
                    rcases edgeMember with edgeExact | remainingMember
                    · subst edge
                      exact
                        ⟨headHeight, by simp, targetLookup⟩
                    · rcases
                        ih remainingResult edge remainingMember
                          edgeSource with
                        ⟨targetHeight, targetMember, targetExact⟩
                      exact
                        ⟨targetHeight,
                          List.mem_cons_of_mem headHeight targetMember,
                          targetExact⟩
          · have targetHeightsExact :
                targetHeights = remainingHeights := by
              simpa [collectTargetHeights, remainingResult,
                headSource] using collected.symm
            subst targetHeights
            simp only [List.mem_cons] at edgeMember
            rcases edgeMember with edgeExact | remainingMember
            · subst edge
              contradiction
            · exact
                ih remainingResult edge remainingMember edgeSource

theorem collect_target_heights_member_has_edge
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (heights : List (Option Nat))
    (source : Nat) :
    ∀ {edges : List (ResolvedEdge registry keysUnique)}
      {targetHeights : List Nat},
      collectTargetHeights heights source edges =
          some targetHeights →
      ∀ targetHeight, targetHeight ∈ targetHeights →
        ∃ edge,
          edge ∈ edges ∧
          edge.occurrence.sourceBlockIndex = source ∧
          listGet? heights edge.resolved.targetBlockIndex =
            some (some targetHeight) := by
  intro edges
  induction edges with
  | nil =>
      intro targetHeights collected targetHeight targetMember
      have targetHeightsExact : targetHeights = [] := by
        simpa [collectTargetHeights] using collected.symm
      subst targetHeights
      simp at targetMember
  | cons head remaining ih =>
      intro targetHeights collected targetHeight targetMember
      cases remainingResult :
          collectTargetHeights heights source remaining with
      | none =>
          simp [collectTargetHeights, remainingResult] at collected
      | some remainingHeights =>
          by_cases headSource :
              head.occurrence.sourceBlockIndex = source
          · cases targetLookup :
                listGet? heights head.resolved.targetBlockIndex with
            | none =>
                simp [collectTargetHeights, remainingResult,
                  headSource, targetLookup] at collected
            | some optionalHeight =>
                cases optionalHeight with
                | none =>
                    simp [collectTargetHeights, remainingResult,
                      headSource, targetLookup] at collected
                | some headHeight =>
                    have targetHeightsExact :
                        targetHeights =
                          headHeight :: remainingHeights := by
                      simpa [collectTargetHeights, remainingResult,
                        headSource, targetLookup] using collected.symm
                    subst targetHeights
                    simp only [List.mem_cons] at targetMember
                    rcases targetMember with heightExact | remainingMember
                    · subst targetHeight
                      exact
                        ⟨head, by simp, headSource, targetLookup⟩
                    · rcases
                        ih remainingResult targetHeight
                          remainingMember with
                        ⟨edge, edgeMember, edgeSource, edgeLookup⟩
                      exact
                        ⟨edge,
                          List.mem_cons_of_mem head edgeMember,
                          edgeSource, edgeLookup⟩
          · have targetHeightsExact :
                targetHeights = remainingHeights := by
              simpa [collectTargetHeights, remainingResult,
                headSource] using collected.symm
            subst targetHeights
            rcases ih remainingResult targetHeight targetMember with
              ⟨edge, edgeMember, edgeSource, edgeLookup⟩
            exact
              ⟨edge, List.mem_cons_of_mem head edgeMember,
                edgeSource, edgeLookup⟩

def heightAboveTargets : List Nat → Nat
  | [] =>
      0
  | head :: tail =>
      Nat.max (Nat.succ head) (heightAboveTargets tail)

theorem member_lt_height_above_targets
    {height : Nat} :
    ∀ {targetHeights : List Nat},
      height ∈ targetHeights →
      height < heightAboveTargets targetHeights := by
  intro targetHeights heightMember
  induction targetHeights with
  | nil =>
      simp at heightMember
  | cons head tail ih =>
      simp only [List.mem_cons] at heightMember
      rcases heightMember with headExact | tailMember
      · subst head
        exact
          Nat.lt_of_lt_of_le
            (Nat.lt_succ_self height)
            (Nat.le_max_left _ _)
      · exact
          Nat.lt_of_lt_of_le
            (ih tailMember)
            (Nat.le_max_right _ _)

theorem height_above_targets_le
    (bound : Nat) :
    ∀ (targetHeights : List Nat),
      (∀ height, height ∈ targetHeights → height < bound) →
      heightAboveTargets targetHeights ≤ bound := by
  intro targetHeights allTargetsLower
  induction targetHeights with
  | nil =>
      exact Nat.zero_le bound
  | cons head tail ih =>
      rw [heightAboveTargets]
      rw [Nat.max_le]
      constructor
      · exact allTargetsLower head (by simp)
      · apply ih
        intro height heightMember
        exact
          allTargetsLower height
            (List.mem_cons_of_mem head heightMember)

def dependencyHeightAt
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source : Nat) :
    Option Nat :=
  (targetHeightsForSource table heights source).map
    heightAboveTargets

theorem dependency_height_at_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source : Nat)
    (allTargetsResolved :
      ∀ edge, edge ∈ table.edges →
        edge.occurrence.sourceBlockIndex = source →
        ∃ targetHeight,
          listGet? heights edge.resolved.targetBlockIndex =
            some (some targetHeight)) :
    ∃ sourceHeight,
      dependencyHeightAt table heights source =
        some sourceHeight := by
  rcases
      collect_target_heights_complete heights source table.edges
        allTargetsResolved with
    ⟨targetHeights, targetHeightsExact⟩
  exact
    ⟨heightAboveTargets targetHeights, by
      simp [dependencyHeightAt, targetHeightsForSource,
        targetHeightsExact]⟩

theorem dependency_height_at_strictly_above_edge
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source sourceHeight : Nat)
    (sourceExact :
      dependencyHeightAt table heights source =
        some sourceHeight)
    (edge : ResolvedEdge registry keysUnique)
    (edgeMember : edge ∈ table.edges)
    (edgeSource :
      edge.occurrence.sourceBlockIndex = source)
    (targetHeight : Nat)
    (targetExact :
      listGet? heights edge.resolved.targetBlockIndex =
        some (some targetHeight)) :
    targetHeight < sourceHeight := by
  unfold dependencyHeightAt at sourceExact
  cases targetHeightsExact :
      targetHeightsForSource table heights source with
  | none =>
      simp [targetHeightsExact] at sourceExact
  | some targetHeights =>
      have sourceHeightExact :
          sourceHeight = heightAboveTargets targetHeights := by
        simpa [targetHeightsExact] using sourceExact.symm
      rcases
          collect_target_heights_contains_edge
            heights source targetHeightsExact edge edgeMember
              edgeSource with
        ⟨collectedHeight, collectedMember, collectedExact⟩
      have collectedHeightExact :
          collectedHeight = targetHeight := by
        have nestedExact :
            some (some collectedHeight) =
              some (some targetHeight) :=
          collectedExact.symm.trans targetExact
        cases nestedExact
        rfl
      subst collectedHeight
      rw [sourceHeightExact]
      exact member_lt_height_above_targets collectedMember

theorem dependency_height_at_resolves_lower_edge
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source sourceHeight : Nat)
    (sourceExact :
      dependencyHeightAt table heights source =
        some sourceHeight)
    (edge : ResolvedEdge registry keysUnique)
    (edgeMember : edge ∈ table.edges)
    (edgeSource :
      edge.occurrence.sourceBlockIndex = source) :
    ∃ targetHeight,
      listGet? heights edge.resolved.targetBlockIndex =
          some (some targetHeight) ∧
      targetHeight < sourceHeight := by
  unfold dependencyHeightAt at sourceExact
  cases targetHeightsExact :
      targetHeightsForSource table heights source with
  | none =>
      simp [targetHeightsExact] at sourceExact
  | some targetHeights =>
      rcases
          collect_target_heights_contains_edge
            heights source targetHeightsExact edge edgeMember
              edgeSource with
        ⟨targetHeight, _, targetExact⟩
      exact
        ⟨targetHeight, targetExact,
          dependency_height_at_strictly_above_edge
            table heights source sourceHeight sourceExact
              edge edgeMember edgeSource targetHeight targetExact⟩

def dependencyHeightStepAt
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source : Nat) :
    Option Nat :=
  match listGet? heights source with
  | some (some sourceHeight) =>
      some sourceHeight
  | _ =>
      dependencyHeightAt table heights source

theorem dependency_height_step_at_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (source : Nat)
    (allTargetsResolved :
      ∀ edge, edge ∈ table.edges →
        edge.occurrence.sourceBlockIndex = source →
        ∃ targetHeight,
          listGet? heights edge.resolved.targetBlockIndex =
            some (some targetHeight)) :
    ∃ sourceHeight,
      dependencyHeightStepAt table heights source =
        some sourceHeight := by
  unfold dependencyHeightStepAt
  cases sourceLookup : listGet? heights source with
  | none =>
      exact
        dependency_height_at_complete table heights source
          allTargetsResolved
  | some optionalHeight =>
      cases optionalHeight with
      | none =>
          exact
            dependency_height_at_complete table heights source
              allTargetsResolved
      | some sourceHeight =>
          exact ⟨sourceHeight, rfl⟩

def dependencyPass
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat)) :
    List (Option Nat) :=
  (finiteIndices registry.length).map
    (fun source =>
      dependencyHeightStepAt table heights source.val)

theorem dependency_pass_lookup
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (index : Nat)
    (indexBound : index < registry.length) :
    listGet? (dependencyPass table heights) index =
      some (dependencyHeightStepAt table heights index) := by
  unfold dependencyPass
  rw [list_get?_map]
  rw [list_get?_finite_indices
    registry.length ⟨index, indexBound⟩]
  rfl

theorem dependency_pass_preserves_assigned
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat))
    (index height : Nat)
    (indexBound : index < registry.length)
    (assigned :
      listGet? heights index = some (some height)) :
    listGet? (dependencyPass table heights) index =
      some (some height) := by
  rw [dependency_pass_lookup table heights index indexBound]
  unfold dependencyHeightStepAt
  rw [assigned]

def iterateDependencyPass
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    Nat → List (Option Nat) → List (Option Nat)
  | 0, heights =>
      heights
  | passes + 1, heights =>
      dependencyPass table
        (iterateDependencyPass table passes heights)

theorem iterate_dependency_pass_preserves_assigned
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (passes : Nat)
    (heights : List (Option Nat))
    (index height : Nat)
    (indexBound : index < registry.length)
    (assigned :
      listGet? heights index = some (some height)) :
    listGet? (iterateDependencyPass table passes heights) index =
      some (some height) := by
  induction passes with
  | zero =>
      exact assigned
  | succ passes ih =>
      rw [iterateDependencyPass]
      exact
        dependency_pass_preserves_assigned
          table _ index height indexBound ih

theorem iterate_dependency_pass_add
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    ∀ left right heights,
      iterateDependencyPass table (left + right) heights =
        iterateDependencyPass table left
          (iterateDependencyPass table right heights) := by
  intro left
  induction left with
  | zero =>
      intro right heights
      simp [iterateDependencyPass]
  | succ left ih =>
      intro right heights
      rw [Nat.succ_add]
      simp only [iterateDependencyPass]
      rw [ih]

def initialDependencyState
    (registry : List (SomeCanonicalBlock context)) :
    List (Option Nat) :=
  List.replicate registry.length none

def dependencyStateAfter
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (passes : Nat) :
    List (Option Nat) :=
  iterateDependencyPass table passes
    (initialDependencyState registry)

theorem dependency_state_after_preserves_assigned
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (earlier extra index height : Nat)
    (indexBound : index < registry.length)
    (assigned :
      listGet? (dependencyStateAfter table earlier) index =
        some (some height)) :
    listGet?
        (dependencyStateAfter table (extra + earlier)) index =
      some (some height) := by
  unfold dependencyStateAfter
  rw [iterate_dependency_pass_add]
  exact
    iterate_dependency_pass_preserves_assigned
      table extra _ index height indexBound assigned

theorem dependency_state_after_orders_edges
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    ∀ passes edge,
      edge ∈ table.edges →
      ∀ sourceHeight,
        listGet? (dependencyStateAfter table passes)
            edge.occurrence.sourceBlockIndex =
          some (some sourceHeight) →
        ∃ targetHeight,
          listGet? (dependencyStateAfter table passes)
              edge.resolved.targetBlockIndex =
            some (some targetHeight) ∧
          targetHeight < sourceHeight := by
  intro passes
  induction passes with
  | zero =>
      intro edge edgeMember sourceHeight sourceAssigned
      have emptyLookup :
          listGet? (initialDependencyState registry)
              edge.occurrence.sourceBlockIndex =
            some (none : Option Nat) :=
        list_get?_replicate registry.length none
          edge.occurrence.sourceBlockIndex
          edge.occurrence.sourceBlockBound
      unfold dependencyStateAfter at sourceAssigned
      simp only [iterateDependencyPass] at sourceAssigned
      rw [emptyLookup] at sourceAssigned
      cases sourceAssigned
  | succ passes ih =>
      intro edge edgeMember sourceHeight sourceAssigned
      let previous := dependencyStateAfter table passes
      have sourceAssignedStep :
          listGet? (dependencyPass table previous)
              edge.occurrence.sourceBlockIndex =
            some (some sourceHeight) := by
        simpa [dependencyStateAfter, previous,
          iterateDependencyPass] using sourceAssigned
      have sourceStepLookup :=
        dependency_pass_lookup table previous
          edge.occurrence.sourceBlockIndex
          edge.occurrence.sourceBlockBound
      have sourceStepExact :
          dependencyHeightStepAt table previous
              edge.occurrence.sourceBlockIndex =
            some sourceHeight :=
        Option.some.inj
          (sourceStepLookup.symm.trans sourceAssignedStep)
      unfold dependencyHeightStepAt at sourceStepExact
      cases previousSource :
          listGet? previous edge.occurrence.sourceBlockIndex with
      | none =>
          have computedExact :
              dependencyHeightAt table previous
                  edge.occurrence.sourceBlockIndex =
                some sourceHeight := by
            simpa [previousSource] using sourceStepExact
          rcases
              dependency_height_at_resolves_lower_edge
                table previous edge.occurrence.sourceBlockIndex
                  sourceHeight computedExact edge edgeMember rfl with
            ⟨targetHeight, previousTarget, targetLower⟩
          refine ⟨targetHeight, ?_, targetLower⟩
          have preserved :=
            dependency_pass_preserves_assigned
              table previous edge.resolved.targetBlockIndex
                targetHeight edge.resolved.targetBlockBound
                previousTarget
          simpa [dependencyStateAfter, previous,
            iterateDependencyPass] using preserved
      | some optionalHeight =>
          cases optionalHeight with
          | none =>
              have computedExact :
                  dependencyHeightAt table previous
                      edge.occurrence.sourceBlockIndex =
                    some sourceHeight := by
                simpa [previousSource] using sourceStepExact
              rcases
                  dependency_height_at_resolves_lower_edge
                    table previous edge.occurrence.sourceBlockIndex
                      sourceHeight computedExact edge edgeMember rfl with
                ⟨targetHeight, previousTarget, targetLower⟩
              refine ⟨targetHeight, ?_, targetLower⟩
              have preserved :=
                dependency_pass_preserves_assigned
                  table previous edge.resolved.targetBlockIndex
                    targetHeight edge.resolved.targetBlockBound
                    previousTarget
              simpa [dependencyStateAfter, previous,
                iterateDependencyPass] using preserved
          | some previousHeight =>
              have previousHeightExact :
                  previousHeight = sourceHeight := by
                simpa [previousSource] using sourceStepExact
              subst previousHeight
              rcases
                  ih edge edgeMember sourceHeight previousSource with
                ⟨targetHeight, previousTarget, targetLower⟩
              refine ⟨targetHeight, ?_, targetLower⟩
              have preserved :=
                dependency_pass_preserves_assigned
                  table previous edge.resolved.targetBlockIndex
                    targetHeight edge.resolved.targetBlockBound
                    previousTarget
              simpa [dependencyStateAfter, previous,
                iterateDependencyPass] using preserved

def computedDependencyState
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    List (Option Nat) :=
  dependencyStateAfter table registry.length

def dependencyStateHeight
    (heights : List (Option Nat))
    (index : Nat) : Nat :=
  match listGet? heights index with
  | some (some height) =>
      height
  | _ =>
      0

def dependencyBoundsValid
    (registry : List (SomeCanonicalBlock context))
    (heights : List (Option Nat)) : Bool :=
  (finiteIndices registry.length).all
    (fun index =>
      decide
        (dependencyStateHeight heights index.val <
          registry.length))

def dependencyEdgesDecrease
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (heights : List (Option Nat)) : Bool :=
  table.edges.all
    (fun edge =>
      decide
        (dependencyStateHeight heights
            edge.resolved.targetBlockIndex <
          dependencyStateHeight heights
            edge.occurrence.sourceBlockIndex))

theorem dependency_bounds_valid_sound
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {heights : List (Option Nat)}
    (valid :
      dependencyBoundsValid registry heights = true)
    (index : Nat)
    (indexBound : index < registry.length) :
    dependencyStateHeight heights index < registry.length := by
  apply of_decide_eq_true
  exact
    (List.all_eq_true.mp valid)
      ⟨index, indexBound⟩
      (finite_indices_complete ⟨index, indexBound⟩)

theorem dependency_edges_decrease_valid_sound
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    {heights : List (Option Nat)}
    (valid :
      dependencyEdgesDecrease table heights = true)
    (edge : ResolvedEdge registry keysUnique)
    (edgeMember : edge ∈ table.edges) :
    dependencyStateHeight heights
        edge.resolved.targetBlockIndex <
      dependencyStateHeight heights
        edge.occurrence.sourceBlockIndex := by
  apply of_decide_eq_true
  exact (List.all_eq_true.mp valid) edge edgeMember

def buildDependencyCertificate
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    Except DependencyResidue (DependencyCertificate table) :=
  let heights := computedDependencyState table
  if boundsValid :
      dependencyBoundsValid registry heights = true then
    if edgesValid :
        dependencyEdgesDecrease table heights = true then
      .ok
        { height := dependencyStateHeight heights
          indexBound := by
            intro index indexBound
            exact
              dependency_bounds_valid_sound
                boundsValid index indexBound
          decreases := by
            intro source target reference
            rcases reference with
              ⟨edge, edgeMember, sourceExact, targetExact⟩
            subst source
            subst target
            exact
              dependency_edges_decrease_valid_sound
                edgesValid edge edgeMember }
    else
      .error .crossBlockCycle
  else
    .error .crossBlockCycle

theorem build_dependency_sound
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    {certificate : DependencyCertificate table}
    (_built :
      buildDependencyCertificate table = .ok certificate)
    (edge : ResolvedEdge registry keysUnique)
    (edgeMember : edge ∈ table.edges) :
    certificate.height edge.resolved.targetBlockIndex <
      certificate.height edge.occurrence.sourceBlockIndex :=
  certificate.decreases
    ⟨edge, edgeMember, rfl, rfl⟩

theorem build_dependency_height_canonical
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    {left right : DependencyCertificate table}
    (leftBuilt :
      buildDependencyCertificate table = .ok left)
    (rightBuilt :
      buildDependencyCertificate table = .ok right) :
    left.height = right.height := by
  have resultsExact :
      (Except.ok left :
        Except DependencyResidue (DependencyCertificate table)) =
        .ok right :=
    leftBuilt.symm.trans rightBuilt
  cases resultsExact
  rfl

theorem filter_length_lt_of_member_false
    (predicate : α → Bool)
    (excluded : α) :
    ∀ {values : List α},
      excluded ∈ values →
      predicate excluded = false →
      (values.filter predicate).length < values.length := by
  intro values excludedMember excludedFalse
  induction values with
  | nil =>
      simp at excludedMember
  | cons head tail ih =>
      simp only [List.mem_cons] at excludedMember
      rcases excludedMember with headExact | tailMember
      · subst head
        simp only [List.filter, excludedFalse]
        exact
          Nat.lt_succ_of_le
            (List.length_filter_le predicate tail)
      · cases headAccepted : predicate head with
        | false =>
            simp only [List.filter, headAccepted, List.length_cons]
            exact
              Nat.lt_succ_of_le
                (List.length_filter_le predicate tail)
        | true =>
            simp only [List.filter, headAccepted, List.length_cons]
            exact Nat.succ_lt_succ (ih tailMember)

theorem filter_length_le_of_implication
    (weaker stronger : α → Bool)
    (implies :
      ∀ value, weaker value = true → stronger value = true) :
    ∀ values : List α,
      (values.filter weaker).length ≤
        (values.filter stronger).length := by
  intro values
  induction values with
  | nil =>
      simp
  | cons head tail ih =>
      cases weakerExact : weaker head with
      | false =>
          simp only [List.filter, weakerExact]
          cases strongerExact : stronger head with
          | false =>
              exact ih
          | true =>
              exact Nat.le.step ih
      | true =>
          have strongerExact :
              stronger head = true :=
            implies head weakerExact
          simp only [List.filter, weakerExact, strongerExact,
            List.length_cons]
          exact Nat.succ_le_succ ih

theorem filter_length_lt_of_strict_implication
    (weaker stronger : α → Bool)
    (implies :
      ∀ value, weaker value = true → stronger value = true)
    (strictWitness : α) :
    ∀ {values : List α},
      strictWitness ∈ values →
      weaker strictWitness = false →
      stronger strictWitness = true →
      (values.filter weaker).length <
        (values.filter stronger).length := by
  intro values witnessMember weakerFalse strongerTrue
  induction values with
  | nil =>
      simp at witnessMember
  | cons head tail ih =>
      simp only [List.mem_cons] at witnessMember
      rcases witnessMember with headExact | tailMember
      · subst head
        simp only [List.filter, weakerFalse, strongerTrue,
          List.length_cons]
        exact
          Nat.lt_succ_of_le
            (filter_length_le_of_implication
              weaker stronger implies tail)
      · cases weakerExact : weaker head with
        | false =>
            simp only [List.filter, weakerExact]
            cases strongerExact : stronger head with
            | false =>
                exact ih tailMember
            | true =>
                exact
                  Nat.lt_succ_of_le
                    (filter_length_le_of_implication
                      weaker stronger implies tail)
        | true =>
            have strongerExact :
                stronger head = true :=
              implies head weakerExact
            simp only [List.filter, weakerExact, strongerExact,
              List.length_cons]
            exact Nat.succ_lt_succ (ih tailMember)

def compressedDependencyRank
    (registry : List (SomeCanonicalBlock context))
    (rank : Nat → Nat)
    (index : Nat) : Nat :=
  ((finiteIndices registry.length).filter
    (fun candidate =>
      decide (rank candidate.val < rank index))).length

theorem compressed_dependency_rank_bound
    (registry : List (SomeCanonicalBlock context))
    (rank : Nat → Nat)
    (index : Nat)
    (indexBound : index < registry.length) :
    compressedDependencyRank registry rank index <
      registry.length := by
  unfold compressedDependencyRank
  have strict :=
    filter_length_lt_of_member_false
      (fun candidate : Fin registry.length =>
        decide (rank candidate.val < rank index))
      ⟨index, indexBound⟩
      (finite_indices_complete ⟨index, indexBound⟩)
      (by simp)
  simpa [finite_indices_length] using strict

theorem compressed_dependency_rank_decreases
    (registry : List (SomeCanonicalBlock context))
    (rank : Nat → Nat)
    (source target : Nat)
    (targetBound : target < registry.length)
    (targetLower : rank target < rank source) :
    compressedDependencyRank registry rank target <
      compressedDependencyRank registry rank source := by
  unfold compressedDependencyRank
  apply filter_length_lt_of_strict_implication
    (fun candidate : Fin registry.length =>
      decide (rank candidate.val < rank target))
    (fun candidate : Fin registry.length =>
      decide (rank candidate.val < rank source))
    (by
      intro candidate lower
      apply decide_eq_true
      exact
        Nat.lt_trans (of_decide_eq_true lower) targetLower)
    ⟨target, targetBound⟩
  · exact finite_indices_complete ⟨target, targetBound⟩
  · simp
  · exact decide_eq_true targetLower

theorem dependency_state_after_height_le_compressed_rank
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (rank : Nat → Nat)
    (ranked :
      ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex) :
    ∀ passes index height,
      index < registry.length →
      listGet? (dependencyStateAfter table passes) index =
          some (some height) →
      height ≤ compressedDependencyRank registry rank index := by
  intro passes
  induction passes with
  | zero =>
      intro index height indexBound assigned
      have emptyLookup :
          listGet?
              (initialDependencyState registry) index =
            some (none : Option Nat) := by
        exact
          list_get?_replicate registry.length none
            index indexBound
      unfold dependencyStateAfter at assigned
      simp only [iterateDependencyPass] at assigned
      rw [emptyLookup] at assigned
      cases assigned
  | succ passes ih =>
      intro index height indexBound assigned
      let previous := dependencyStateAfter table passes
      have assignedStep :
          listGet? (dependencyPass table previous) index =
            some (some height) := by
        simpa [dependencyStateAfter, previous,
          iterateDependencyPass] using assigned
      have stepLookup :=
        dependency_pass_lookup table previous index indexBound
      have stepExact :
          dependencyHeightStepAt table previous index =
            some height :=
        Option.some.inj (stepLookup.symm.trans assignedStep)
      unfold dependencyHeightStepAt at stepExact
      cases previousLookup : listGet? previous index with
      | none =>
          have computedExact :
              dependencyHeightAt table previous index =
                some height := by
            simpa [previousLookup] using stepExact
          unfold dependencyHeightAt at computedExact
          cases targetHeightsExact :
              targetHeightsForSource table previous index with
          | none =>
              simp [targetHeightsExact] at computedExact
          | some targetHeights =>
              have heightExact :
                  height = heightAboveTargets targetHeights := by
                simpa [targetHeightsExact] using computedExact.symm
              rw [heightExact]
              apply height_above_targets_le
              intro targetHeight targetMember
              rcases
                  collect_target_heights_member_has_edge
                    previous index targetHeightsExact
                      targetHeight targetMember with
                ⟨edge, edgeMember, edgeSource, edgeLookup⟩
              have targetBound :=
                ih edge.resolved.targetBlockIndex targetHeight
                  edge.resolved.targetBlockBound edgeLookup
              have targetRankLower :=
                compressed_dependency_rank_decreases
                  registry rank edge.occurrence.sourceBlockIndex
                    edge.resolved.targetBlockIndex
                    edge.resolved.targetBlockBound
                    (ranked edge edgeMember)
              rw [edgeSource] at targetRankLower
              exact Nat.lt_of_le_of_lt targetBound targetRankLower
      | some optionalHeight =>
          cases optionalHeight with
          | none =>
              have computedExact :
                  dependencyHeightAt table previous index =
                    some height := by
                simpa [previousLookup] using stepExact
              unfold dependencyHeightAt at computedExact
              cases targetHeightsExact :
                  targetHeightsForSource table previous index with
              | none =>
                  simp [targetHeightsExact] at computedExact
              | some targetHeights =>
                  have heightExact :
                      height = heightAboveTargets targetHeights := by
                    simpa [targetHeightsExact] using computedExact.symm
                  rw [heightExact]
                  apply height_above_targets_le
                  intro targetHeight targetMember
                  rcases
                      collect_target_heights_member_has_edge
                        previous index targetHeightsExact
                          targetHeight targetMember with
                    ⟨edge, edgeMember, edgeSource, edgeLookup⟩
                  have targetBound :=
                    ih edge.resolved.targetBlockIndex targetHeight
                      edge.resolved.targetBlockBound edgeLookup
                  have targetRankLower :=
                    compressed_dependency_rank_decreases
                      registry rank edge.occurrence.sourceBlockIndex
                        edge.resolved.targetBlockIndex
                        edge.resolved.targetBlockBound
                        (ranked edge edgeMember)
                  rw [edgeSource] at targetRankLower
                  exact Nat.lt_of_le_of_lt targetBound targetRankLower
          | some previousHeight =>
              have previousHeightExact :
                  previousHeight = height := by
                simpa [previousLookup] using stepExact
              subst previousHeight
              exact ih index height indexBound previousLookup

theorem dependency_state_after_resolves_compressed_rank
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (rank : Nat → Nat)
    (ranked :
      ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex) :
    ∀ passes index,
      index < registry.length →
      compressedDependencyRank registry rank index < passes →
      ∃ height,
        listGet? (dependencyStateAfter table passes) index =
          some (some height) := by
  intro passes
  induction passes with
  | zero =>
      intro index indexBound rankBound
      exact False.elim (Nat.not_lt_zero _ rankBound)
  | succ passes ih =>
      intro index indexBound rankBound
      have sourceRankBound :
          compressedDependencyRank registry rank index ≤ passes :=
        Nat.le_of_lt_succ rankBound
      have allTargetsResolved :
          ∀ edge, edge ∈ table.edges →
            edge.occurrence.sourceBlockIndex = index →
            ∃ targetHeight,
              listGet? (dependencyStateAfter table passes)
                  edge.resolved.targetBlockIndex =
                some (some targetHeight) := by
        intro edge edgeMember sourceExact
        have targetRankLower :
            compressedDependencyRank registry rank
                edge.resolved.targetBlockIndex <
              compressedDependencyRank registry rank
                edge.occurrence.sourceBlockIndex :=
          compressed_dependency_rank_decreases
            registry rank edge.occurrence.sourceBlockIndex
              edge.resolved.targetBlockIndex
              edge.resolved.targetBlockBound
              (ranked edge edgeMember)
        rw [sourceExact] at targetRankLower
        exact
          ih edge.resolved.targetBlockIndex
            edge.resolved.targetBlockBound
            (Nat.lt_of_lt_of_le targetRankLower sourceRankBound)
      rcases
          dependency_height_step_at_complete table
            (dependencyStateAfter table passes) index
            allTargetsResolved with
        ⟨sourceHeight, sourceHeightExact⟩
      refine ⟨sourceHeight, ?_⟩
      unfold dependencyStateAfter
      rw [iterateDependencyPass]
      rw [dependency_pass_lookup table _ index indexBound]
      change
        some
            (dependencyHeightStepAt table
              (dependencyStateAfter table passes) index) =
          some (some sourceHeight)
      rw [sourceHeightExact]

theorem computed_dependency_state_resolves_of_ranked
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (rank : Nat → Nat)
    (ranked :
      ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex)
    (index : Nat)
    (indexBound : index < registry.length) :
    ∃ height,
      listGet? (computedDependencyState table) index =
        some (some height) := by
  unfold computedDependencyState
  exact
    dependency_state_after_resolves_compressed_rank
      table rank ranked registry.length index indexBound
      (compressed_dependency_rank_bound
        registry rank index indexBound)

theorem dependency_bounds_valid_of_ranked
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (rank : Nat → Nat)
    (ranked :
      ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex) :
    dependencyBoundsValid registry
        (computedDependencyState table) = true := by
  apply List.all_eq_true.mpr
  intro index _
  apply decide_eq_true
  rcases
      computed_dependency_state_resolves_of_ranked
        table rank ranked index.val index.isLt with
    ⟨height, heightExact⟩
  have heightBound :
      height ≤
        compressedDependencyRank registry rank index.val :=
    dependency_state_after_height_le_compressed_rank
      table rank ranked registry.length index.val height
        index.isLt heightExact
  unfold dependencyStateHeight
  rw [heightExact]
  exact
    Nat.lt_of_le_of_lt heightBound
      (compressed_dependency_rank_bound
        registry rank index.val index.isLt)

theorem dependency_edges_decrease_of_ranked
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique)
    (rank : Nat → Nat)
    (ranked :
      ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex) :
    dependencyEdgesDecrease table
        (computedDependencyState table) = true := by
  apply List.all_eq_true.mpr
  intro edge edgeMember
  apply decide_eq_true
  rcases
      computed_dependency_state_resolves_of_ranked
        table rank ranked edge.occurrence.sourceBlockIndex
          edge.occurrence.sourceBlockBound with
    ⟨sourceHeight, sourceExact⟩
  rcases
      dependency_state_after_orders_edges
        table registry.length edge edgeMember sourceHeight
          sourceExact with
    ⟨targetHeight, targetExact, targetLower⟩
  change
    listGet? (computedDependencyState table)
        edge.resolved.targetBlockIndex =
      some (some targetHeight) at targetExact
  unfold dependencyStateHeight
  rw [sourceExact, targetExact]
  exact targetLower

theorem build_dependency_complete
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    (ranked :
      ∃ rank : Nat → Nat,
        ∀ edge, edge ∈ table.edges →
          rank edge.resolved.targetBlockIndex <
            rank edge.occurrence.sourceBlockIndex) :
    ∃ certificate,
      buildDependencyCertificate table = .ok certificate := by
  rcases ranked with ⟨rank, rankDecreases⟩
  have boundsValid :=
    dependency_bounds_valid_of_ranked table rank rankDecreases
  have edgesValid :=
    dependency_edges_decrease_of_ranked table rank rankDecreases
  unfold buildDependencyCertificate
  rw [dif_pos boundsValid, dif_pos edgesValid]
  exact ⟨_, rfl⟩

theorem build_dependency_cycle_iff
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique :
      CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    buildDependencyCertificate table = .error .crossBlockCycle ↔
      ¬ ∃ rank : Nat → Nat,
          ∀ edge, edge ∈ table.edges →
            rank edge.resolved.targetBlockIndex <
              rank edge.occurrence.sourceBlockIndex := by
  constructor
  · intro builtError ranked
    rcases build_dependency_complete ranked with
      ⟨certificate, builtOk⟩
    have impossible :
        (Except.error .crossBlockCycle :
          Except DependencyResidue (DependencyCertificate table)) =
          .ok certificate :=
      builtError.symm.trans builtOk
    cases impossible
  · intro noRank
    cases built : buildDependencyCertificate table with
    | error residue =>
        cases residue
        rfl
    | ok certificate =>
        apply False.elim
        apply noRank
        refine ⟨certificate.height, ?_⟩
        intro edge edgeMember
        exact
          build_dependency_sound built edge edgeMember

def BlockAddressesDerived
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Prop :=
  ∀ entry, entry ∈ registry →
    entry.blockQ =
      context.blockWireAddress entry.kind
        (encodeCanonicalBlock entry.block)

structure CanonicalCollectionOccurrence
    (nodes : List (CanonicalNode schema)) where
  sourceNodeIndex : Nat
  sourceNode : CanonicalNode schema
  sourceNodeLookup :
    listGet? nodes sourceNodeIndex = some sourceNode
  owningCollectionIndex : Nat
  owningCollection :
    EdgeCollection schema (ExternalRef schema)
  owningCollectionLookup :
    listGet? sourceNode.edgeCollections owningCollectionIndex =
      some owningCollection

structure LocalReferenceOccurrence
    (nodes : List (CanonicalNode schema))
    extends CanonicalCollectionOccurrence nodes where
  targetPosition : Nat
  localIndex : Nat
  targetExact :
    listGet? owningCollection.targets targetPosition =
      some
        (Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.local
          localIndex)

def NoLocalReference
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ _occurrence : LocalReferenceOccurrence nodes, False

def EveryLocalReferenceBound
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ occurrence : LocalReferenceOccurrence nodes,
    occurrence.localIndex < nodes.length

def EveryLocalReferenceExpectedKindExact
    (kind : schema.Kind)
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ occurrence : LocalReferenceOccurrence nodes,
    occurrence.owningCollection.expectedTargetKind = kind

def EveryUnorderedTargetListSortedWithMultiplicity
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ occurrence : CanonicalCollectionOccurrence nodes,
    occurrence.owningCollection.mode = .unordered →
    normalizeTargetList occurrence.owningCollection =
      occurrence.owningCollection.targets

def EveryOuterCollectionListSortedWithMultiplicity
    (nodes : List (CanonicalNode schema)) : Prop :=
  ∀ node, node ∈ nodes →
    normalizeOuterCollections node.edgeCollections =
      node.edgeCollections

structure CanonicalBlockWellFormed
    (block : CanonicalBlock schema kind) : Prop where
  form :
    match block with
    | .dagSingleton node =>
        NoLocalReference [node]
    | .cyclic nodes =>
        nodes ≠ []
  localReferencesBound :
    EveryLocalReferenceBound block.nodes
  localReferenceKindsExact :
    EveryLocalReferenceExpectedKindExact kind block.nodes
  unorderedTargetsNormalized :
    EveryUnorderedTargetListSortedWithMultiplicity block.nodes
  outerCollectionsNormalized :
    EveryOuterCollectionListSortedWithMultiplicity block.nodes
  canonicalTLV :
    decodeCanonicalBlockDetailed schema kind
        (encodeCanonicalBlock block) = .ok block

structure CanonicalRegistryWellFormed
    (context : GraphCodecContext)
    (registry : List (SomeCanonicalBlock context)) : Prop where
  blocks :
    ∀ index : Fin registry.length,
      CanonicalBlockWellFormed (registry.get index).block

def pureMaterializeCanonicalBlock :
    (block : CanonicalBlock schema kind) →
      PermutationWitness block.nodes.length →
      CanonicalBlock schema kind
  | .dagSingleton node, permutation =>
      .dagSingleton
        (normalizeMaterializedNode
          (relabelNode (permutationBijection permutation) node))
  | .cyclic nodes, permutation =>
      .cyclic
        ((relabelNodes nodes (permutationBijection permutation)).map
          normalizeMaterializedNode)

def pureCanonicalCandidateBytes
    (block : CanonicalBlock schema kind) : List GraphBytes :=
  (permutationWitnesses block.nodes.length).map
    (fun permutation =>
      encodeCanonicalBlock
        (pureMaterializeCanonicalBlock block permutation))

theorem pure_candidate_bytes_nonempty
    (block : CanonicalBlock schema kind) :
    pureCanonicalCandidateBytes block ≠ [] := by
  intro candidatesEmpty
  have sourceLengthZero :
      (permutationWitnesses block.nodes.length).length = 0 := by
    have lengthsExact := congrArg List.length candidatesEmpty
    simpa [pureCanonicalCandidateBytes] using lengthsExact
  have sourceEmpty :
      permutationWitnesses block.nodes.length = [] :=
    List.eq_nil_of_length_eq_zero sourceLengthZero
  exact
    (permutation_witnesses_nonempty block.nodes.length)
      sourceEmpty

structure StoredAtCanonicalMinimum
    (block : CanonicalBlock schema kind) where
  selectedPermutation : PermutationWitness block.nodes.length
  allCandidateBytes : List GraphBytes
  allCandidateBytesExact :
    allCandidateBytes = pureCanonicalCandidateBytes block
  selectedMaterialization : CanonicalBlock schema kind
  selectedMaterializationExact :
    selectedMaterialization =
      pureMaterializeCanonicalBlock block selectedPermutation
  selectedBytesAreMinimum :
    encodeCanonicalBlock selectedMaterialization =
      lexicographicMinimum allCandidateBytes
        (by
          rw [allCandidateBytesExact]
          exact pure_candidate_bytes_nonempty block)
  selectedPermutationUniqueProducer :
    ∀ permutation,
      encodeCanonicalBlock
          (pureMaterializeCanonicalBlock block permutation) =
        encodeCanonicalBlock selectedMaterialization →
      permutation = selectedPermutation
  storedEqualsSelectedMinimum : block = selectedMaterialization

inductive BlockStoredAtCanonicalMinimum
    (block : CanonicalBlock schema kind) : Prop
  | dagTrivial
      (node)
      (blockExact : block = .dagSingleton node)
      (wellFormed : CanonicalBlockWellFormed block)
  | cyclicSelected
      (wellFormed : CanonicalBlockWellFormed block)
      (certificate : StoredAtCanonicalMinimum block)

def EveryBlockStoredAtCanonicalMinimum
    (registry : List (SomeCanonicalBlock context)) : Prop :=
  ∀ entry, entry ∈ registry →
    BlockStoredAtCanonicalMinimum entry.block

structure ClosedRootedGraph (context : GraphCodecContext) where
  canonicalRegistry : List (SomeCanonicalBlock context)
  canonicalRoot :
    CanonicalNodePointer context canonicalRegistry
  registryStrictlySorted :
    CanonicalRegistryStrictOrder context canonicalRegistry
  registryKeysNoDup :
    CanonicalRegistryKeysNoDup context canonicalRegistry
  registryWellFormed :
    CanonicalRegistryWellFormed context canonicalRegistry
  connectivity :
    EveryCyclicBlockHasComputedConnectivity canonicalRegistry
  resolvedEdges :
    ResolvedEdgeTable canonicalRegistry registryKeysNoDup
  dependency :
    DependencyCertificate resolvedEdges
  blockAddressesDerived :
    BlockAddressesDerived context canonicalRegistry
  canonicalMinima :
    EveryBlockStoredAtCanonicalMinimum canonicalRegistry

structure SerializedCanonicalRoot where
  blockIndex : Nat
  localIndex : Nat

structure CanonicalRootedGraph (context : GraphCodecContext) where
  registry : List (SomeCanonicalBlock context)
  root : SerializedCanonicalRoot

def serializedCanonicalProjection
    (graph : ClosedRootedGraph context) :
    CanonicalRootedGraph context :=
  ⟨graph.canonicalRegistry,
    ⟨graph.canonicalRoot.blockIndex, graph.canonicalRoot.localIndex⟩⟩

structure FiniteBijection (leftSize rightSize : Nat) where
  forward : Fin leftSize → Fin rightSize
  inverse : Fin rightSize → Fin leftSize
  leftInverse : ∀ index, inverse (forward index) = index
  rightInverse : ∀ index, forward (inverse index) = index

def FiniteBijection.refl (size : Nat) :
    FiniteBijection size size :=
  { forward := fun index => index
    inverse := fun index => index
    leftInverse := fun _ => rfl
    rightInverse := fun _ => rfl }

/-- Reverse a finite bijection without choosing any new representatives. -/
def FiniteBijection.symm
    (bijection : FiniteBijection leftSize rightSize) :
    FiniteBijection rightSize leftSize :=
  { forward := bijection.inverse
    inverse := bijection.forward
    leftInverse := bijection.rightInverse
    rightInverse := bijection.leftInverse }

/-- Compose finite bijections in the same direction as graph transports. -/
def FiniteBijection.trans
    (leftMiddle : FiniteBijection leftSize middleSize)
    (middleRight : FiniteBijection middleSize rightSize) :
    FiniteBijection leftSize rightSize :=
  { forward := fun index =>
      middleRight.forward (leftMiddle.forward index)
    inverse := fun index =>
      leftMiddle.inverse (middleRight.inverse index)
    leftInverse := fun index => by
      change
        leftMiddle.inverse
            (middleRight.inverse
              (middleRight.forward (leftMiddle.forward index))) =
          index
      rw [middleRight.leftInverse, leftMiddle.leftInverse]
    rightInverse := fun index => by
      change
        middleRight.forward
            (leftMiddle.forward
              (leftMiddle.inverse (middleRight.inverse index))) =
          index
      rw [leftMiddle.rightInverse, middleRight.rightInverse] }

/-- The forward map of a finite bijection reflects index equality. -/
theorem FiniteBijection.forward_injective
    (bijection : FiniteBijection leftSize rightSize)
    {left right : Fin leftSize}
    (equal : bijection.forward left = bijection.forward right) :
    left = right := by
  have inverseEqual := congrArg bijection.inverse equal
  rw [bijection.leftInverse, bijection.leftInverse] at inverseEqual
  exact inverseEqual

/-- Enumerate the codomain values reached from the canonical finite range. -/
def FiniteBijection.forwardValues
    (bijection : FiniteBijection leftSize rightSize) :
    List Nat :=
  (range leftSize).attach.map fun index =>
    (bijection.forward
      ⟨index.val, by
        simpa [range] using index.property⟩).val

/-- A finite bijection can exist only between equal cardinalities. -/
theorem FiniteBijection.size_eq
    (bijection : FiniteBijection leftSize rightSize) :
    leftSize = rightSize := by
  have sourceNoDuplicates :
      NoDuplicates (range leftSize).attach :=
    attach_no_duplicates (range_no_duplicates leftSize)
  have mappedNoDuplicates :
      NoDuplicates bijection.forwardValues := by
    unfold FiniteBijection.forwardValues
    change
      List.Pairwise (fun left right : Nat => left ≠ right)
        ((range leftSize).attach.map fun index =>
          (bijection.forward
            ⟨index.val, by
              simpa [range] using index.property⟩).val)
    rw [List.pairwise_map]
    exact sourceNoDuplicates.imp (by
      intro left right different equal
      apply different
      apply Subtype.ext
      exact
        Fin.val_eq_of_eq
          (bijection.forward_injective (Fin.ext equal)))
  have mappedMembership :
      ∀ value,
        value ∈ bijection.forwardValues ↔
          value ∈ range rightSize := by
    intro value
    constructor
    · intro member
      rcases List.mem_map.mp member with
        ⟨source, _sourceMember, valueExact⟩
      rw [← valueExact]
      simp [range]
    · intro member
      have valueBound : value < rightSize := by
        simpa [range] using member
      let target : Fin rightSize := ⟨value, valueBound⟩
      let source : Fin leftSize := bijection.inverse target
      have sourceMember : source.val ∈ range leftSize := by
        simp [range, source.isLt]
      let attached : { index // index ∈ range leftSize } :=
        ⟨source.val, sourceMember⟩
      apply List.mem_map.mpr
      refine ⟨attached, by simp [attached], ?_⟩
      change (bijection.forward source).val = value
      rw [bijection.rightInverse]
  have valuesPermuted :
      IsPermutation bijection.forwardValues (range rightSize) :=
    no_duplicates_mem_iff_permutation
      mappedNoDuplicates
      (range_no_duplicates rightSize)
      mappedMembership
  have lengthsExact := valuesPermuted.length_eq
  simpa [FiniteBijection.forwardValues, range] using lengthsExact

/--
The forward image of the canonical finite-index enumeration is the canonical
enumeration of the codomain up to permutation.
-/
theorem finite_bijection_forward_indices_permutation
    (bijection : FiniteBijection leftSize rightSize) :
    IsPermutation
      ((finiteIndices leftSize).map bijection.forward)
      (finiteIndices rightSize) := by
  apply no_duplicates_mem_iff_permutation
  · change
      List.Pairwise (fun left right : Fin rightSize => left ≠ right)
        ((finiteIndices leftSize).map bijection.forward)
    rw [List.pairwise_map]
    exact
      (finite_indices_no_duplicates leftSize).imp_of_mem (by
        intro left right _leftMember _rightMember different equal
        exact different (bijection.forward_injective equal))
  · exact finite_indices_no_duplicates rightSize
  · intro value
    constructor
    · intro member
      rcases List.mem_map.mp member with
        ⟨source, _sourceMember, valueExact⟩
      subst value
      exact finite_indices_complete (bijection.forward source)
    · intro member
      apply List.mem_map.mpr
      exact
        ⟨bijection.inverse value,
          finite_indices_complete (bijection.inverse value),
          bijection.rightInverse value⟩

/-- Reading a list at its canonical finite-index enumeration reconstructs it. -/
theorem finite_indices_map_get (values : List α) :
    (finiteIndices values.length).map values.get = values := by
  apply List.ext_get
  · simp [finite_indices_length]
  · intro index leftBound rightBound
    have finiteBound :
        index < (finiteIndices values.length).length := by
      simpa using leftBound
    let indexFin : Fin values.length := ⟨index, rightBound⟩
    have indexExact :
        (finiteIndices values.length).get ⟨index, finiteBound⟩ =
          indexFin := by
      simpa [List.get_eq_getElem, indexFin] using
        finite_indices_get values.length indexFin
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_map]
    exact congrArg values.get indexExact

/--
A pointwise equality transported by a finite bijection yields a permutation of
the mapped source list and the target list.
-/
theorem list_map_permutation_of_finite_bijection_get
    {left : List α} {right : List β}
    (bijection : FiniteBijection left.length right.length)
    (mapValue : α → β)
    (valuesExact :
      ∀ index,
        mapValue (left.get index) =
          right.get (bijection.forward index)) :
    IsPermutation (left.map mapValue) right := by
  have indexPermutation :=
    finite_bijection_forward_indices_permutation bijection
  have mappedPermutation :=
    indexPermutation.map right.get
  have leftExact :
      ((finiteIndices left.length).map bijection.forward).map right.get =
        left.map mapValue := by
    rw [List.map_map]
    calc
      (finiteIndices left.length).map
          (fun index => right.get (bijection.forward index)) =
          (finiteIndices left.length).map
            (fun index => mapValue (left.get index)) := by
        apply List.map_congr_left
        intro index _indexMember
        exact (valuesExact index).symm
      _ = ((finiteIndices left.length).map left.get).map mapValue := by
        simp [List.map_map, Function.comp_def]
      _ = left.map mapValue := by
        rw [finite_indices_map_get]
  have rightExact :
      (finiteIndices right.length).map right.get = right :=
    finite_indices_map_get right
  exact
    (List.Perm.of_eq leftExact.symm).trans
      (mappedPermutation.trans (List.Perm.of_eq rightExact))

/--
If a finite transport preserves numeric positions, its pointwise transported
values reconstruct the target list in literal order.
-/
theorem list_map_eq_of_finite_bijection_position_exact
    {left : List α} {right : List β}
    (bijection : FiniteBijection left.length right.length)
    (mapValue : α → β)
    (positionExact :
      ∀ index, (bijection.forward index).val = index.val)
    (valuesExact :
      ∀ index,
        mapValue (left.get index) =
          right.get (bijection.forward index)) :
    left.map mapValue = right := by
  apply List.ext_get
  · simp [bijection.size_eq]
  · intro index leftBound rightBound
    have sourceBound : index < left.length := by
      simpa using leftBound
    let sourceIndex : Fin left.length := ⟨index, sourceBound⟩
    have targetIndexExact :
        bijection.forward sourceIndex = ⟨index, rightBound⟩ := by
      apply Fin.ext
      exact positionExact sourceIndex
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_map]
    simpa [sourceIndex, targetIndexExact] using
      valuesExact sourceIndex

/-- Reindex an equal-cardinality graph transport as a local permutation. -/
def FiniteBijection.toLocalBijection
    (bijection : FiniteBijection leftSize rightSize) :
    LocalBijection leftSize := by
  have sizeExact := bijection.size_eq
  subst rightSize
  exact
    { forward := bijection.forward
      inverse := bijection.inverse
      leftInverse := bijection.leftInverse
      rightInverse := bijection.rightInverse }

theorem FiniteBijection.toLocalBijection_forward_val
    (bijection : FiniteBijection leftSize rightSize)
    (index : Fin leftSize) :
    (bijection.toLocalBijection.forward index).val =
      (bijection.forward index).val := by
  have sizeExact := bijection.size_eq
  subst rightSize
  rfl

/--
The local view of the reversed finite transport is the cardinality-cast
inverse of the original local view.
-/
theorem FiniteBijection.symm_toLocalBijection_exact
    (bijection : FiniteBijection leftSize rightSize) :
    bijection.symm.toLocalBijection =
      transportLocalBijection bijection.size_eq
        (inverseLocalBijection bijection.toLocalBijection) := by
  have sizeExact := bijection.size_eq
  subst rightSize
  apply local_bijection_ext
  intro index
  rfl

structure RegistryNodeTransport
    (left right : ClosedRootedGraph context) where
  blockBijection :
    FiniteBijection left.canonicalRegistry.length
      right.canonicalRegistry.length
  blockKindPreserved :
    ∀ leftIndex,
      (left.canonicalRegistry.get leftIndex).kind =
        (right.canonicalRegistry.get
          (blockBijection.forward leftIndex)).kind
  nodeBijection :
    ∀ leftIndex,
      FiniteBijection
        (left.canonicalRegistry.get leftIndex).block.nodes.length
        (right.canonicalRegistry.get
          (blockBijection.forward leftIndex)).block.nodes.length

def RegistryNodeTransport.refl
    (graph : ClosedRootedGraph context) :
    RegistryNodeTransport graph graph :=
  { blockBijection :=
      FiniteBijection.refl graph.canonicalRegistry.length
    blockKindPreserved := fun _ => rfl
    nodeBijection := fun index =>
      FiniteBijection.refl
        (graph.canonicalRegistry.get index).block.nodes.length }

def PublicReferenceOccurrence.sourceBlockFin
    (occurrence : PublicReferenceOccurrence registry) :
    Fin registry.length :=
  ⟨occurrence.sourceBlockIndex, occurrence.sourceBlockBound⟩

theorem PublicReferenceOccurrence.source_block_get_exact
    (occurrence : PublicReferenceOccurrence registry) :
    registry.get occurrence.sourceBlockFin =
      occurrence.sourceBlock :=
  Option.some.inj
    ((list_get?_eq_get registry occurrence.sourceBlockFin).symm.trans
      occurrence.sourceBlockLookup)

def PublicReferenceOccurrence.sourceNodeFin
    (occurrence : PublicReferenceOccurrence registry) :
    Fin
      (registry.get occurrence.sourceBlockFin).block.nodes.length :=
  ⟨occurrence.sourceNodeIndex, by
    rw [occurrence.source_block_get_exact]
    exact occurrence.sourceNodeBound⟩

def ResolvedPublicReference.targetBlockFin
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {occurrence : PublicReferenceOccurrence registry}
    (resolved : ResolvedPublicReference occurrence) :
    Fin registry.length :=
  ⟨resolved.targetBlockIndex, resolved.targetBlockBound⟩

theorem ResolvedPublicReference.target_block_get_exact
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {occurrence : PublicReferenceOccurrence registry}
    (resolved : ResolvedPublicReference occurrence) :
    registry.get resolved.targetBlockFin =
      resolved.targetBlock :=
  Option.some.inj
    ((list_get?_eq_get registry resolved.targetBlockFin).symm.trans
      resolved.targetLookup)

def ResolvedPublicReference.targetNodeFin
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {occurrence : PublicReferenceOccurrence registry}
    (resolved : ResolvedPublicReference occurrence) :
    Fin
      (registry.get resolved.targetBlockFin).block.nodes.length :=
  ⟨resolved.targetNodeIndex.val, by
    rw [resolved.target_block_get_exact]
    exact resolved.targetNodeIndex.isLt⟩

inductive PublicReferenceOccurrenceIsomorphic
    (transport : RegistryNodeTransport left right)
    (leftOccurrence :
      PublicReferenceOccurrence left.canonicalRegistry)
    (rightOccurrence :
      PublicReferenceOccurrence right.canonicalRegistry) : Prop
  | intro
      (sourceBlockTransport :
        rightOccurrence.sourceBlockIndex =
          (transport.blockBijection.forward
            leftOccurrence.sourceBlockFin).val)
      (sourceNodeTransport :
        rightOccurrence.sourceNodeIndex =
          ((transport.nodeBijection
            leftOccurrence.sourceBlockFin).forward
            leftOccurrence.sourceNodeFin).val)
      (expectedTargetKindPreserved :
        HEq leftOccurrence.expectedTargetKind
          rightOccurrence.expectedTargetKind)
      (leftResolved : ResolvedPublicReference leftOccurrence)
      (rightResolved : ResolvedPublicReference rightOccurrence)
      (leftResolutionExact :
        resolvePublicReferenceOccurrence
          left.registryKeysNoDup leftOccurrence = .ok leftResolved)
      (rightResolutionExact :
        resolvePublicReferenceOccurrence
          right.registryKeysNoDup rightOccurrence = .ok rightResolved)
      (targetBlockTransport :
        rightResolved.targetBlockIndex =
          (transport.blockBijection.forward
            leftResolved.targetBlockFin).val)
      (targetNodeTransport :
        rightResolved.targetNodeIndex.val =
          ((transport.nodeBijection
            leftResolved.targetBlockFin).forward
            leftResolved.targetNodeFin).val)

theorem PublicReferenceOccurrenceIsomorphic.refl
    (graph : ClosedRootedGraph context)
    (occurrence :
      PublicReferenceOccurrence graph.canonicalRegistry) :
    PublicReferenceOccurrenceIsomorphic
      (RegistryNodeTransport.refl graph) occurrence occurrence := by
  rcases graph.resolvedEdges.complete occurrence with
    ⟨edge, edgeMember, edgeOccurrenceExact⟩
  cases edgeOccurrenceExact
  exact
    .intro rfl rfl (HEq.rfl)
      edge.resolved edge.resolved
      (graph.resolvedEdges.sound edge edgeMember)
      (graph.resolvedEdges.sound edge edgeMember)
      rfl rfl

/--
Forward node transports preserve values across propositionally equal source
indices.
-/
theorem RegistryNodeTransport.forward_node_val_congr
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    {firstBlockIndex secondBlockIndex :
      Fin left.canonicalRegistry.length}
    (blockIndexExact : firstBlockIndex = secondBlockIndex)
    (firstNodeIndex :
      Fin
        (left.canonicalRegistry.get
          firstBlockIndex).block.nodes.length)
    (secondNodeIndex :
      Fin
        (left.canonicalRegistry.get
          secondBlockIndex).block.nodes.length)
    (nodeIndexValExact :
      firstNodeIndex.val = secondNodeIndex.val) :
    ((transport.nodeBijection firstBlockIndex).forward
        firstNodeIndex).val =
      ((transport.nodeBijection secondBlockIndex).forward
        secondNodeIndex).val := by
  cases blockIndexExact
  have nodeIndexExact : firstNodeIndex = secondNodeIndex :=
    Fin.ext nodeIndexValExact
  cases nodeIndexExact
  rfl

/-- Equal block kinds and bytes induce heterogeneous address equality. -/
theorem block_wire_address_heq_of_kind_bytes
    (context : GraphCodecContext)
    {leftKind rightKind : context.kindSchema.Kind}
    {leftBytes rightBytes : GraphBytes}
    (kindExact : leftKind = rightKind)
    (bytesExact : leftBytes = rightBytes) :
    HEq
      (context.blockWireAddress leftKind leftBytes)
      (context.blockWireAddress rightKind rightBytes) := by
  subst rightKind
  subst rightBytes
  rfl

/--
Transported block bytes induce heterogeneous equality of their stored typed
block addresses.
-/
theorem transported_registry_block_address_heq_of_bytes
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftIndex : Fin left.canonicalRegistry.length)
    (blockBytesExact :
      encodeCanonicalBlock
          (left.canonicalRegistry.get leftIndex).block =
        encodeCanonicalBlock
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftIndex)).block) :
    HEq
      (left.canonicalRegistry.get leftIndex).blockQ
      (right.canonicalRegistry.get
        (transport.blockBijection.forward leftIndex)).blockQ := by
  have leftDerived :=
    left.blockAddressesDerived
      (left.canonicalRegistry.get leftIndex)
      (list_get_mem_fin left.canonicalRegistry leftIndex)
  have rightDerived :=
    right.blockAddressesDerived
      (right.canonicalRegistry.get
        (transport.blockBijection.forward leftIndex))
      (list_get_mem_fin right.canonicalRegistry
        (transport.blockBijection.forward leftIndex))
  have kindExact :=
    transport.blockKindPreserved leftIndex
  have derivedAddressesExact :
      HEq
        (context.blockWireAddress
          (left.canonicalRegistry.get leftIndex).kind
          (encodeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block))
        (context.blockWireAddress
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftIndex)).kind
          (encodeCanonicalBlock
            (right.canonicalRegistry.get
              (transport.blockBijection.forward leftIndex)).block)) := by
    exact
      block_wire_address_heq_of_kind_bytes
        context kindExact blockBytesExact
  exact
    (heq_of_eq leftDerived).trans
      (derivedAddressesExact.trans
        (heq_of_eq rightDerived.symm))

inductive TargetAtTransport
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length)
    (leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema))
    (leftPosition : Fin leftCollection.targets.length)
    (rightPosition : Fin rightCollection.targets.length) : Type
  | local
      (leftLocal rightLocal : Nat)
      (leftExact :
        leftCollection.targets.get leftPosition = .local leftLocal)
      (rightExact :
        rightCollection.targets.get rightPosition = .local rightLocal)
      (leftBound :
        leftLocal <
          (left.canonicalRegistry.get leftBlockIndex).block.nodes.length)
      (rightBound :
        rightLocal <
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftBlockIndex)).block.nodes.length)
      (indexTransport :
        (transport.nodeBijection leftBlockIndex).forward
            ⟨leftLocal, leftBound⟩ =
          ⟨rightLocal, rightBound⟩)
  | external
      (leftRef rightRef : ExternalRef context.kindSchema)
      (leftSlotExact :
        leftCollection.targets.get leftPosition = .external leftRef)
      (rightSlotExact :
        rightCollection.targets.get rightPosition = .external rightRef)
      (leftOccurrence :
        PublicReferenceOccurrence left.canonicalRegistry)
      (rightOccurrence :
        PublicReferenceOccurrence right.canonicalRegistry)
      (leftSourceBlockExact :
        leftOccurrence.sourceBlockIndex = leftBlockIndex.val)
      (rightSourceBlockExact :
        rightOccurrence.sourceBlockIndex =
          (transport.blockBijection.forward leftBlockIndex).val)
      (leftSourceNodeExact :
        leftOccurrence.sourceNodeIndex = leftNodeIndex.val)
      (rightSourceNodeExact :
        rightOccurrence.sourceNodeIndex =
          ((transport.nodeBijection leftBlockIndex).forward
            leftNodeIndex).val)
      (leftOwningCollectionExact :
        leftOccurrence.owningCollection = leftCollection)
      (rightOwningCollectionExact :
        rightOccurrence.owningCollection = rightCollection)
      (leftPositionExact :
        leftOccurrence.targetPosition = leftPosition.val)
      (rightPositionExact :
        rightOccurrence.targetPosition = rightPosition.val)
      (leftExpectedKindExact :
        leftOccurrence.expectedTargetKind =
          leftCollection.expectedTargetKind)
      (rightExpectedKindExact :
        rightOccurrence.expectedTargetKind =
          rightCollection.expectedTargetKind)
      (leftRefExact : leftOccurrence.ref = leftRef)
      (rightRefExact : rightOccurrence.ref = rightRef)
      (occurrenceTransport :
        PublicReferenceOccurrenceIsomorphic
          transport leftOccurrence rightOccurrence)

theorem target_at_transport_external_anchored
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    {leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)}
    {leftPosition : Fin leftCollection.targets.length}
    {rightPosition : Fin rightCollection.targets.length} :
  ∀ (_witness :
      TargetAtTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection leftPosition rightPosition)
    {leftRef rightRef},
    leftCollection.targets.get leftPosition = .external leftRef →
    rightCollection.targets.get rightPosition = .external rightRef →
    ∃ leftOccurrence rightOccurrence,
      leftOccurrence.sourceBlockIndex = leftBlockIndex.val ∧
      rightOccurrence.sourceBlockIndex =
        (transport.blockBijection.forward leftBlockIndex).val ∧
      leftOccurrence.sourceNodeIndex = leftNodeIndex.val ∧
      rightOccurrence.sourceNodeIndex =
        ((transport.nodeBijection leftBlockIndex).forward
          leftNodeIndex).val ∧
      leftOccurrence.owningCollection = leftCollection ∧
      rightOccurrence.owningCollection = rightCollection ∧
      leftOccurrence.targetPosition = leftPosition.val ∧
      rightOccurrence.targetPosition = rightPosition.val ∧
      leftOccurrence.expectedTargetKind =
        leftCollection.expectedTargetKind ∧
      rightOccurrence.expectedTargetKind =
        rightCollection.expectedTargetKind ∧
      leftOccurrence.ref = leftRef ∧ rightOccurrence.ref = rightRef ∧
      PublicReferenceOccurrenceIsomorphic
        transport leftOccurrence rightOccurrence := by
  intro witness leftRef rightRef leftSlot rightSlot
  cases witness with
  | «local» leftLocal rightLocal leftExact _ _ _ _ =>
      have impossible := leftExact.symm.trans leftSlot
      cases impossible
  | external storedLeftRef storedRightRef
      storedLeftSlot storedRightSlot
      leftOccurrence rightOccurrence
      leftSourceBlockExact rightSourceBlockExact
      leftSourceNodeExact rightSourceNodeExact
      leftOwningCollectionExact rightOwningCollectionExact
      leftPositionExact rightPositionExact
      leftExpectedKindExact rightExpectedKindExact
      leftRefExact rightRefExact occurrenceTransport =>
      have leftRefStoredExact : storedLeftRef = leftRef := by
        have slotsExact := storedLeftSlot.symm.trans leftSlot
        cases slotsExact
        rfl
      have rightRefStoredExact : storedRightRef = rightRef := by
        have slotsExact := storedRightSlot.symm.trans rightSlot
        cases slotsExact
        rfl
      exact
        ⟨leftOccurrence, rightOccurrence,
          leftSourceBlockExact, rightSourceBlockExact,
          leftSourceNodeExact, rightSourceNodeExact,
          leftOwningCollectionExact, rightOwningCollectionExact,
          leftPositionExact, rightPositionExact,
          leftExpectedKindExact, rightExpectedKindExact,
          leftRefExact.trans leftRefStoredExact,
          rightRefExact.trans rightRefStoredExact,
          occurrenceTransport⟩

def TargetAtTransport.refl
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin
        (graph.canonicalRegistry.get blockIndex).block.nodes.length)
    (collectionIndex :
      Fin
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length))
    (targetPosition :
      Fin
        ((((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex).targets.length)) :
    TargetAtTransport
      (RegistryNodeTransport.refl graph)
      blockIndex nodeIndex
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex)
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex)
      targetPosition targetPosition := by
  let block := (graph.canonicalRegistry.get blockIndex).block
  let node := block.nodes.get nodeIndex
  let collection := node.edgeCollections.get collectionIndex
  cases targetExact : collection.targets.get targetPosition with
  | «local» localIndex =>
      let occurrence : LocalReferenceOccurrence block.nodes :=
        { sourceNodeIndex := nodeIndex.val
          sourceNode := node
          sourceNodeLookup :=
            list_get?_eq_get block.nodes nodeIndex
          owningCollectionIndex := collectionIndex.val
          owningCollection := collection
          owningCollectionLookup :=
            list_get?_eq_get node.edgeCollections collectionIndex
          targetPosition := targetPosition.val
          localIndex := localIndex
          targetExact :=
            (list_get?_eq_get collection.targets targetPosition).trans
              (congrArg some targetExact) }
      have localBound : localIndex < block.nodes.length :=
        (graph.registryWellFormed.blocks blockIndex).localReferencesBound
          occurrence
      exact
        .local localIndex localIndex targetExact targetExact
          localBound localBound rfl
  | external ref =>
      let occurrence :
          PublicReferenceOccurrence graph.canonicalRegistry :=
        { sourceBlockIndex := blockIndex.val
          sourceBlockBound := blockIndex.isLt
          sourceBlock := graph.canonicalRegistry.get blockIndex
          sourceBlockLookup :=
            list_get?_eq_get graph.canonicalRegistry blockIndex
          sourceNodeIndex := nodeIndex.val
          sourceNodeBound := nodeIndex.isLt
          sourceNode := node
          sourceNodeLookup :=
            list_get?_eq_get block.nodes nodeIndex
          owningCollectionIndex := collectionIndex.val
          owningCollection := collection
          owningCollectionLookup :=
            list_get?_eq_get node.edgeCollections collectionIndex
          expectedTargetKind := collection.expectedTargetKind
          expectedTargetKindExact := rfl
          ref := ref
          targetPosition := targetPosition.val
          targetOccurrence :=
            (list_get?_eq_get collection.targets targetPosition).trans
              (congrArg some targetExact) }
      exact
        .external ref ref targetExact targetExact
          occurrence occurrence rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
          rfl rfl
          (PublicReferenceOccurrenceIsomorphic.refl graph occurrence)

inductive TargetPositionMap
    {context : GraphCodecContext}
    (leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema))
    (bijection :
      FiniteBijection
        leftCollection.targets.length
        rightCollection.targets.length) : Prop
  | ordered
      (leftMode : leftCollection.mode = .ordered)
      (rightMode : rightCollection.mode = .ordered)
      (positionExact :
        ∀ index, (bijection.forward index).val = index.val)
  | unordered
      (leftMode : leftCollection.mode = .unordered)
      (rightMode : rightCollection.mode = .unordered)

structure EdgeCollectionTransport
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length)
    (leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)) where
  labelExact : leftCollection.labelText = rightCollection.labelText
  directionExact :
    leftCollection.direction = rightCollection.direction
  expectedKindExact :
    leftCollection.expectedTargetKind =
      rightCollection.expectedTargetKind
  targetBijection :
    FiniteBijection
      leftCollection.targets.length rightCollection.targets.length
  positionMap :
    TargetPositionMap leftCollection rightCollection targetBijection
  targets :
    ∀ leftPosition,
      TargetAtTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection leftPosition
        (targetBijection.forward leftPosition)

def EdgeCollectionTransport.refl
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin
        (graph.canonicalRegistry.get blockIndex).block.nodes.length)
    (collectionIndex :
      Fin
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length)) :
    EdgeCollectionTransport
      (RegistryNodeTransport.refl graph)
      blockIndex nodeIndex
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex)
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex) := by
  let collection :=
    ((graph.canonicalRegistry.get blockIndex).block.nodes.get
      nodeIndex).edgeCollections.get collectionIndex
  let targetBijection :=
    FiniteBijection.refl collection.targets.length
  refine
    { labelExact := rfl
      directionExact := rfl
      expectedKindExact := rfl
      targetBijection := targetBijection
      positionMap := ?_
      targets := ?_ }
  · cases modeExact : collection.mode with
    | ordered =>
        exact .ordered modeExact modeExact (fun _ => rfl)
    | unordered =>
        exact .unordered modeExact modeExact
  · intro targetPosition
    exact
      TargetAtTransport.refl
        graph blockIndex nodeIndex collectionIndex targetPosition

structure NodeTransport
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length)
    where
  payloadExact :
    ((left.canonicalRegistry.get leftBlockIndex).block.nodes.get
      leftNodeIndex).payload =
    ((right.canonicalRegistry.get
      (transport.blockBijection.forward leftBlockIndex)).block.nodes.get
      ((transport.nodeBijection leftBlockIndex).forward leftNodeIndex)).payload
  collectionBijection :
    FiniteBijection
      ((left.canonicalRegistry.get leftBlockIndex).block.nodes.get
        leftNodeIndex).edgeCollections.length
      ((right.canonicalRegistry.get
        (transport.blockBijection.forward leftBlockIndex)).block.nodes.get
        ((transport.nodeBijection leftBlockIndex).forward
          leftNodeIndex)).edgeCollections.length
  collections :
    ∀ leftCollectionIndex,
      EdgeCollectionTransport transport leftBlockIndex leftNodeIndex
        (((left.canonicalRegistry.get leftBlockIndex).block.nodes.get
          leftNodeIndex).edgeCollections.get leftCollectionIndex)
        (((right.canonicalRegistry.get
          (transport.blockBijection.forward leftBlockIndex)).block.nodes.get
          ((transport.nodeBijection leftBlockIndex).forward
            leftNodeIndex)).edgeCollections.get
              (collectionBijection.forward leftCollectionIndex))

def NodeTransport.refl
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin
        (graph.canonicalRegistry.get blockIndex).block.nodes.length) :
    NodeTransport
      (RegistryNodeTransport.refl graph) blockIndex nodeIndex :=
  { payloadExact := rfl
    collectionBijection :=
      FiniteBijection.refl
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length)
    collections := fun collectionIndex =>
      EdgeCollectionTransport.refl
        graph blockIndex nodeIndex collectionIndex }

structure BlockIsomorphic
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftIndex : Fin left.canonicalRegistry.length) where
  formExact :
    (left.canonicalRegistry.get leftIndex).block.form =
      (right.canonicalRegistry.get
        (transport.blockBijection.forward leftIndex)).block.form
  nodes :
    ∀ leftNodeIndex,
      NodeTransport transport leftIndex leftNodeIndex

def BlockIsomorphic.refl
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length) :
    BlockIsomorphic
      (RegistryNodeTransport.refl graph) blockIndex :=
  { formExact := rfl
    nodes := fun nodeIndex =>
      NodeTransport.refl graph blockIndex nodeIndex }

structure RootTransport
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right) : Prop where
  blockIndexExact :
    right.canonicalRoot.blockIndex =
      (transport.blockBijection.forward
        ⟨left.canonicalRoot.blockIndex,
          left.canonicalRoot.blockBound⟩).val
  localIndexExact :
    right.canonicalRoot.localIndex =
      ((transport.nodeBijection
        ⟨left.canonicalRoot.blockIndex,
          left.canonicalRoot.blockBound⟩).forward
        ⟨left.canonicalRoot.localIndex,
          left.canonicalRoot.localBound⟩).val

def RootTransport.refl
    (graph : ClosedRootedGraph context) :
    RootTransport (RegistryNodeTransport.refl graph) :=
  { blockIndexExact := rfl
    localIndexExact := rfl }

structure GraphIsomorphism
    {context : GraphCodecContext}
    (left right : ClosedRootedGraph context) where
  transport : RegistryNodeTransport left right
  blocks : ∀ leftIndex, BlockIsomorphic transport leftIndex
  root : RootTransport transport

/--
Graph isomorphism is propositionally witnessed by one concrete finite
transport.  The witness remains data, while the relation consumed by quotient
adequacy is proof-irrelevant.
-/
def GraphIsomorphic
    {context : GraphCodecContext}
    (left right : ClosedRootedGraph context) : Prop :=
  Nonempty (GraphIsomorphism left right)

def GraphIsomorphism.refl
    (graph : ClosedRootedGraph context) :
    GraphIsomorphism graph graph :=
  { transport := RegistryNodeTransport.refl graph
    blocks := fun blockIndex =>
      BlockIsomorphic.refl graph blockIndex
    root := RootTransport.refl graph }

theorem GraphIsomorphic.refl
    (graph : ClosedRootedGraph context) :
    GraphIsomorphic graph graph :=
  ⟨GraphIsomorphism.refl graph⟩

/--
Equality of serialized canonical projections constructively realizes the
identity graph transport and therefore graph isomorphism.
-/
theorem canonical_projection_eq_implies_graph_isomorphic
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (exact :
      serializedCanonicalProjection left =
        serializedCanonicalProjection right) :
    GraphIsomorphic left right := by
  cases left with
  | mk leftRegistry leftRoot leftSorted leftKeys leftWellFormed
      leftConnectivity leftEdges leftDependency leftAddresses leftMinima =>
      cases right with
      | mk rightRegistry rightRoot rightSorted rightKeys rightWellFormed
          rightConnectivity rightEdges rightDependency rightAddresses
          rightMinima =>
          simp [serializedCanonicalProjection] at exact
          rcases exact with ⟨rfl, rootBlockExact, rootLocalExact⟩
          cases leftRoot with
          | mk leftBlock leftBlockBound leftLocal leftLocalBound =>
              cases rightRoot with
              | mk rightBlock rightBlockBound rightLocal rightLocalBound =>
                  simp only at rootBlockExact rootLocalExact
                  cases rootBlockExact
                  cases rootLocalExact
                  have blockBoundExact :
                      leftBlockBound = rightBlockBound :=
                    Subsingleton.elim _ _
                  cases blockBoundExact
                  have localBoundExact :
                      leftLocalBound = rightLocalBound :=
                    Subsingleton.elim _ _
                  cases localBoundExact
                  have keysExact : leftKeys = rightKeys :=
                    Subsingleton.elim _ _
                  cases keysExact
                  refine ⟨{ transport := ?_, blocks := ?_, root := ?_ }⟩
                  · exact
                      { blockBijection :=
                          FiniteBijection.refl leftRegistry.length
                        blockKindPreserved := fun _ => rfl
                        nodeBijection := fun index =>
                          FiniteBijection.refl
                            (leftRegistry.get index).block.nodes.length }
                  · intro index
                    refine { formExact := rfl, nodes := ?_ }
                    intro nodeIndex
                    refine
                      { payloadExact := rfl
                        collectionBijection :=
                          FiniteBijection.refl
                            ((leftRegistry.get index).block.nodes.get
                              nodeIndex).edgeCollections.length
                        collections := ?_ }
                    intro collectionIndex
                    let collection :=
                      ((leftRegistry.get index).block.nodes.get
                        nodeIndex).edgeCollections.get collectionIndex
                    refine
                      { labelExact := rfl
                        directionExact := rfl
                        expectedKindExact := rfl
                        targetBijection :=
                          FiniteBijection.refl collection.targets.length
                        positionMap := ?_
                        targets := ?_ }
                    · cases modeExact : collection.mode with
                      | ordered =>
                          exact .ordered modeExact modeExact (fun _ => rfl)
                      | unordered =>
                          exact .unordered modeExact modeExact
                    · intro targetPosition
                      let block := (leftRegistry.get index).block
                      let node := block.nodes.get nodeIndex
                      cases targetExact :
                          collection.targets.get targetPosition with
                      | «local» localIndex =>
                          let occurrence :
                              LocalReferenceOccurrence block.nodes :=
                            { sourceNodeIndex := nodeIndex.val
                              sourceNode := node
                              sourceNodeLookup :=
                                list_get?_eq_get block.nodes nodeIndex
                              owningCollectionIndex :=
                                collectionIndex.val
                              owningCollection := collection
                              owningCollectionLookup :=
                                list_get?_eq_get
                                  node.edgeCollections collectionIndex
                              targetPosition := targetPosition.val
                              localIndex := localIndex
                              targetExact :=
                                (list_get?_eq_get
                                  collection.targets
                                  targetPosition).trans
                                  (congrArg some targetExact) }
                          have localBound :
                              localIndex < block.nodes.length :=
                            (leftWellFormed.blocks index)
                              |>.localReferencesBound occurrence
                          exact
                            .local localIndex localIndex
                              targetExact targetExact
                              localBound localBound rfl
                      | external ref =>
                          let occurrence :
                              PublicReferenceOccurrence leftRegistry :=
                            { sourceBlockIndex := index.val
                              sourceBlockBound := index.isLt
                              sourceBlock := leftRegistry.get index
                              sourceBlockLookup :=
                                list_get?_eq_get leftRegistry index
                              sourceNodeIndex := nodeIndex.val
                              sourceNodeBound := nodeIndex.isLt
                              sourceNode := node
                              sourceNodeLookup :=
                                list_get?_eq_get block.nodes nodeIndex
                              owningCollectionIndex :=
                                collectionIndex.val
                              owningCollection := collection
                              owningCollectionLookup :=
                                list_get?_eq_get
                                  node.edgeCollections collectionIndex
                              expectedTargetKind :=
                                collection.expectedTargetKind
                              expectedTargetKindExact := rfl
                              ref := ref
                              targetPosition := targetPosition.val
                              targetOccurrence :=
                                (list_get?_eq_get
                                  collection.targets
                                  targetPosition).trans
                                  (congrArg some targetExact) }
                          let edge :=
                            leftEdges.edgeForOccurrence occurrence
                          have edgeMember :
                              edge ∈ leftEdges.edges :=
                            leftEdges.edge_for_occurrence_member occurrence
                          have edgeOccurrenceExact :
                              edge.occurrence = occurrence :=
                            leftEdges.edge_for_occurrence_exact occurrence
                          let occurrenceResolved :=
                            edge.resolved.transportOccurrence
                              edgeOccurrenceExact
                          have edgeResolutionExact :
                              resolvePublicReferenceOccurrence
                                  leftKeys occurrence =
                                .ok occurrenceResolved :=
                            resolve_public_reference_occurrence_transport
                              edgeOccurrenceExact edge.resolved
                              (leftEdges.sound edge edgeMember)
                          exact
                            .external ref ref targetExact targetExact
                              occurrence occurrence
                              rfl rfl rfl rfl rfl rfl rfl rfl
                              rfl rfl rfl rfl
                              (.intro rfl rfl (HEq.rfl)
                                occurrenceResolved occurrenceResolved
                                edgeResolutionExact edgeResolutionExact
                                rfl rfl)
                  · exact { blockIndexExact := rfl, localIndexExact := rfl }

/--
Constructive data extracted from the exact target-slot transport carrying one
resolved external edge.
-/
structure ExternalSlotTransportData
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup) where
  leftOccurrence :
    PublicReferenceOccurrence left.canonicalRegistry
  rightOccurrence :
    PublicReferenceOccurrence right.canonicalRegistry
  leftRefExact : leftOccurrence.ref = leftEdge.occurrence.ref
  leftExpectedKindExact :
    leftOccurrence.expectedTargetKind =
      leftEdge.occurrence.expectedTargetKind
  leftSourceBlockExact :
    leftOccurrence.sourceBlockIndex =
      leftEdge.occurrence.sourceBlockIndex
  leftSourceNodeExact :
    leftOccurrence.sourceNodeIndex =
      leftEdge.occurrence.sourceNodeIndex
  occurrenceTransport :
    PublicReferenceOccurrenceIsomorphic
      transport leftOccurrence rightOccurrence

/--
Extract the transported external occurrence from the isomorphism's exact
block/node/collection/target path.
-/
def GraphIsomorphism.externalSlotTransportData
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
    (_leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val) :
    ExternalSlotTransportData
      isomorphism.transport leftEdge := by
  let leftNodeIndex :
      Fin
        (left.canonicalRegistry.get
          leftSourceIndex).block.nodes.length :=
    ⟨leftEdge.occurrence.sourceNodeIndex, by
      have sourceBlockFinExact :
          leftEdge.occurrence.sourceBlockFin = leftSourceIndex := by
        apply Fin.ext
        exact sourceExact
      rw [← sourceBlockFinExact]
      exact leftEdge.occurrence.sourceNodeFin.isLt⟩
  have sourceBlockExact :
      left.canonicalRegistry.get leftSourceIndex =
        leftEdge.occurrence.sourceBlock := by
    have sourceBlockFinExact :
        leftEdge.occurrence.sourceBlockFin = leftSourceIndex := by
      apply Fin.ext
      exact sourceExact
    rw [← sourceBlockFinExact]
    exact leftEdge.occurrence.source_block_get_exact
  have sourceNodeLookup :
      listGet?
          (left.canonicalRegistry.get
            leftSourceIndex).block.nodes
          leftEdge.occurrence.sourceNodeIndex =
        some leftEdge.occurrence.sourceNode := by
    rw [sourceBlockExact]
    exact leftEdge.occurrence.sourceNodeLookup
  have sourceNodeExact :
      (left.canonicalRegistry.get
        leftSourceIndex).block.nodes.get leftNodeIndex =
        leftEdge.occurrence.sourceNode :=
    Option.some.inj
      ((list_get?_eq_get
        (left.canonicalRegistry.get
          leftSourceIndex).block.nodes leftNodeIndex).symm.trans
        sourceNodeLookup)
  have owningCollectionLookup :
      listGet?
          ((left.canonicalRegistry.get
            leftSourceIndex).block.nodes.get
            leftNodeIndex).edgeCollections
          leftEdge.occurrence.owningCollectionIndex =
        some leftEdge.occurrence.owningCollection := by
    rw [sourceNodeExact]
    exact leftEdge.occurrence.owningCollectionLookup
  let leftCollectionIndex :
      Fin
        (((left.canonicalRegistry.get
          leftSourceIndex).block.nodes.get
          leftNodeIndex).edgeCollections.length) :=
    ⟨leftEdge.occurrence.owningCollectionIndex,
      list_get?_some_bound owningCollectionLookup⟩
  have owningCollectionExact :
      ((left.canonicalRegistry.get
        leftSourceIndex).block.nodes.get
        leftNodeIndex).edgeCollections.get leftCollectionIndex =
        leftEdge.occurrence.owningCollection :=
    Option.some.inj
      ((list_get?_eq_get
        ((left.canonicalRegistry.get
          leftSourceIndex).block.nodes.get
          leftNodeIndex).edgeCollections leftCollectionIndex).symm.trans
        owningCollectionLookup)
  have targetOccurrence :
      listGet?
          (((left.canonicalRegistry.get
            leftSourceIndex).block.nodes.get
            leftNodeIndex).edgeCollections.get
            leftCollectionIndex).targets
          leftEdge.occurrence.targetPosition =
        some (.external leftEdge.occurrence.ref) := by
    rw [owningCollectionExact]
    exact leftEdge.occurrence.targetOccurrence
  let leftPosition :
      Fin
        ((((left.canonicalRegistry.get
          leftSourceIndex).block.nodes.get
          leftNodeIndex).edgeCollections.get
          leftCollectionIndex).targets.length) :=
    ⟨leftEdge.occurrence.targetPosition,
      list_get?_some_bound targetOccurrence⟩
  have leftSlot :
      (((left.canonicalRegistry.get
        leftSourceIndex).block.nodes.get
        leftNodeIndex).edgeCollections.get
        leftCollectionIndex).targets.get leftPosition =
        .external leftEdge.occurrence.ref :=
    Option.some.inj
      ((list_get?_eq_get
        (((left.canonicalRegistry.get
          leftSourceIndex).block.nodes.get
          leftNodeIndex).edgeCollections.get
          leftCollectionIndex).targets leftPosition).symm.trans
        targetOccurrence)
  let nodeTransport :=
    (isomorphism.blocks leftSourceIndex).nodes leftNodeIndex
  let collectionTransport :=
    nodeTransport.collections leftCollectionIndex
  let targetTransport :=
    collectionTransport.targets leftPosition
  cases targetTransport with
  | «local» leftLocal rightLocal leftLocalExact
      _rightLocalExact _leftBound _rightBound _indexTransport =>
      have impossible := leftLocalExact.symm.trans leftSlot
      cases impossible
  | external leftRef rightRef leftSlotExact _rightSlotExact
      leftOccurrence rightOccurrence
      _leftSourceBlockExact _rightSourceBlockExact
      _leftSourceNodeExact _rightSourceNodeExact
      _leftOwningCollectionExact _rightOwningCollectionExact
      _leftPositionExact _rightPositionExact
      _leftExpectedKindExact _rightExpectedKindExact
      leftRefExact _rightRefExact occurrenceTransport =>
      have storedRefExact : leftRef = leftEdge.occurrence.ref := by
        have slotExact := leftSlotExact.symm.trans leftSlot
        cases slotExact
        rfl
      have expectedKindExact :
          leftOccurrence.expectedTargetKind =
            leftEdge.occurrence.expectedTargetKind := by
        calc
          leftOccurrence.expectedTargetKind =
              (((left.canonicalRegistry.get
                leftSourceIndex).block.nodes.get
                leftNodeIndex).edgeCollections.get
                leftCollectionIndex).expectedTargetKind :=
            _leftExpectedKindExact
          _ = leftEdge.occurrence.owningCollection.expectedTargetKind := by
            rw [owningCollectionExact]
          _ = leftEdge.occurrence.expectedTargetKind :=
            leftEdge.occurrence.expectedTargetKindExact
      exact
        { leftOccurrence
          rightOccurrence
          leftRefExact := leftRefExact.trans storedRefExact
          leftExpectedKindExact := expectedKindExact
          leftSourceBlockExact :=
            _leftSourceBlockExact.trans sourceExact.symm
          leftSourceNodeExact := _leftSourceNodeExact
          occurrenceTransport }

/--
Re-anchor the carried external occurrence to the actual resolved edge.  The
resolution result depends only on expected kind and external reference, not
the occurrence's owning collection metadata.
-/
theorem ExternalSlotTransportData.reanchored
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup}
    (leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (data :
      ExternalSlotTransportData transport leftEdge) :
    PublicReferenceOccurrenceIsomorphic
      transport leftEdge.occurrence data.rightOccurrence := by
  rcases data with
    ⟨carriedLeftOccurrence, rightOccurrence,
      carriedRefExact, carriedExpectedKindExact,
      carriedSourceBlockExact, carriedSourceNodeExact,
      carriedTransport⟩
  cases carriedTransport with
  | intro sourceBlockTransport sourceNodeTransport
      expectedTargetKindPreserved
      carriedLeftResolved rightResolved
      carriedLeftResolutionExact rightResolutionExact
      targetBlockTransport targetNodeTransport =>
      have leftResolutionExact :
          resolvePublicReferenceOccurrence
              left.registryKeysNoDup leftEdge.occurrence =
            .ok leftEdge.resolved :=
        left.resolvedEdges.sound leftEdge leftEdgeMember
      have coordinatesExact :=
        resolved_coordinates_congr
          left.registryKeysNoDup
          leftEdge.resolved carriedLeftResolved
          leftResolutionExact carriedLeftResolutionExact
          carriedExpectedKindExact.symm carriedRefExact.symm
      have sourceBlockFinExact :
          carriedLeftOccurrence.sourceBlockFin =
            leftEdge.occurrence.sourceBlockFin := by
        apply Fin.ext
        exact carriedSourceBlockExact
      have sourceBlockTransportExact :
          rightOccurrence.sourceBlockIndex =
            (transport.blockBijection.forward
              leftEdge.occurrence.sourceBlockFin).val := by
        exact
          sourceBlockTransport.trans
            (congrArg
              (fun index =>
                (transport.blockBijection.forward index).val)
              sourceBlockFinExact)
      have sourceNodeTransportExact :
          rightOccurrence.sourceNodeIndex =
            ((transport.nodeBijection
              leftEdge.occurrence.sourceBlockFin).forward
              leftEdge.occurrence.sourceNodeFin).val := by
        exact
          sourceNodeTransport.trans
            (transport.forward_node_val_congr
              sourceBlockFinExact
              carriedLeftOccurrence.sourceNodeFin
              leftEdge.occurrence.sourceNodeFin
              carriedSourceNodeExact)
      have expectedKindTransportExact :
          HEq leftEdge.occurrence.expectedTargetKind
            rightOccurrence.expectedTargetKind :=
        (heq_of_eq carriedExpectedKindExact.symm).trans
          expectedTargetKindPreserved
      have targetBlockFinExact :
          carriedLeftResolved.targetBlockFin =
            leftEdge.resolved.targetBlockFin := by
        apply Fin.ext
        exact coordinatesExact.1.symm
      have targetBlockTransportExact :
          rightResolved.targetBlockIndex =
            (transport.blockBijection.forward
              leftEdge.resolved.targetBlockFin).val :=
        targetBlockTransport.trans
          (congrArg
            (fun index =>
              (transport.blockBijection.forward index).val)
            targetBlockFinExact)
      have targetNodeTransportExact :
          rightResolved.targetNodeIndex.val =
            ((transport.nodeBijection
              leftEdge.resolved.targetBlockFin).forward
              leftEdge.resolved.targetNodeFin).val := by
        exact
          targetNodeTransport.trans
            (transport.forward_node_val_congr
              targetBlockFinExact
              carriedLeftResolved.targetNodeFin
              leftEdge.resolved.targetNodeFin
              coordinatesExact.2.symm)
      exact
        .intro
          sourceBlockTransportExact
          sourceNodeTransportExact
          expectedKindTransportExact
          leftEdge.resolved rightResolved
          leftResolutionExact rightResolutionExact
          targetBlockTransportExact targetNodeTransportExact

/-- The transported right occurrence selected for one resolved left edge. -/
def GraphIsomorphism.transportedRightOccurrenceForEdge
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
    (leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val) :
    PublicReferenceOccurrence right.canonicalRegistry :=
  (isomorphism.externalSlotTransportData
    leftSourceIndex leftEdge leftEdgeMember sourceExact).rightOccurrence

/--
Select the resolved right edge corresponding to the transported external
occurrence.
-/
def GraphIsomorphism.transportedRightEdgeForEdge
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
    (leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val) :
    ResolvedEdge right.canonicalRegistry right.registryKeysNoDup :=
  right.resolvedEdges.edgeForOccurrence
    (isomorphism.transportedRightOccurrenceForEdge
      leftSourceIndex leftEdge leftEdgeMember sourceExact)

theorem GraphIsomorphism.transported_right_edge_for_edge_member
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
    (leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val) :
    isomorphism.transportedRightEdgeForEdge
        leftSourceIndex leftEdge leftEdgeMember sourceExact ∈
      right.resolvedEdges.edges := by
  unfold GraphIsomorphism.transportedRightEdgeForEdge
  exact right.resolvedEdges.edge_for_occurrence_member _

theorem GraphIsomorphism.transported_right_edge_for_edge_isomorphic
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
    (leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
    (sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val) :
    PublicReferenceOccurrenceIsomorphic
      isomorphism.transport leftEdge.occurrence
        (isomorphism.transportedRightEdgeForEdge
          leftSourceIndex leftEdge
          leftEdgeMember sourceExact).occurrence := by
  let data :=
    isomorphism.externalSlotTransportData
      leftSourceIndex leftEdge leftEdgeMember sourceExact
  have reanchored :=
    data.reanchored leftEdgeMember
  have occurrenceExact :=
    right.resolvedEdges.edge_for_occurrence_exact
      data.rightOccurrence
  unfold GraphIsomorphism.transportedRightEdgeForEdge
  unfold GraphIsomorphism.transportedRightOccurrenceForEdge
  rw [occurrenceExact]
  exact reanchored

structure LowerRankCanonicalEnvironmentAgreement
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length) where
  rightEdgeFor :
    ∀ (leftEdge :
        ResolvedEdge left.canonicalRegistry left.registryKeysNoDup)
      (_leftEdgeMember : leftEdge ∈ left.resolvedEdges.edges)
      (_sourceExact :
        leftEdge.occurrence.sourceBlockIndex = leftSourceIndex.val)
      (_lower :
        left.dependency.height leftEdge.resolved.targetBlockIndex <
          left.dependency.height leftSourceIndex.val),
      ResolvedEdge right.canonicalRegistry right.registryKeysNoDup
  rightEdgeMember :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      rightEdgeFor leftEdge leftEdgeMember sourceExact lower ∈
        right.resolvedEdges.edges
  occurrenceTransport :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      PublicReferenceOccurrenceIsomorphic transport leftEdge.occurrence
        (rightEdgeFor
          leftEdge leftEdgeMember sourceExact lower).occurrence
  targetBlockBytesExact :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      encodeCanonicalBlock leftEdge.resolved.targetBlock.block =
        encodeCanonicalBlock
          (rightEdgeFor
            leftEdge leftEdgeMember sourceExact lower).resolved.targetBlock.block
  targetAddressExact :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      HEq leftEdge.resolved.targetBlock.blockQ
        (rightEdgeFor
          leftEdge leftEdgeMember sourceExact lower).resolved.targetBlock.blockQ
  targetSelectorExact :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      (rightEdgeFor
        leftEdge leftEdgeMember sourceExact lower).resolved.targetNodeIndex.val =
      ((transport.nodeBijection
        leftEdge.resolved.targetBlockFin).forward
        leftEdge.resolved.targetNodeFin).val
  targetSelectorCanonicalExact :
    ∀ leftEdge leftEdgeMember sourceExact lower,
      (rightEdgeFor
        leftEdge leftEdgeMember sourceExact lower).resolved.targetNodeIndex.val =
      leftEdge.resolved.targetNodeIndex.val

/-- Kind, typed block address, and canonical selector determine an external ref. -/
theorem external_ref_eq_of_kind_address_selector
    {left right : ExternalRef schema}
    (kindExact : left.kind = right.kind)
    (addressExact : HEq left.target.blockQ right.target.blockQ)
    (selectorExact :
      left.target.canonicalLocalIndex =
        right.target.canonicalLocalIndex) :
    left = right := by
  cases left with
  | mk leftKind leftTarget =>
      cases right with
      | mk rightKind rightTarget =>
          cases kindExact
          cases leftTarget with
          | mk leftAddress leftSelector =>
              cases rightTarget with
              | mk rightAddress rightSelector =>
                  cases eq_of_heq addressExact
                  cases selectorExact
                  rfl

/-- Equal existentially typed canonical blocks expose equal typed addresses. -/
theorem some_canonical_block_address_heq_of_eq
    {context : GraphCodecContext}
    {left right : SomeCanonicalBlock context}
    (exact : left = right) :
    HEq left.blockQ right.blockQ := by
  cases exact
  rfl

/--
An isomorphic resolved edge transports both of its canonical target
coordinates through the registry/node transport.
-/
theorem resolved_edge_target_coordinates_transport
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftEdge :
      ResolvedEdge left.canonicalRegistry left.registryKeysNoDup}
    {rightEdge :
      ResolvedEdge right.canonicalRegistry right.registryKeysNoDup}
    (leftMember : leftEdge ∈ left.resolvedEdges.edges)
    (rightMember : rightEdge ∈ right.resolvedEdges.edges)
    (isomorphic :
      PublicReferenceOccurrenceIsomorphic
        transport leftEdge.occurrence rightEdge.occurrence) :
    rightEdge.resolved.targetBlockIndex =
        (transport.blockBijection.forward
          leftEdge.resolved.targetBlockFin).val ∧
      rightEdge.resolved.targetNodeIndex.val =
        ((transport.nodeBijection
          leftEdge.resolved.targetBlockFin).forward
          leftEdge.resolved.targetNodeFin).val := by
  cases isomorphic with
  | intro _sourceBlockTransport _sourceNodeTransport
      _expectedTargetKindPreserved
      leftResolved rightResolved
      leftResolutionExact rightResolutionExact
      targetBlockTransport targetNodeTransport =>
      have leftResolvedExact :
          leftEdge.resolved = leftResolved :=
        Except.ok.inj
          ((left.resolvedEdges.sound leftEdge leftMember).symm.trans
            leftResolutionExact)
      have rightResolvedExact :
          rightEdge.resolved = rightResolved :=
        Except.ok.inj
          ((right.resolvedEdges.sound rightEdge rightMember).symm.trans
            rightResolutionExact)
      subst leftResolved
      subst rightResolved
      exact
        ⟨targetBlockTransport, targetNodeTransport⟩

/--
Construct the complete lower-rank canonical environment agreement from a
graph isomorphism and already established lower-rank block/node exactness.
-/
def GraphIsomorphism.lowerRankEnvironmentAgreement
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphism : GraphIsomorphism left right)
    (leftSourceIndex : Fin left.canonicalRegistry.length)
    (lowerBlockBytes :
      ∀ lowerIndex,
        left.dependency.height lowerIndex.val <
            left.dependency.height leftSourceIndex.val →
          encodeCanonicalBlock
              (left.canonicalRegistry.get lowerIndex).block =
            encodeCanonicalBlock
              (right.canonicalRegistry.get
                (isomorphism.transport.blockBijection.forward
                  lowerIndex)).block)
    (lowerNodeValues :
      ∀ lowerIndex,
        left.dependency.height lowerIndex.val <
            left.dependency.height leftSourceIndex.val →
          ∀ lowerNodeIndex,
            ((isomorphism.transport.nodeBijection
              lowerIndex).forward lowerNodeIndex).val =
              lowerNodeIndex.val) :
    LowerRankCanonicalEnvironmentAgreement
      isomorphism.transport leftSourceIndex := by
  refine
    { rightEdgeFor := fun leftEdge leftEdgeMember sourceExact _lower =>
        isomorphism.transportedRightEdgeForEdge
          leftSourceIndex leftEdge leftEdgeMember sourceExact
      rightEdgeMember := ?_
      occurrenceTransport := ?_
      targetBlockBytesExact := ?_
      targetAddressExact := ?_
      targetSelectorExact := ?_
      targetSelectorCanonicalExact := ?_ }
  · intro leftEdge leftEdgeMember sourceExact lower
    exact
      isomorphism.transported_right_edge_for_edge_member
        leftSourceIndex leftEdge leftEdgeMember sourceExact
  · intro leftEdge leftEdgeMember sourceExact lower
    exact
      isomorphism.transported_right_edge_for_edge_isomorphic
        leftSourceIndex leftEdge leftEdgeMember sourceExact
  · intro leftEdge leftEdgeMember sourceExact lower
    let rightEdge :=
      isomorphism.transportedRightEdgeForEdge
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have rightEdgeMember :
        rightEdge ∈ right.resolvedEdges.edges :=
      isomorphism.transported_right_edge_for_edge_member
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have occurrenceTransport :
        PublicReferenceOccurrenceIsomorphic
          isomorphism.transport leftEdge.occurrence
            rightEdge.occurrence :=
      isomorphism.transported_right_edge_for_edge_isomorphic
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have targetCoordinates :=
      resolved_edge_target_coordinates_transport
        leftEdgeMember rightEdgeMember occurrenceTransport
    have rightTargetFinExact :
        rightEdge.resolved.targetBlockFin =
          isomorphism.transport.blockBijection.forward
            leftEdge.resolved.targetBlockFin := by
      apply Fin.ext
      exact targetCoordinates.1
    calc
      encodeCanonicalBlock leftEdge.resolved.targetBlock.block =
          encodeCanonicalBlock
            (left.canonicalRegistry.get
              leftEdge.resolved.targetBlockFin).block :=
        congrArg
          (fun entry => encodeCanonicalBlock entry.block)
          leftEdge.resolved.target_block_get_exact.symm
      _ = encodeCanonicalBlock
            (right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftEdge.resolved.targetBlockFin)).block :=
        lowerBlockBytes leftEdge.resolved.targetBlockFin lower
      _ = encodeCanonicalBlock
            (right.canonicalRegistry.get
              rightEdge.resolved.targetBlockFin).block :=
        congrArg
          (fun index =>
            encodeCanonicalBlock
              (right.canonicalRegistry.get index).block)
          rightTargetFinExact.symm
      _ = encodeCanonicalBlock rightEdge.resolved.targetBlock.block :=
        congrArg
          (fun entry => encodeCanonicalBlock entry.block)
          rightEdge.resolved.target_block_get_exact
  · intro leftEdge leftEdgeMember sourceExact lower
    let rightEdge :=
      isomorphism.transportedRightEdgeForEdge
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have rightEdgeMember :
        rightEdge ∈ right.resolvedEdges.edges :=
      isomorphism.transported_right_edge_for_edge_member
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have occurrenceTransport :
        PublicReferenceOccurrenceIsomorphic
          isomorphism.transport leftEdge.occurrence
            rightEdge.occurrence :=
      isomorphism.transported_right_edge_for_edge_isomorphic
        leftSourceIndex leftEdge leftEdgeMember sourceExact
    have targetCoordinates :=
      resolved_edge_target_coordinates_transport
        leftEdgeMember rightEdgeMember occurrenceTransport
    have rightTargetFinExact :
        rightEdge.resolved.targetBlockFin =
          isomorphism.transport.blockBijection.forward
            leftEdge.resolved.targetBlockFin := by
      apply Fin.ext
      exact targetCoordinates.1
    have transportedAddressExact :=
      transported_registry_block_address_heq_of_bytes
        isomorphism.transport leftEdge.resolved.targetBlockFin
        (lowerBlockBytes leftEdge.resolved.targetBlockFin lower)
    have leftTargetStoredExact :
        HEq leftEdge.resolved.targetBlock.blockQ
          (left.canonicalRegistry.get
            leftEdge.resolved.targetBlockFin).blockQ :=
      some_canonical_block_address_heq_of_eq
        leftEdge.resolved.target_block_get_exact.symm
    have rightTargetStoredExact :
        HEq
          (right.canonicalRegistry.get
            (isomorphism.transport.blockBijection.forward
              leftEdge.resolved.targetBlockFin)).blockQ
          rightEdge.resolved.targetBlock.blockQ := by
      have targetBlockExact :
          right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftEdge.resolved.targetBlockFin) =
            rightEdge.resolved.targetBlock := by
        calc
          right.canonicalRegistry.get
              (isomorphism.transport.blockBijection.forward
                leftEdge.resolved.targetBlockFin) =
              right.canonicalRegistry.get
                rightEdge.resolved.targetBlockFin :=
            congrArg right.canonicalRegistry.get
              rightTargetFinExact.symm
          _ = rightEdge.resolved.targetBlock :=
            rightEdge.resolved.target_block_get_exact
      exact
        some_canonical_block_address_heq_of_eq targetBlockExact
    exact
      leftTargetStoredExact.trans
        (transportedAddressExact.trans rightTargetStoredExact)
  · intro leftEdge leftEdgeMember sourceExact lower
    exact
      (resolved_edge_target_coordinates_transport
        leftEdgeMember
        (isomorphism.transported_right_edge_for_edge_member
          leftSourceIndex leftEdge leftEdgeMember sourceExact)
        (isomorphism.transported_right_edge_for_edge_isomorphic
          leftSourceIndex leftEdge leftEdgeMember sourceExact)).2
  · intro leftEdge leftEdgeMember sourceExact lower
    have transportedSelector :=
      (resolved_edge_target_coordinates_transport
        leftEdgeMember
        (isomorphism.transported_right_edge_for_edge_member
          leftSourceIndex leftEdge leftEdgeMember sourceExact)
        (isomorphism.transported_right_edge_for_edge_isomorphic
          leftSourceIndex leftEdge leftEdgeMember sourceExact)).2
    exact
      transportedSelector.trans
        (lowerNodeValues
          leftEdge.resolved.targetBlockFin lower
          leftEdge.resolved.targetNodeFin)

/-- Isomorphic public-reference occurrences preserve their expected kind. -/
theorem public_reference_occurrence_isomorphic_expected_kind
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftOccurrence :
      PublicReferenceOccurrence left.canonicalRegistry}
    {rightOccurrence :
      PublicReferenceOccurrence right.canonicalRegistry}
    (isomorphic :
      PublicReferenceOccurrenceIsomorphic
        transport leftOccurrence rightOccurrence) :
    HEq leftOccurrence.expectedTargetKind
      rightOccurrence.expectedTargetKind := by
  cases isomorphic with
  | intro _sourceBlockTransport _sourceNodeTransport
      expectedTargetKindPreserved
      _leftResolved _rightResolved
      _leftResolutionExact _rightResolutionExact
      _targetBlockTransport _targetNodeTransport =>
      exact expectedTargetKindPreserved

/--
Resolved occurrences with the same canonical target coordinates carry the
same serialized external reference.
-/
theorem resolved_occurrence_refs_eq_of_canonical_target_exact
    {context : GraphCodecContext}
    {leftRegistry rightRegistry : List (SomeCanonicalBlock context)}
    {leftOccurrence : PublicReferenceOccurrence leftRegistry}
    {rightOccurrence : PublicReferenceOccurrence rightRegistry}
    (leftResolved : ResolvedPublicReference leftOccurrence)
    (rightResolved : ResolvedPublicReference rightOccurrence)
    (expectedKindExact :
      HEq leftOccurrence.expectedTargetKind
        rightOccurrence.expectedTargetKind)
    (targetAddressExact :
      HEq leftResolved.targetBlock.blockQ
        rightResolved.targetBlock.blockQ)
    (targetSelectorBytesExact :
      leftResolved.targetNodeIndex.val =
        rightResolved.targetNodeIndex.val) :
    leftOccurrence.ref = rightOccurrence.ref := by
  have expectedKindEq :
      leftOccurrence.expectedTargetKind =
        rightOccurrence.expectedTargetKind :=
    eq_of_heq expectedKindExact
  have refKindExact :
      leftOccurrence.ref.kind = rightOccurrence.ref.kind :=
    leftResolved.expectedTargetKind.symm.trans
      (expectedKindEq.trans rightResolved.expectedTargetKind)
  have refAddressExact :
      HEq leftOccurrence.ref.target.blockQ
        rightOccurrence.ref.target.blockQ :=
    leftResolved.targetAddress.symm.trans
      (targetAddressExact.trans rightResolved.targetAddress)
  have refSelectorExact :
      leftOccurrence.ref.target.canonicalLocalIndex =
        rightOccurrence.ref.target.canonicalLocalIndex :=
    leftResolved.targetNodeIndexExact.symm.trans
      (targetSelectorBytesExact.trans
        rightResolved.targetNodeIndexExact)
  exact
    external_ref_eq_of_kind_address_selector
      refKindExact refAddressExact refSelectorExact

/--
Lower-rank environment agreement is sufficient to identify any pair of
anchored external references in a transported edge slot.
-/
theorem target_at_transport_external_ref_exact_of_lower_rank_agreement
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    {leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)}
    {leftPosition : Fin leftCollection.targets.length}
    {rightPosition : Fin rightCollection.targets.length}
    (agreement :
      LowerRankCanonicalEnvironmentAgreement transport leftBlockIndex)
    (witness :
      TargetAtTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection leftPosition rightPosition)
    {leftRef rightRef}
    (leftSlot :
      leftCollection.targets.get leftPosition = .external leftRef)
    (rightSlot :
      rightCollection.targets.get rightPosition = .external rightRef) :
    leftRef = rightRef := by
  rcases
      target_at_transport_external_anchored
        witness leftSlot rightSlot with
    ⟨leftOccurrence, rightOccurrence,
      leftSourceBlockExact, _rightSourceBlockExact,
      _leftSourceNodeExact, _rightSourceNodeExact,
      _leftOwningCollectionExact, _rightOwningCollectionExact,
      _leftPositionExact, _rightPositionExact,
      _leftExpectedKindExact, _rightExpectedKindExact,
      leftRefExact, rightRefExact, anchoredIsomorphic⟩
  rcases left.resolvedEdges.complete leftOccurrence with
    ⟨leftEdge, leftEdgeMember, leftOccurrenceExact⟩
  rcases right.resolvedEdges.complete rightOccurrence with
    ⟨anchoredRightEdge, anchoredRightEdgeMember,
      rightOccurrenceExact⟩
  have sourceExact :
      leftEdge.occurrence.sourceBlockIndex = leftBlockIndex.val := by
    rw [leftOccurrenceExact]
    exact leftSourceBlockExact
  have lower :
      left.dependency.height leftEdge.resolved.targetBlockIndex <
        left.dependency.height leftBlockIndex.val :=
    left.dependency.decreases
      ⟨leftEdge, leftEdgeMember, sourceExact, rfl⟩
  let chosenRightEdge :=
    agreement.rightEdgeFor
      leftEdge leftEdgeMember sourceExact lower
  have chosenRightEdgeMember :
      chosenRightEdge ∈ right.resolvedEdges.edges :=
    agreement.rightEdgeMember
      leftEdge leftEdgeMember sourceExact lower
  have chosenIsomorphic :
      PublicReferenceOccurrenceIsomorphic transport
        leftEdge.occurrence chosenRightEdge.occurrence :=
    agreement.occurrenceTransport
      leftEdge leftEdgeMember sourceExact lower
  have anchoredIsomorphicEdges :
      PublicReferenceOccurrenceIsomorphic transport
        leftEdge.occurrence anchoredRightEdge.occurrence := by
    rw [leftOccurrenceExact, rightOccurrenceExact]
    exact anchoredIsomorphic
  have chosenCoordinates :=
    resolved_edge_target_coordinates_transport
      leftEdgeMember chosenRightEdgeMember chosenIsomorphic
  have anchoredCoordinates :=
    resolved_edge_target_coordinates_transport
      leftEdgeMember anchoredRightEdgeMember
      anchoredIsomorphicEdges
  have targetBlockIndexExact :
      chosenRightEdge.resolved.targetBlockFin =
        anchoredRightEdge.resolved.targetBlockFin := by
    apply Fin.ext
    exact
      chosenCoordinates.1.trans anchoredCoordinates.1.symm
  have targetBlockExact :
      chosenRightEdge.resolved.targetBlock =
        anchoredRightEdge.resolved.targetBlock := by
    calc
      chosenRightEdge.resolved.targetBlock =
          right.canonicalRegistry.get
            chosenRightEdge.resolved.targetBlockFin :=
        chosenRightEdge.resolved.target_block_get_exact.symm
      _ = right.canonicalRegistry.get
            anchoredRightEdge.resolved.targetBlockFin :=
        congrArg right.canonicalRegistry.get targetBlockIndexExact
      _ = anchoredRightEdge.resolved.targetBlock :=
        anchoredRightEdge.resolved.target_block_get_exact
  have chosenAnchoredAddressExact :
      HEq chosenRightEdge.resolved.targetBlock.blockQ
        anchoredRightEdge.resolved.targetBlock.blockQ :=
    some_canonical_block_address_heq_of_eq targetBlockExact
  have targetAddressExact :
      HEq leftEdge.resolved.targetBlock.blockQ
        anchoredRightEdge.resolved.targetBlock.blockQ :=
    (agreement.targetAddressExact
      leftEdge leftEdgeMember sourceExact lower).trans
      chosenAnchoredAddressExact
  have targetSelectorExact :
      leftEdge.resolved.targetNodeIndex.val =
        anchoredRightEdge.resolved.targetNodeIndex.val := by
    calc
      leftEdge.resolved.targetNodeIndex.val =
          chosenRightEdge.resolved.targetNodeIndex.val :=
        (agreement.targetSelectorCanonicalExact
          leftEdge leftEdgeMember sourceExact lower).symm
      _ = anchoredRightEdge.resolved.targetNodeIndex.val :=
        chosenCoordinates.2.trans anchoredCoordinates.2.symm
  have expectedKindExact :
      HEq leftEdge.occurrence.expectedTargetKind
        anchoredRightEdge.occurrence.expectedTargetKind :=
    public_reference_occurrence_isomorphic_expected_kind
      anchoredIsomorphicEdges
  have occurrenceRefsExact :
      leftEdge.occurrence.ref = anchoredRightEdge.occurrence.ref :=
    resolved_occurrence_refs_eq_of_canonical_target_exact
      leftEdge.resolved anchoredRightEdge.resolved
      expectedKindExact targetAddressExact targetSelectorExact
  have leftEdgeRefExact :
      leftEdge.occurrence.ref = leftRef := by
    rw [leftOccurrenceExact]
    exact leftRefExact
  have rightEdgeRefExact :
      anchoredRightEdge.occurrence.ref = rightRef := by
    rw [rightOccurrenceExact]
    exact rightRefExact
  exact
    leftEdgeRefExact.symm.trans
      (occurrenceRefsExact.trans rightEdgeRefExact)

/--
An anchored target transport is exactly the graph reference produced by the
transport's local relabeling once external target coordinates are canonical.
-/
theorem target_at_transport_relabel_graph_ref_exact
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    {leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)}
    {leftPosition : Fin leftCollection.targets.length}
    {rightPosition : Fin rightCollection.targets.length}
    (witness :
      TargetAtTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection leftPosition rightPosition)
    (externalRefsExact :
      ∀ {leftRef rightRef},
        leftCollection.targets.get leftPosition = .external leftRef →
        rightCollection.targets.get rightPosition = .external rightRef →
        leftRef = rightRef) :
    relabelGraphRef
        (transport.nodeBijection leftBlockIndex).toLocalBijection
        (leftCollection.targets.get leftPosition) =
      rightCollection.targets.get rightPosition := by
  cases witness with
  | «local» leftLocal rightLocal leftExact rightExact
      leftBound rightBound indexTransport =>
      rw [leftExact, rightExact]
      rw [relabel_graph_ref_local
        (transport.nodeBijection leftBlockIndex).toLocalBijection
        leftLocal leftBound]
      apply congrArg
        Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.local
      calc
        ((transport.nodeBijection
            leftBlockIndex).toLocalBijection.forward
          ⟨leftLocal, leftBound⟩).val =
            ((transport.nodeBijection leftBlockIndex).forward
              ⟨leftLocal, leftBound⟩).val :=
          FiniteBijection.toLocalBijection_forward_val _ _
        _ = rightLocal := congrArg Fin.val indexTransport
  | external leftRef rightRef leftExact rightExact
      _leftOccurrence _rightOccurrence
      _leftSourceBlockExact _rightSourceBlockExact
      _leftSourceNodeExact _rightSourceNodeExact
      _leftOwningCollectionExact _rightOwningCollectionExact
      _leftPositionExact _rightPositionExact
      _leftExpectedKindExact _rightExpectedKindExact
      _leftRefExact _rightRefExact _occurrenceTransport =>
      rw [leftExact, rightExact]
      rw [relabel_graph_ref_external]
      exact congrArg
        Residua.RCC.Addressing.AddressedGraph.Foundation.GraphRef.external
        (externalRefsExact leftExact rightExact)

/--
Relabeling the targets of a transported edge collection yields a permutation of
the target collection's references.
-/
theorem edge_collection_transport_target_permutation
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    {leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)}
    (collectionTransport :
      EdgeCollectionTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection)
    (externalRefsExact :
      ∀ (leftPosition : Fin leftCollection.targets.length)
        {leftRef rightRef},
        leftCollection.targets.get leftPosition = .external leftRef →
        rightCollection.targets.get
            (collectionTransport.targetBijection.forward leftPosition) =
          .external rightRef →
        leftRef = rightRef) :
    IsPermutation
      (leftCollection.targets.map
        (relabelGraphRef
          (transport.nodeBijection leftBlockIndex).toLocalBijection))
      rightCollection.targets := by
  apply list_map_permutation_of_finite_bijection_get
    collectionTransport.targetBijection
    (relabelGraphRef
      (transport.nodeBijection leftBlockIndex).toLocalBijection)
  intro leftPosition
  exact
    target_at_transport_relabel_graph_ref_exact
      (collectionTransport.targets leftPosition)
      (externalRefsExact leftPosition)

/-- An edge collection is determined by its observable shape and targets. -/
theorem edge_collection_eq_of_fields
    {left right : EdgeCollection schema External}
    (modeExact : left.mode = right.mode)
    (labelExact : left.labelText = right.labelText)
    (directionExact : left.direction = right.direction)
    (expectedKindExact :
      left.expectedTargetKind = right.expectedTargetKind)
    (targetsExact : left.targets = right.targets) :
    left = right := by
  cases left <;> cases right <;>
    simp only [
      Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.mode,
      Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.labelText,
      Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.direction,
      Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.expectedTargetKind,
      Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.targets
    ] at *
  all_goals
    try contradiction
  all_goals
    cases labelExact
    cases directionExact
    cases expectedKindExact
    cases targetsExact
    rfl

/-- Relabeling references preserves the ordered/unordered collection mode. -/
theorem relabel_collection_mode
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).mode =
      collection.mode := by
  cases collection <;> rfl

/-- Relabeling references preserves the semantic collection label. -/
theorem relabel_collection_label_text
    (bijection : LocalBijection n)
    (collection : EdgeCollection schema External) :
    (relabelCollection bijection collection).labelText =
      collection.labelText := by
  cases collection <;> rfl

/-- Replacing a collection's targets by themselves is definitionally inert. -/
theorem collection_with_targets_self
    (collection : EdgeCollection schema External) :
    collectionWithTargets collection collection.targets = collection := by
  cases collection <;> rfl

/-- Replacing targets preserves every non-target collection field. -/
theorem collection_with_targets_mode
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    (collectionWithTargets collection targets).mode =
      collection.mode := by
  cases collection <;> rfl

theorem collection_with_targets_label_text
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    (collectionWithTargets collection targets).labelText =
      collection.labelText := by
  cases collection <;> rfl

theorem collection_with_targets_direction
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    (collectionWithTargets collection targets).direction =
      collection.direction := by
  cases collection <;> rfl

theorem collection_with_targets_expected_target_kind
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    (collectionWithTargets collection targets).expectedTargetKind =
      collection.expectedTargetKind := by
  cases collection <;> rfl

theorem collection_with_targets_targets
    (collection : EdgeCollection schema SourceExternal)
    (targets : List (GraphRef TargetExternal)) :
    (collectionWithTargets collection targets).targets = targets := by
  cases collection <;> rfl

/-- Ordered target lists are already in their canonical target order. -/
theorem normalize_target_list_of_ordered
    (collection :
      EdgeCollection schema (ExternalRef schema))
    (ordered : collection.mode = .ordered) :
    normalizeTargetList collection = collection.targets := by
  cases collection with
  | ordered => rfl
  | unordered =>
      simp [
        Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.mode
      ] at ordered

/--
Replacing a relabeled collection's targets by a collection with the same
non-target fields reconstructs that collection.
-/
theorem collection_with_relabelled_shape_exact
    (bijection : LocalBijection n)
    (left right :
      EdgeCollection schema (ExternalRef schema))
    (modeExact : left.mode = right.mode)
    (labelExact : left.labelText = right.labelText)
    (directionExact : left.direction = right.direction)
    (expectedKindExact :
      left.expectedTargetKind = right.expectedTargetKind) :
    collectionWithTargets
        (relabelCollection bijection left) right.targets =
      right := by
  apply edge_collection_eq_of_fields
  · rw [
      collection_with_targets_mode,
      relabel_collection_mode,
      modeExact
    ]
  · rw [
      collection_with_targets_label_text,
      relabel_collection_label_text,
      labelExact
    ]
  · rw [
      collection_with_targets_direction,
      relabel_collection_direction,
      directionExact
    ]
  · rw [
      collection_with_targets_expected_target_kind,
      relabel_collection_expected_target_kind,
      expectedKindExact
    ]
  · exact collection_with_targets_targets _ _

/--
A transported edge collection materializes exactly after relabeling and
canonical target normalization.
-/
theorem edge_collection_transport_normalized_exact
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    {leftCollection rightCollection :
      EdgeCollection context.kindSchema
        (ExternalRef context.kindSchema)}
    (collectionTransport :
      EdgeCollectionTransport transport leftBlockIndex leftNodeIndex
        leftCollection rightCollection)
    (rightTargetsNormalized :
      rightCollection.mode = .unordered →
        normalizeTargetList rightCollection =
          rightCollection.targets)
    (externalRefsExact :
      ∀ (leftPosition : Fin leftCollection.targets.length)
        {leftRef rightRef},
        leftCollection.targets.get leftPosition = .external leftRef →
        rightCollection.targets.get
            (collectionTransport.targetBijection.forward leftPosition) =
          .external rightRef →
        leftRef = rightRef) :
    collectionWithTargets
        (relabelCollection
          (transport.nodeBijection leftBlockIndex).toLocalBijection
          leftCollection)
        (normalizeTargetList
          (relabelCollection
            (transport.nodeBijection leftBlockIndex).toLocalBijection
            leftCollection)) =
      rightCollection := by
  let localBijection :=
    (transport.nodeBijection leftBlockIndex).toLocalBijection
  have targetPermutation :=
    edge_collection_transport_target_permutation
      collectionTransport externalRefsExact
  cases collectionTransport.positionMap with
  | ordered leftMode rightMode positionExact =>
      have mappedTargetsExact :
          leftCollection.targets.map
              (relabelGraphRef localBijection) =
            rightCollection.targets := by
        apply list_map_eq_of_finite_bijection_position_exact
          collectionTransport.targetBijection
          (relabelGraphRef localBijection)
          positionExact
        intro leftPosition
        exact
          target_at_transport_relabel_graph_ref_exact
            (collectionTransport.targets leftPosition)
            (externalRefsExact leftPosition)
      have relabeledMode :
          (relabelCollection localBijection leftCollection).mode =
            .ordered :=
        (relabel_collection_mode
          localBijection leftCollection).trans leftMode
      have normalizedTargetsExact :
          normalizeTargetList
              (relabelCollection localBijection leftCollection) =
            rightCollection.targets := by
        rw [normalize_target_list_of_ordered _ relabeledMode]
        rw [relabel_collection_targets, mappedTargetsExact]
      rw [normalizedTargetsExact]
      exact
        collection_with_relabelled_shape_exact
          localBijection leftCollection rightCollection
          (leftMode.trans rightMode.symm)
          collectionTransport.labelExact
          collectionTransport.directionExact
          collectionTransport.expectedKindExact
  | unordered leftMode rightMode =>
      have relabeledMode :
          (relabelCollection localBijection leftCollection).mode =
            .unordered :=
        (relabel_collection_mode
          localBijection leftCollection).trans leftMode
      have rightShapeExact :
          collectionWithTargets
              (relabelCollection localBijection leftCollection)
              rightCollection.targets =
            rightCollection :=
        collection_with_relabelled_shape_exact
          localBijection leftCollection rightCollection
          (leftMode.trans rightMode.symm)
          collectionTransport.labelExact
          collectionTransport.directionExact
          collectionTransport.expectedKindExact
      have normalizedTargetsExact :
          normalizeTargetList
              (relabelCollection localBijection leftCollection) =
            rightCollection.targets := by
        calc
          normalizeTargetList
              (relabelCollection localBijection leftCollection) =
            normalizeTargetList
              (collectionWithTargets
                (relabelCollection localBijection leftCollection)
                rightCollection.targets) := by
              simpa [collection_with_targets_self] using
                normalize_target_list_permutation_invariant
                  (relabelCollection localBijection leftCollection)
                  relabeledMode
                  (relabelCollection
                    localBijection leftCollection).targets
                  rightCollection.targets
                  (by
                    rw [relabel_collection_targets]
                    exact targetPermutation)
          _ = normalizeTargetList rightCollection :=
            congrArg normalizeTargetList rightShapeExact
          _ = rightCollection.targets :=
            rightTargetsNormalized rightMode
      rw [normalizedTargetsExact]
      exact rightShapeExact

/--
Every indexed unordered collection in a closed graph is already target-list
normalized.
-/
theorem closed_graph_collection_targets_normalized
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin (graph.canonicalRegistry.get blockIndex).block.nodes.length)
    (collectionIndex :
      Fin
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length))
    (unordered :
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex).mode =
        .unordered) :
    normalizeTargetList
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex) =
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex).targets := by
  let block :=
    (graph.canonicalRegistry.get blockIndex).block
  let node := block.nodes.get nodeIndex
  let collection := node.edgeCollections.get collectionIndex
  let occurrence : CanonicalCollectionOccurrence block.nodes :=
    { sourceNodeIndex := nodeIndex.val
      sourceNode := node
      sourceNodeLookup :=
        list_get?_eq_get block.nodes nodeIndex
      owningCollectionIndex := collectionIndex.val
      owningCollection := collection
      owningCollectionLookup :=
        list_get?_eq_get node.edgeCollections collectionIndex }
  exact
    (graph.registryWellFormed.blocks
      blockIndex).unorderedTargetsNormalized occurrence unordered

/--
Every indexed node in a closed graph is already outer-collection normalized.
-/
theorem closed_graph_node_outer_collections_normalized
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin (graph.canonicalRegistry.get blockIndex).block.nodes.length) :
    normalizeOuterCollections
        ((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections =
      ((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections := by
  exact
    (graph.registryWellFormed.blocks
      blockIndex).outerCollectionsNormalized
      ((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex)
      (list_get_mem_fin
        (graph.canonicalRegistry.get blockIndex).block.nodes nodeIndex)

/--
Relabel a collection and immediately restore its canonical target order.
-/
def normalizedRelabeledCollection
    (bijection : LocalBijection n)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    EdgeCollection schema (ExternalRef schema) :=
  let relabeled := relabelCollection bijection collection
  collectionWithTargets relabeled (normalizeTargetList relabeled)

/-- A graph node is determined by its payload and edge collections. -/
theorem graph_node_eq_of_fields
    {left right : GraphNode schema External}
    (payloadExact : left.payload = right.payload)
    (collectionsExact :
      left.edgeCollections = right.edgeCollections) :
    left = right := by
  cases left
  cases right
  simp only [
    Residua.RCC.Addressing.AddressedGraph.Foundation.GraphNode.mk.injEq
  ] at payloadExact collectionsExact ⊢
  exact ⟨payloadExact, collectionsExact⟩

/--
Materializing a relabeled node normalizes the relabeled collections first,
then canonically orders the outer collection list.
-/
theorem normalize_materialized_relabel_node_collections
    (bijection : LocalBijection n)
    (node : CanonicalNode schema) :
    (normalizeMaterializedNode (relabelNode bijection node)).edgeCollections =
      normalizeOuterCollections
        (node.edgeCollections.map
          (normalizedRelabeledCollection bijection)) := by
  unfold normalizeMaterializedNode
  simp only [relabelNode, List.map_map]
  apply congrArg normalizeOuterCollections
  apply List.map_congr_left
  intro collection _collectionMember
  rfl

/--
Pointwise exact transported collections and a normalized target node assemble
into exact normalized-node materialization.
-/
theorem node_transport_normalized_exact_of_collections
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    (nodeTransport :
      NodeTransport transport leftBlockIndex leftNodeIndex)
    (collectionsExact :
      ∀ leftCollectionIndex,
        normalizedRelabeledCollection
            (transport.nodeBijection
              leftBlockIndex).toLocalBijection
            (((left.canonicalRegistry.get
              leftBlockIndex).block.nodes.get
                leftNodeIndex).edgeCollections.get leftCollectionIndex) =
          (((right.canonicalRegistry.get
            (transport.blockBijection.forward
              leftBlockIndex)).block.nodes.get
              ((transport.nodeBijection
                leftBlockIndex).forward
                leftNodeIndex)).edgeCollections.get
            (nodeTransport.collectionBijection.forward
              leftCollectionIndex)))
    (rightOuterNormalized :
      normalizeOuterCollections
          (((right.canonicalRegistry.get
            (transport.blockBijection.forward
              leftBlockIndex)).block.nodes.get
              ((transport.nodeBijection
                leftBlockIndex).forward
                leftNodeIndex)).edgeCollections) =
        ((right.canonicalRegistry.get
          (transport.blockBijection.forward
            leftBlockIndex)).block.nodes.get
            ((transport.nodeBijection
              leftBlockIndex).forward
              leftNodeIndex)).edgeCollections) :
    normalizeMaterializedNode
        (relabelNode
          (transport.nodeBijection
            leftBlockIndex).toLocalBijection
          ((left.canonicalRegistry.get
            leftBlockIndex).block.nodes.get leftNodeIndex)) =
      ((right.canonicalRegistry.get
        (transport.blockBijection.forward
          leftBlockIndex)).block.nodes.get
          ((transport.nodeBijection
            leftBlockIndex).forward leftNodeIndex)) := by
  let localBijection :=
    (transport.nodeBijection leftBlockIndex).toLocalBijection
  let leftNode :=
    (left.canonicalRegistry.get
      leftBlockIndex).block.nodes.get leftNodeIndex
  let rightNode :=
    (right.canonicalRegistry.get
      (transport.blockBijection.forward
        leftBlockIndex)).block.nodes.get
      ((transport.nodeBijection
        leftBlockIndex).forward leftNodeIndex)
  have normalizedCollectionsPermutation :
      IsPermutation
        (leftNode.edgeCollections.map
          (normalizedRelabeledCollection localBijection))
        rightNode.edgeCollections := by
    apply list_map_permutation_of_finite_bijection_get
      nodeTransport.collectionBijection
      (normalizedRelabeledCollection localBijection)
    intro leftCollectionIndex
    exact collectionsExact leftCollectionIndex
  have normalizedCollectionsExact :
      normalizeOuterCollections
          (leftNode.edgeCollections.map
            (normalizedRelabeledCollection localBijection)) =
        rightNode.edgeCollections := by
    calc
      normalizeOuterCollections
          (leftNode.edgeCollections.map
            (normalizedRelabeledCollection localBijection)) =
        normalizeOuterCollections rightNode.edgeCollections :=
          normalize_outer_collections_permutation_invariant
            _ _ normalizedCollectionsPermutation
      _ = rightNode.edgeCollections := rightOuterNormalized
  have leftCollectionsExact :=
    normalize_materialized_relabel_node_collections
      localBijection leftNode
  change
    ({ payload := leftNode.payload
       edgeCollections :=
        (normalizeMaterializedNode
          (relabelNode localBijection leftNode)).edgeCollections } :
      CanonicalNode context.kindSchema) =
      rightNode
  rw [leftCollectionsExact, normalizedCollectionsExact]
  have payloadExact : leftNode.payload = rightNode.payload :=
    nodeTransport.payloadExact
  exact graph_node_eq_of_fields payloadExact rfl

/--
Lower-rank environment agreement discharges every external-reference premise,
so an isomorphic node materializes to the target graph's canonical node.
-/
theorem node_transport_normalized_exact_of_lower_rank_agreement
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    {leftBlockIndex : Fin left.canonicalRegistry.length}
    {leftNodeIndex :
      Fin (left.canonicalRegistry.get leftBlockIndex).block.nodes.length}
    (agreement :
      LowerRankCanonicalEnvironmentAgreement transport leftBlockIndex)
    (nodeTransport :
      NodeTransport transport leftBlockIndex leftNodeIndex) :
    normalizeMaterializedNode
        (relabelNode
          (transport.nodeBijection
            leftBlockIndex).toLocalBijection
          ((left.canonicalRegistry.get
            leftBlockIndex).block.nodes.get leftNodeIndex)) =
      ((right.canonicalRegistry.get
        (transport.blockBijection.forward
          leftBlockIndex)).block.nodes.get
          ((transport.nodeBijection
            leftBlockIndex).forward leftNodeIndex)) := by
  apply
    node_transport_normalized_exact_of_collections
      nodeTransport
  · intro leftCollectionIndex
    let rightBlockIndex :=
      transport.blockBijection.forward leftBlockIndex
    let rightNodeIndex :=
      (transport.nodeBijection leftBlockIndex).forward leftNodeIndex
    let rightCollectionIndex :=
      nodeTransport.collectionBijection.forward leftCollectionIndex
    let collectionTransport :=
      nodeTransport.collections leftCollectionIndex
    have rightTargetsNormalized :=
      closed_graph_collection_targets_normalized
        right rightBlockIndex rightNodeIndex rightCollectionIndex
    have externalRefsExact :
        ∀ (leftPosition :
            Fin
              ((((left.canonicalRegistry.get
                leftBlockIndex).block.nodes.get
                  leftNodeIndex).edgeCollections.get
                    leftCollectionIndex).targets.length))
          {leftRef rightRef},
          (((left.canonicalRegistry.get
            leftBlockIndex).block.nodes.get
              leftNodeIndex).edgeCollections.get
                leftCollectionIndex).targets.get leftPosition =
            .external leftRef →
          (((right.canonicalRegistry.get
            rightBlockIndex).block.nodes.get
              rightNodeIndex).edgeCollections.get
                rightCollectionIndex).targets.get
                  (collectionTransport.targetBijection.forward
                    leftPosition) =
            .external rightRef →
          leftRef = rightRef := by
      intro leftPosition leftRef rightRef leftSlot rightSlot
      exact
        target_at_transport_external_ref_exact_of_lower_rank_agreement
          agreement
          (collectionTransport.targets leftPosition)
          leftSlot rightSlot
    simpa [normalizedRelabeledCollection] using
      edge_collection_transport_normalized_exact
        collectionTransport rightTargetsNormalized externalRefsExact
  · exact
      closed_graph_node_outer_collections_normalized
        right
        (transport.blockBijection.forward leftBlockIndex)
        ((transport.nodeBijection leftBlockIndex).forward
          leftNodeIndex)

/-- Equality of values makes `indexOfMember` independent of proof identity. -/
theorem index_of_member_eq_of_value_eq
    [DecidableEq α]
    {left right : α}
    (values : List α)
    (leftMember : left ∈ values)
    (rightMember : right ∈ values)
    (exact : left = right) :
    indexOfMember left values leftMember =
      indexOfMember right values rightMember := by
  subst right
  rfl

/-- The canonical range is the identity permutation witness. -/
def identityPermutationWitness (n : Nat) :
    PermutationWitness n :=
  { values := range n
    permutesRange := .rfl }

theorem permutation_bijection_identity (n : Nat) :
    permutationBijection (identityPermutationWitness n) =
      identityLocalBijection n := by
  apply local_bijection_ext
  intro index
  let position : Fin (range n).length :=
    ⟨index.val, by simp [range, index.isLt]⟩
  have valueAtPosition :
      (range n).get position = index.val := by
    simp [range, position]
  have noDuplicates : NoDuplicates (range n) := by
    exact range_no_duplicates n
  have positionExact :=
    indexOfMember_get (range n) noDuplicates position
  have indexMember : index.val ∈ range n := by
    simp [range, index.isLt]
  have indexValueExact :
      indexOfMember index.val (range n) indexMember =
        position := by
    calc
      indexOfMember index.val (range n) indexMember =
          indexOfMember ((range n).get position) (range n)
            (get_mem_compat (range n) position) :=
        index_of_member_eq_of_value_eq
          (range n) indexMember
          (get_mem_compat (range n) position)
          valueAtPosition.symm
      _ = position := positionExact
  apply Fin.ext
  simpa [
    permutationBijection,
    permutationForward,
    identityPermutationWitness,
    identityLocalBijection,
    position
  ] using congrArg Fin.val indexValueExact

/--
Transporting the identity range by a local inverse produces a permutation
witness whose realized bijection is the original bijection.
-/
def localBijectionPermutationWitness
    (bijection : LocalBijection n) :
    PermutationWitness n :=
  transportPermutationSameCount
    (inverseLocalBijection bijection)
    (identityPermutationWitness n)

theorem permutation_bijection_local_witness
    (bijection : LocalBijection n) :
    permutationBijection
        (localBijectionPermutationWitness bijection) =
      bijection := by
  apply local_bijection_ext
  intro index
  have transported :=
    transport_permutation_forward_same_count
      (inverseLocalBijection bijection)
      (identityPermutationWitness n)
      (bijection.forward index)
  rw [permutation_bijection_identity] at transported
  simpa [
    localBijectionPermutationWitness,
    inverseLocalBijection,
    identityLocalBijection,
    bijection.leftInverse
  ] using transported

/-- Realize any finite transport as an exact permutation witness. -/
def FiniteBijection.toPermutationWitness
    (bijection : FiniteBijection leftSize rightSize) :
    PermutationWitness leftSize :=
  localBijectionPermutationWitness bijection.toLocalBijection

theorem FiniteBijection.permutationBijection_toPermutationWitness
    (bijection : FiniteBijection leftSize rightSize) :
    permutationBijection bijection.toPermutationWitness =
      bijection.toLocalBijection :=
  permutation_bijection_local_witness bijection.toLocalBijection

/--
Pointwise normalized node transport reconstructs the target node list in its
literal order.
-/
theorem normalized_relabel_nodes_eq_of_transport
    {leftNodes rightNodes : List (CanonicalNode schema)}
    (bijection :
      FiniteBijection leftNodes.length rightNodes.length)
    (nodesExact :
      ∀ leftIndex,
        normalizeMaterializedNode
            (relabelNode bijection.toLocalBijection
              (leftNodes.get leftIndex)) =
          rightNodes.get (bijection.forward leftIndex)) :
    (relabelNodes leftNodes bijection.toLocalBijection).map
        normalizeMaterializedNode =
      rightNodes := by
  apply List.ext_get
  · simpa [relabel_nodes_length] using bijection.size_eq
  · intro index leftBound rightBound
    let rightIndex : Fin rightNodes.length :=
      ⟨index, rightBound⟩
    let leftIndex : Fin leftNodes.length :=
      bijection.inverse rightIndex
    have forwardExact :
        bijection.forward leftIndex = rightIndex :=
      bijection.rightInverse rightIndex
    have relabeledBound :
        index <
          (relabelNodes leftNodes
            bijection.toLocalBijection).length := by
      simpa using leftBound
    have relabeledPositionExact :
        (bijection.toLocalBijection.forward leftIndex).val =
          index := by
      calc
        (bijection.toLocalBijection.forward leftIndex).val =
            (bijection.forward leftIndex).val :=
          FiniteBijection.toLocalBijection_forward_val _ _
        _ = index := congrArg Fin.val forwardExact
    have relabeledNodeExact :
        (relabelNodes leftNodes
          bijection.toLocalBijection).get
            ⟨index, relabeledBound⟩ =
          relabelNode bijection.toLocalBijection
            (leftNodes.get leftIndex) := by
      simpa [List.get_eq_getElem, relabeledPositionExact] using
        relabel_nodes_get
          leftNodes bijection.toLocalBijection leftIndex
    have relabeledNodeGetElemExact :
        (relabelNodes leftNodes
          bijection.toLocalBijection)[index]'relabeledBound =
          relabelNode bijection.toLocalBijection
            (leftNodes.get leftIndex) := by
      simpa [List.get_eq_getElem] using relabeledNodeExact
    rw [List.get_eq_getElem, List.get_eq_getElem]
    simp only [List.getElem_map]
    rw [relabeledNodeGetElemExact]
    have nodeExact := nodesExact leftIndex
    simpa [rightIndex, forwardExact] using nodeExact

/--
If normalized relabeling reconstructs every target node and block forms agree,
the corresponding pure permutation candidate has exactly the target bytes.
-/
theorem pure_materialize_encode_exact_of_normalized_nodes
    {leftBlock : CanonicalBlock schema leftKind}
    {rightBlock : CanonicalBlock schema rightKind}
    (nodeBijection :
      FiniteBijection leftBlock.nodes.length rightBlock.nodes.length)
    (formExact : leftBlock.form = rightBlock.form)
    (nodesExact :
      ∀ leftNodeIndex,
        normalizeMaterializedNode
            (relabelNode nodeBijection.toLocalBijection
              (leftBlock.nodes.get leftNodeIndex)) =
          rightBlock.nodes.get
            (nodeBijection.forward leftNodeIndex)) :
    encodeCanonicalBlock
        (pureMaterializeCanonicalBlock leftBlock
          nodeBijection.toPermutationWitness) =
      encodeCanonicalBlock rightBlock := by
  have permutationExact :
      permutationBijection
          nodeBijection.toPermutationWitness =
        nodeBijection.toLocalBijection :=
    nodeBijection.permutationBijection_toPermutationWitness
  cases leftBlock with
  | dagSingleton leftNode =>
      cases rightBlock with
      | dagSingleton rightNode =>
          let leftNodeIndex : Fin [leftNode].length :=
            ⟨0, by simp⟩
          have materializedNodeExact :
              normalizeMaterializedNode
                  (relabelNode nodeBijection.toLocalBijection
                    leftNode) =
                rightNode := by
            simpa [leftNodeIndex] using nodesExact leftNodeIndex
          have materializedNodeWithPermutationExact :
              normalizeMaterializedNode
                  (relabelNode
                    (permutationBijection
                      nodeBijection.toPermutationWitness)
                    leftNode) =
                rightNode :=
            (congrArg
              (fun bijection =>
                normalizeMaterializedNode
                  (relabelNode bijection leftNode))
              permutationExact).trans materializedNodeExact
          simp only [pureMaterializeCanonicalBlock]
          rw [materializedNodeWithPermutationExact]
          rfl
      | cyclic rightNodes =>
          cases formExact
  | cyclic leftNodes =>
      cases rightBlock with
      | dagSingleton rightNode =>
          cases formExact
      | cyclic rightNodes =>
          have materializedNodesExact :
              (relabelNodes leftNodes
                  nodeBijection.toLocalBijection).map
                  normalizeMaterializedNode =
                rightNodes :=
            normalized_relabel_nodes_eq_of_transport
              nodeBijection nodesExact
          have materializedNodesWithPermutationExact :
              (relabelNodes leftNodes
                  (permutationBijection
                    nodeBijection.toPermutationWitness)).map
                  normalizeMaterializedNode =
                rightNodes :=
            (congrArg
              (fun bijection =>
                (relabelNodes leftNodes bijection).map
                  normalizeMaterializedNode)
              permutationExact).trans materializedNodesExact
          simp only [pureMaterializeCanonicalBlock]
          rw [materializedNodesWithPermutationExact]
          rfl

/--
An isomorphic block under lower-rank environment agreement occurs as the
transport permutation candidate with the target block's exact bytes.
-/
theorem pure_materialize_transport_encode_exact
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (agreement :
      LowerRankCanonicalEnvironmentAgreement transport leftBlockIndex)
    (blockIsomorphic :
      BlockIsomorphic transport leftBlockIndex) :
    encodeCanonicalBlock
        (pureMaterializeCanonicalBlock
          (left.canonicalRegistry.get leftBlockIndex).block
          (transport.nodeBijection
            leftBlockIndex).toPermutationWitness) =
      encodeCanonicalBlock
        (right.canonicalRegistry.get
          (transport.blockBijection.forward leftBlockIndex)).block := by
  apply
    pure_materialize_encode_exact_of_normalized_nodes
      (transport.nodeBijection leftBlockIndex)
      blockIsomorphic.formExact
  intro leftNodeIndex
  exact
    node_transport_normalized_exact_of_lower_rank_agreement
      agreement (blockIsomorphic.nodes leftNodeIndex)

/-- Identity relabeling fixes every local or external graph reference. -/
theorem relabel_graph_ref_identity
    (reference : GraphRef External) :
    relabelGraphRef (identityLocalBijection n) reference =
      reference := by
  cases reference with
  | external =>
      rfl
  | «local» index =>
      simp [relabelGraphRef, identityLocalBijection]

/-- Identity relabeling fixes every edge collection. -/
theorem relabel_collection_identity
    (collection : EdgeCollection schema External) :
    relabelCollection (identityLocalBijection n) collection =
      collection := by
  have targetsExact :
      ∀ targets : List (GraphRef External),
        targets.map
            (relabelGraphRef (identityLocalBijection n)) =
          targets := by
    intro targets
    calc
      targets.map
          (relabelGraphRef (identityLocalBijection n)) =
          targets.map id := by
        apply List.map_congr_left
        intro reference _
        exact relabel_graph_ref_identity reference
      _ = targets := List.map_id targets
  cases collection <;> simp [relabelCollection, targetsExact]

/-- Identity relabeling fixes every graph node. -/
theorem relabel_node_identity
    (node : GraphNode schema External) :
    relabelNode (identityLocalBijection n) node = node := by
  cases node with
  | mk payload collections =>
      simp only [relabelNode]
      have collectionsExact :
          collections.map
              (relabelCollection (identityLocalBijection n)) =
            collections := by
        calc
          collections.map
              (relabelCollection (identityLocalBijection n)) =
              collections.map id := by
            apply List.map_congr_left
            intro collection _
            exact relabel_collection_identity collection
          _ = collections := List.map_id collections
      rw [collectionsExact]

/-- Identity relabeling fixes the canonical ordering of a node list. -/
theorem relabel_nodes_identity
    (nodes : List (GraphNode schema External)) :
    relabelNodes nodes (identityLocalBijection nodes.length) =
      nodes := by
  apply List.ext_get
  · exact relabel_nodes_length nodes _
  · intro index leftBound rightBound
    let sourceIndex : Fin nodes.length := ⟨index, rightBound⟩
    have atForward :=
      relabel_nodes_get nodes
        (identityLocalBijection nodes.length) sourceIndex
    rw [relabel_node_identity] at atForward
    simpa [identityLocalBijection] using atForward

/-- Every indexed collection in a closed graph is target-normalized. -/
theorem closed_graph_collection_targets_normalized_all
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin (graph.canonicalRegistry.get blockIndex).block.nodes.length)
    (collectionIndex :
      Fin
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.length)) :
    normalizeTargetList
        (((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex).edgeCollections.get collectionIndex) =
      (((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex).edgeCollections.get collectionIndex).targets := by
  let collection :=
    ((graph.canonicalRegistry.get blockIndex).block.nodes.get
      nodeIndex).edgeCollections.get collectionIndex
  cases modeExact : collection.mode with
  | ordered =>
      exact normalize_target_list_of_ordered collection modeExact
  | unordered =>
      exact
        closed_graph_collection_targets_normalized
          graph blockIndex nodeIndex collectionIndex modeExact

/-- Every indexed node in a closed graph is fixed by material normalization. -/
theorem closed_graph_node_normalized
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (nodeIndex :
      Fin (graph.canonicalRegistry.get blockIndex).block.nodes.length) :
    normalizeMaterializedNode
        ((graph.canonicalRegistry.get blockIndex).block.nodes.get
          nodeIndex) =
      ((graph.canonicalRegistry.get blockIndex).block.nodes.get
        nodeIndex) := by
  let node :=
    (graph.canonicalRegistry.get blockIndex).block.nodes.get nodeIndex
  let normalizeCollection :
      EdgeCollection context.kindSchema
          (ExternalRef context.kindSchema) →
        EdgeCollection context.kindSchema
          (ExternalRef context.kindSchema) :=
    fun collection =>
      collectionWithTargets collection (normalizeTargetList collection)
  have normalizedCollections :
      node.edgeCollections.map normalizeCollection =
        node.edgeCollections := by
    calc
      node.edgeCollections.map normalizeCollection =
          node.edgeCollections.map id := by
        apply List.map_congr_left
        intro collection collectionMember
        rcases List.get_of_mem collectionMember with
          ⟨collectionIndex, collectionExact⟩
        have targetsExact :=
          closed_graph_collection_targets_normalized_all
            graph blockIndex nodeIndex collectionIndex
        rw [collectionExact] at targetsExact
        change
          collectionWithTargets collection
              (normalizeTargetList collection) =
            collection
        rw [targetsExact]
        exact collection_with_targets_self collection
      _ = node.edgeCollections := List.map_id node.edgeCollections
  have outerNormalized :=
    closed_graph_node_outer_collections_normalized
      graph blockIndex nodeIndex
  change
    normalizeOuterCollections node.edgeCollections =
      node.edgeCollections at outerNormalized
  change
    ({ payload := node.payload
       edgeCollections :=
        normalizeOuterCollections
          (node.edgeCollections.map normalizeCollection) } :
      CanonicalNode context.kindSchema) =
      node
  rw [normalizedCollections]
  rw [outerNormalized]

/-- Every closed block's full node list is fixed by material normalization. -/
theorem closed_graph_block_nodes_normalized
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length) :
    (graph.canonicalRegistry.get blockIndex).block.nodes.map
        normalizeMaterializedNode =
      (graph.canonicalRegistry.get blockIndex).block.nodes := by
  let nodes :=
    (graph.canonicalRegistry.get blockIndex).block.nodes
  calc
    nodes.map normalizeMaterializedNode =
        nodes.map id := by
      apply List.map_congr_left
      intro node nodeMember
      rcases List.get_of_mem nodeMember with
        ⟨nodeIndex, nodeExact⟩
      have normalized :=
        closed_graph_node_normalized
          graph blockIndex nodeIndex
      rw [nodeExact] at normalized
      exact normalized
    _ = nodes := List.map_id nodes

/-- The identity permutation pure-materializes every closed block to itself. -/
theorem pure_materialize_identity_closed_block
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length) :
    pureMaterializeCanonicalBlock
        (graph.canonicalRegistry.get blockIndex).block
        (identityPermutationWitness
          (graph.canonicalRegistry.get blockIndex).block.nodes.length) =
      (graph.canonicalRegistry.get blockIndex).block := by
  let block :=
    (graph.canonicalRegistry.get blockIndex).block
  have nodesNormalized :=
    closed_graph_block_nodes_normalized graph blockIndex
  change
    pureMaterializeCanonicalBlock block
        (identityPermutationWitness block.nodes.length) =
      block
  change block.nodes.map normalizeMaterializedNode =
    block.nodes at nodesNormalized
  cases formExact : block with
  | dagSingleton node =>
      simp only [
        formExact,
        Residua.RCC.Addressing.AddressedGraph.Foundation.CanonicalBlock.nodes,
        List.map_cons,
        List.map_nil,
        List.cons.injEq,
        and_true
      ] at nodesNormalized
      simp only [
        pureMaterializeCanonicalBlock,
        Residua.RCC.Addressing.AddressedGraph.Foundation.CanonicalBlock.nodes
      ]
      rw [permutation_bijection_identity]
      rw [relabel_node_identity, nodesNormalized]
  | cyclic nodes =>
      simp only [
        formExact,
        Residua.RCC.Addressing.AddressedGraph.Foundation.CanonicalBlock.nodes
      ] at nodesNormalized
      simp only [
        pureMaterializeCanonicalBlock,
        Residua.RCC.Addressing.AddressedGraph.Foundation.CanonicalBlock.nodes
      ]
      rw [permutation_bijection_identity]
      rw [relabel_nodes_identity, nodesNormalized]

/-- Target normalization only permutes the existing targets. -/
theorem normalize_target_list_permutation
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    IsPermutation
      (normalizeTargetList collection) collection.targets := by
  cases collection with
  | ordered =>
      exact .rfl
  | unordered label direction kind targets =>
      exact
        stable_sort_by_bytes_permutation
          (targetSortBytes
            (.unordered label direction kind targets))
          targets

/--
Normalize-after-relabel composes exactly with local bijection composition.
-/
theorem normalized_relabel_collection_compose
    (first second : LocalBijection n)
    (collection :
      EdgeCollection schema (ExternalRef schema)) :
    normalizedRelabeledCollection second
        (normalizedRelabeledCollection first collection) =
      normalizedRelabeledCollection
        (composeLocalBijection first second) collection := by
  cases collection with
  | ordered label direction kind targets =>
      simp [
        normalizedRelabeledCollection,
        relabelCollection,
        collectionWithTargets,
        normalizeTargetList,
        List.map_map,
        relabel_graph_ref_compose
      ]
  | unordered label direction kind targets =>
      unfold normalizedRelabeledCollection
      simp only [relabelCollection, collectionWithTargets]
      apply congrArg
        (Residua.RCC.Addressing.AddressedGraph.Foundation.EdgeCollection.unordered
          label direction kind)
      let firstCollection :
          EdgeCollection schema (ExternalRef schema) :=
        .unordered label direction kind
          (targets.map (relabelGraphRef first))
      have firstNormalizedPermutation :
          IsPermutation
            (normalizeTargetList firstCollection)
            firstCollection.targets :=
        normalize_target_list_permutation firstCollection
      have mappedPermutation :=
        firstNormalizedPermutation.map (relabelGraphRef second)
      have composedTargetsExact :
          firstCollection.targets.map (relabelGraphRef second) =
            targets.map
              (relabelGraphRef
                (composeLocalBijection first second)) := by
        change
          (targets.map (relabelGraphRef first)).map
              (relabelGraphRef second) =
            targets.map
              (relabelGraphRef
                (composeLocalBijection first second))
        rw [List.map_map]
        apply List.map_congr_left
        intro reference _referenceMember
        exact relabel_graph_ref_compose first second reference
      have targetPermutation :
          IsPermutation
            ((normalizeTargetList firstCollection).map
              (relabelGraphRef second))
            (targets.map
              (relabelGraphRef
                (composeLocalBijection first second))) :=
        mappedPermutation.trans
          (List.Perm.of_eq composedTargetsExact)
      simpa [firstCollection] using
        normalize_target_list_permutation_invariant
          (.unordered label direction kind targets)
          (by rfl)
          ((normalizeTargetList firstCollection).map
            (relabelGraphRef second))
          (targets.map
            (relabelGraphRef
              (composeLocalBijection first second)))
          targetPermutation

/-- Outer collection normalization only permutes its input collections. -/
theorem normalize_outer_collections_permutation
    (collections :
      List (EdgeCollection schema (ExternalRef schema))) :
    IsPermutation
      (normalizeOuterCollections collections) collections :=
  stable_sort_by_bytes_permutation collectionSortBytes collections

/--
Node material normalization commutes with sequential relabeling.
-/
theorem normalize_materialized_relabel_node_compose
    (first second : LocalBijection n)
    (node : CanonicalNode schema) :
    normalizeMaterializedNode
        (relabelNode second
          (normalizeMaterializedNode
            (relabelNode first node))) =
      normalizeMaterializedNode
        (relabelNode
          (composeLocalBijection first second) node) := by
  apply graph_node_eq_of_fields
  · rfl
  · have leftProjection :=
      normalize_materialized_relabel_node_collections
        second
        (normalizeMaterializedNode (relabelNode first node))
    have firstProjection :=
      normalize_materialized_relabel_node_collections
        first node
    have rightProjection :=
      normalize_materialized_relabel_node_collections
        (composeLocalBijection first second) node
    rw [leftProjection, firstProjection, rightProjection]
    let firstCollections :=
      node.edgeCollections.map
        (normalizedRelabeledCollection first)
    have firstOuterPermutation :
        IsPermutation
          (normalizeOuterCollections firstCollections)
          firstCollections :=
      normalize_outer_collections_permutation firstCollections
    have mappedPermutation :=
      firstOuterPermutation.map
        (normalizedRelabeledCollection second)
    have composedCollectionsExact :
        firstCollections.map
            (normalizedRelabeledCollection second) =
          node.edgeCollections.map
            (normalizedRelabeledCollection
              (composeLocalBijection first second)) := by
      unfold firstCollections
      rw [List.map_map]
      apply List.map_congr_left
      intro collection _collectionMember
      exact
        normalized_relabel_collection_compose
          first second collection
    apply normalize_outer_collections_permutation_invariant
    exact
      mappedPermutation.trans
        (List.Perm.of_eq composedCollectionsExact)

/-- Composing a local bijection with its inverse is identity. -/
theorem compose_local_bijection_inverse
    (bijection : LocalBijection n) :
    composeLocalBijection bijection
        (inverseLocalBijection bijection) =
      identityLocalBijection n := by
  apply local_bijection_ext
  intro index
  exact bijection.leftInverse index

/--
Normalized relabeling by an inverse recovers a normalized source node.
-/
theorem normalize_materialized_relabel_node_inverse
    (bijection : LocalBijection n)
    (leftNode rightNode : CanonicalNode schema)
    (rightExact :
      normalizeMaterializedNode
          (relabelNode bijection leftNode) =
        rightNode)
    (leftNormalized :
      normalizeMaterializedNode leftNode = leftNode) :
    normalizeMaterializedNode
        (relabelNode
          (inverseLocalBijection bijection) rightNode) =
      leftNode := by
  calc
    normalizeMaterializedNode
        (relabelNode
          (inverseLocalBijection bijection) rightNode) =
      normalizeMaterializedNode
        (relabelNode
          (inverseLocalBijection bijection)
          (normalizeMaterializedNode
            (relabelNode bijection leftNode))) := by
        rw [rightExact]
    _ = normalizeMaterializedNode
          (relabelNode
            (composeLocalBijection bijection
              (inverseLocalBijection bijection))
            leftNode) :=
      normalize_materialized_relabel_node_compose
        bijection (inverseLocalBijection bijection) leftNode
    _ = normalizeMaterializedNode
          (relabelNode (identityLocalBijection n) leftNode) := by
      rw [compose_local_bijection_inverse]
    _ = normalizeMaterializedNode leftNode := by
      rw [relabel_node_identity]
    _ = leftNode := leftNormalized

/-- Cardinality transport does not alter node relabeling semantics. -/
theorem relabel_node_transport_local_bijection
    {leftSize rightSize : Nat}
    (sizeExact : leftSize = rightSize)
    (bijection : LocalBijection leftSize)
    (node : GraphNode schema External) :
    relabelNode (transportLocalBijection sizeExact bijection) node =
      relabelNode bijection node := by
  subst rightSize
  rfl

/--
Pointwise exact forward transport and normalized source nodes yield exact
inverse transport of every target node.
-/
theorem normalized_inverse_node_exact_of_transport
    {leftNodes rightNodes : List (CanonicalNode schema)}
    (bijection :
      FiniteBijection leftNodes.length rightNodes.length)
    (rightNodesExact :
      ∀ leftIndex,
        normalizeMaterializedNode
            (relabelNode bijection.toLocalBijection
              (leftNodes.get leftIndex)) =
          rightNodes.get (bijection.forward leftIndex))
    (leftNodesNormalized :
      ∀ leftIndex,
        normalizeMaterializedNode (leftNodes.get leftIndex) =
          leftNodes.get leftIndex) :
    ∀ rightIndex,
      normalizeMaterializedNode
          (relabelNode bijection.symm.toLocalBijection
            (rightNodes.get rightIndex)) =
        leftNodes.get (bijection.symm.forward rightIndex) := by
  intro rightIndex
  let leftIndex := bijection.inverse rightIndex
  have forwardExact :
      bijection.forward leftIndex = rightIndex :=
    bijection.rightInverse rightIndex
  have rightNodeExact :
      normalizeMaterializedNode
          (relabelNode bijection.toLocalBijection
            (leftNodes.get leftIndex)) =
        rightNodes.get rightIndex := by
    simpa [forwardExact] using rightNodesExact leftIndex
  have inverseExact :=
    normalize_materialized_relabel_node_inverse
      bijection.toLocalBijection
      (leftNodes.get leftIndex)
      (rightNodes.get rightIndex)
      rightNodeExact
      (leftNodesNormalized leftIndex)
  have inverseBijectionExact :
      bijection.symm.toLocalBijection =
        transportLocalBijection bijection.size_eq
          (inverseLocalBijection bijection.toLocalBijection) :=
    bijection.symm_toLocalBijection_exact
  rw [inverseBijectionExact]
  rw [relabel_node_transport_local_bijection]
  simpa [leftIndex, FiniteBijection.symm] using inverseExact

/--
An exact normalized forward node transport produces the source block bytes as
an inverse pure-materialization candidate of the target block.
-/
theorem pure_materialize_inverse_encode_exact_of_normalized_nodes
    {leftBlock : CanonicalBlock schema leftKind}
    {rightBlock : CanonicalBlock schema rightKind}
    (nodeBijection :
      FiniteBijection leftBlock.nodes.length rightBlock.nodes.length)
    (formExact : leftBlock.form = rightBlock.form)
    (rightNodesExact :
      ∀ leftNodeIndex,
        normalizeMaterializedNode
            (relabelNode nodeBijection.toLocalBijection
              (leftBlock.nodes.get leftNodeIndex)) =
          rightBlock.nodes.get
            (nodeBijection.forward leftNodeIndex))
    (leftNodesNormalized :
      ∀ leftNodeIndex,
        normalizeMaterializedNode
            (leftBlock.nodes.get leftNodeIndex) =
          leftBlock.nodes.get leftNodeIndex) :
    encodeCanonicalBlock
        (pureMaterializeCanonicalBlock rightBlock
          nodeBijection.symm.toPermutationWitness) =
      encodeCanonicalBlock leftBlock := by
  apply
    pure_materialize_encode_exact_of_normalized_nodes
      nodeBijection.symm formExact.symm
  exact
    normalized_inverse_node_exact_of_transport
      nodeBijection rightNodesExact leftNodesNormalized

/--
The inverse node transport realizes the source block as a target-block
permutation candidate.
-/
theorem pure_materialize_inverse_transport_encode_exact
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    {transport : RegistryNodeTransport left right}
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (agreement :
      LowerRankCanonicalEnvironmentAgreement transport leftBlockIndex)
    (blockIsomorphic :
      BlockIsomorphic transport leftBlockIndex) :
    encodeCanonicalBlock
        (pureMaterializeCanonicalBlock
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftBlockIndex)).block
          (transport.nodeBijection
            leftBlockIndex).symm.toPermutationWitness) =
      encodeCanonicalBlock
        (left.canonicalRegistry.get leftBlockIndex).block := by
  apply
    pure_materialize_inverse_encode_exact_of_normalized_nodes
      (transport.nodeBijection leftBlockIndex)
      blockIsomorphic.formExact
  · intro leftNodeIndex
    exact
      node_transport_normalized_exact_of_lower_rank_agreement
        agreement (blockIsomorphic.nodes leftNodeIndex)
  · intro leftNodeIndex
    exact
      closed_graph_node_normalized
        left leftBlockIndex leftNodeIndex

/--
The bytes stored at a certified canonical minimum are no greater than
the bytes of any materialized permutation candidate.
-/
theorem stored_canonical_minimum_le_candidate
    {block : CanonicalBlock schema kind}
    (certificate : StoredAtCanonicalMinimum block)
    (permutation : PermutationWitness block.nodes.length) :
    compareGraphBytes
        (encodeCanonicalBlock block)
        (encodeCanonicalBlock
          (pureMaterializeCanonicalBlock block permutation)) ≠
      .gt := by
  have candidatesNonempty :
      certificate.allCandidateBytes ≠ [] := by
    rw [certificate.allCandidateBytesExact]
    exact pure_candidate_bytes_nonempty block
  have candidateMember :
      encodeCanonicalBlock
          (pureMaterializeCanonicalBlock block permutation) ∈
        certificate.allCandidateBytes := by
    rw [certificate.allCandidateBytesExact]
    unfold pureCanonicalCandidateBytes
    apply List.mem_map.mpr
    exact
      ⟨permutation,
        permutation_witnesses_complete permutation,
        rfl⟩
  have lowerBound :=
    lexicographic_minimum_lower_bound
      certificate.allCandidateBytes candidatesNonempty
      (encodeCanonicalBlock
        (pureMaterializeCanonicalBlock block permutation))
      candidateMember
  have storedMinimumExact :
      encodeCanonicalBlock block =
        lexicographicMinimum certificate.allCandidateBytes
          candidatesNonempty := by
    calc
      encodeCanonicalBlock block =
          encodeCanonicalBlock certificate.selectedMaterialization :=
        congrArg encodeCanonicalBlock
          certificate.storedEqualsSelectedMinimum
      _ = lexicographicMinimum certificate.allCandidateBytes
            candidatesNonempty :=
        certificate.selectedBytesAreMinimum
  rw [← storedMinimumExact] at lowerBound
  exact lowerBound

/--
The graph-byte comparison preorder is antisymmetric.
-/
theorem compare_graph_bytes_le_antisymmetric
    {left right : GraphBytes}
    (leftRight : compareGraphBytes left right ≠ .gt)
    (rightLeft : compareGraphBytes right left ≠ .gt) :
    left = right := by
  rcases compare_graph_bytes_trichotomy left right with
    leftLess | equal | leftGreater
  · have rightGreater :
        compareGraphBytes right left = .gt := by
      have swapped := compare_graph_bytes_swap left right
      simpa [leftLess, Ordering.swap] using swapped.symm
    exact False.elim (rightLeft rightGreater)
  · exact compare_graph_bytes_eq_iff.mp equal
  · exact False.elim (leftRight leftGreater)

/--
A singleton DAG block is fixed by every finite node transport.
-/
theorem pure_materialize_dag_fixed
    (graph : ClosedRootedGraph context)
    (blockIndex : Fin graph.canonicalRegistry.length)
    (bijection :
      FiniteBijection
        (graph.canonicalRegistry.get blockIndex).block.nodes.length
        targetSize)
    (node : CanonicalNode context.kindSchema)
    (blockExact :
      (graph.canonicalRegistry.get blockIndex).block =
        .dagSingleton node) :
    encodeCanonicalBlock
        (pureMaterializeCanonicalBlock
          (graph.canonicalRegistry.get blockIndex).block
          bijection.toPermutationWitness) =
      encodeCanonicalBlock
        (graph.canonicalRegistry.get blockIndex).block := by
  have sourceSizeExact :
      (graph.canonicalRegistry.get blockIndex).block.nodes.length =
        1 := by
    rw [blockExact]
    rfl
  have permutationIdentity :
      bijection.toPermutationWitness =
        identityPermutationWitness
          (graph.canonicalRegistry.get
            blockIndex).block.nodes.length := by
    apply permutation_witness_ext
    change
      bijection.toPermutationWitness.values =
        range
          (graph.canonicalRegistry.get
            blockIndex).block.nodes.length
    have permuted :=
      bijection.toPermutationWitness.permutesRange
    have rangeExact :
        range
            (graph.canonicalRegistry.get
              blockIndex).block.nodes.length =
          [0] := by
      calc
        range
            (graph.canonicalRegistry.get
              blockIndex).block.nodes.length =
            range 1 :=
          congrArg range sourceSizeExact
        _ = [0] := by rfl
    have singletonPermutation :
        IsPermutation
          bijection.toPermutationWitness.values [0] := by
      exact permuted.trans (List.Perm.of_eq rangeExact)
    exact singletonPermutation.eq_singleton.trans rangeExact.symm
  rw [permutationIdentity]
  exact
    congrArg encodeCanonicalBlock
      (pure_materialize_identity_closed_block graph blockIndex)

/--
Isomorphic blocks stored at their respective canonical minima have identical
canonical bytes.
-/
theorem block_encode_eq_of_isomorphic_canonical_minima
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftBlockIndex : Fin left.canonicalRegistry.length)
    (agreement :
      LowerRankCanonicalEnvironmentAgreement transport leftBlockIndex)
    (blockIsomorphic :
      BlockIsomorphic transport leftBlockIndex)
    (leftMinimum :
      BlockStoredAtCanonicalMinimum
        (left.canonicalRegistry.get leftBlockIndex).block)
    (rightMinimum :
      BlockStoredAtCanonicalMinimum
        (right.canonicalRegistry.get
          (transport.blockBijection.forward leftBlockIndex)).block) :
    encodeCanonicalBlock
        (left.canonicalRegistry.get leftBlockIndex).block =
      encodeCanonicalBlock
        (right.canonicalRegistry.get
          (transport.blockBijection.forward leftBlockIndex)).block := by
  have forwardCandidateExact :=
    pure_materialize_transport_encode_exact
      leftBlockIndex agreement blockIsomorphic
  have inverseCandidateExact :=
    pure_materialize_inverse_transport_encode_exact
      leftBlockIndex agreement blockIsomorphic
  cases leftMinimum with
  | dagTrivial leftNode leftBlockExact _leftWellFormed =>
      have leftCandidateFixed :=
        pure_materialize_dag_fixed
          left leftBlockIndex
          (transport.nodeBijection leftBlockIndex)
          leftNode leftBlockExact
      exact
        leftCandidateFixed.symm.trans
          forwardCandidateExact
  | cyclicSelected _leftWellFormed leftCertificate =>
      cases rightMinimum with
      | dagTrivial rightNode rightBlockExact _rightWellFormed =>
          have rightCandidateFixed :=
            pure_materialize_dag_fixed
              right
              (transport.blockBijection.forward leftBlockIndex)
              (transport.nodeBijection leftBlockIndex).symm
              rightNode rightBlockExact
          exact
            inverseCandidateExact.symm.trans
              rightCandidateFixed
      | cyclicSelected _rightWellFormed rightCertificate =>
          have leftLower :=
            stored_canonical_minimum_le_candidate
              leftCertificate
              (transport.nodeBijection
                leftBlockIndex).toPermutationWitness
          rw [forwardCandidateExact] at leftLower
          have rightLower :=
            stored_canonical_minimum_le_candidate
              rightCertificate
              (transport.nodeBijection
                leftBlockIndex).symm.toPermutationWitness
          rw [inverseCandidateExact] at rightLower
          exact
            compare_graph_bytes_le_antisymmetric
              leftLower rightLower

/--
When the transported candidate and both stored canonical minima have the same
bytes, the finite node transport fixes every local node index.
-/
theorem transported_node_indices_rigid_of_candidate_bytes
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (leftIndex : Fin left.canonicalRegistry.length)
    (transportedCandidateBytesExact :
      encodeCanonicalBlock
          (pureMaterializeCanonicalBlock
            (left.canonicalRegistry.get leftIndex).block
            ((transport.nodeBijection
              leftIndex).toPermutationWitness)) =
        encodeCanonicalBlock
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftIndex)).block)
    (blockBytesExact :
      encodeCanonicalBlock
          (left.canonicalRegistry.get leftIndex).block =
        encodeCanonicalBlock
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftIndex)).block) :
    ∀ leftNodeIndex,
      ((transport.nodeBijection leftIndex).forward
        leftNodeIndex).val =
      leftNodeIndex.val := by
  intro leftNodeIndex
  have minimum :=
    left.canonicalMinima
      (left.canonicalRegistry.get leftIndex)
      (list_get_mem_fin left.canonicalRegistry leftIndex)
  cases minimum with
  | dagTrivial node blockExact _wellFormed =>
      have leftCount :
          (left.canonicalRegistry.get
            leftIndex).block.nodes.length = 1 := by
        rw [blockExact]
        rfl
      have sizeExact :=
        (transport.nodeBijection leftIndex).size_eq
      have sourceBound := leftNodeIndex.isLt
      have targetBound :=
        ((transport.nodeBijection leftIndex).forward
          leftNodeIndex).isLt
      omega
  | cyclicSelected _wellFormed certificate =>
      let transportedPermutation :=
        (transport.nodeBijection
          leftIndex).toPermutationWitness
      let identityPermutation :=
        identityPermutationWitness
          (left.canonicalRegistry.get leftIndex).block.nodes.length
      have storedBytesSelected :
          encodeCanonicalBlock
              (left.canonicalRegistry.get leftIndex).block =
            encodeCanonicalBlock
              certificate.selectedMaterialization :=
        congrArg encodeCanonicalBlock
          certificate.storedEqualsSelectedMinimum
      have transportedBytesSelected :
          encodeCanonicalBlock
              (pureMaterializeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block
                transportedPermutation) =
            encodeCanonicalBlock
              certificate.selectedMaterialization := by
        calc
          encodeCanonicalBlock
              (pureMaterializeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block
                transportedPermutation) =
              encodeCanonicalBlock
                (right.canonicalRegistry.get
                  (transport.blockBijection.forward
                    leftIndex)).block :=
            transportedCandidateBytesExact
          _ = encodeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block :=
            blockBytesExact.symm
          _ = encodeCanonicalBlock
                certificate.selectedMaterialization :=
            storedBytesSelected
      have identityBytesSelected :
          encodeCanonicalBlock
              (pureMaterializeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block
                identityPermutation) =
            encodeCanonicalBlock
              certificate.selectedMaterialization := by
        calc
          encodeCanonicalBlock
              (pureMaterializeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block
                identityPermutation) =
              encodeCanonicalBlock
                (left.canonicalRegistry.get leftIndex).block :=
            congrArg encodeCanonicalBlock
              (pure_materialize_identity_closed_block
                left leftIndex)
          _ = encodeCanonicalBlock
                certificate.selectedMaterialization :=
            storedBytesSelected
      have transportedSelected :
          transportedPermutation =
            certificate.selectedPermutation :=
        certificate.selectedPermutationUniqueProducer
          transportedPermutation transportedBytesSelected
      have identitySelected :
          identityPermutation =
            certificate.selectedPermutation :=
        certificate.selectedPermutationUniqueProducer
          identityPermutation identityBytesSelected
      have permutationsExact :
          transportedPermutation = identityPermutation :=
        transportedSelected.trans identitySelected.symm
      have localBijectionsExact :
          (transport.nodeBijection leftIndex).toLocalBijection =
            identityLocalBijection
              (left.canonicalRegistry.get
                leftIndex).block.nodes.length := by
        calc
          (transport.nodeBijection
              leftIndex).toLocalBijection =
              permutationBijection transportedPermutation :=
            (FiniteBijection.permutationBijection_toPermutationWitness
              (transport.nodeBijection leftIndex)).symm
          _ = permutationBijection identityPermutation :=
            congrArg permutationBijection permutationsExact
          _ = identityLocalBijection
                (left.canonicalRegistry.get
                  leftIndex).block.nodes.length :=
            permutation_bijection_identity _
      calc
        ((transport.nodeBijection leftIndex).forward
            leftNodeIndex).val =
            ((transport.nodeBijection
              leftIndex).toLocalBijection.forward
                leftNodeIndex).val :=
          (FiniteBijection.toLocalBijection_forward_val
            (transport.nodeBijection leftIndex) leftNodeIndex).symm
        _ =
            ((identityLocalBijection
              (left.canonicalRegistry.get
                leftIndex).block.nodes.length).forward
                leftNodeIndex).val := by
          rw [localBijectionsExact]
        _ = leftNodeIndex.val := rfl

theorem stored_minimum_preserved_by_block_isomorphism
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right) :
    ∀ (leftIndex : Fin left.canonicalRegistry.length),
      LowerRankCanonicalEnvironmentAgreement transport leftIndex →
      BlockIsomorphic transport leftIndex →
      (BlockStoredAtCanonicalMinimum
          (left.canonicalRegistry.get leftIndex).block ↔
       BlockStoredAtCanonicalMinimum
          (right.canonicalRegistry.get
            (transport.blockBijection.forward leftIndex)).block) := by
  intro leftIndex _agreement _blockIsomorphic
  constructor
  · intro _leftMinimum
    exact
      right.canonicalMinima
        (right.canonicalRegistry.get
          (transport.blockBijection.forward leftIndex))
        (list_get_mem_fin right.canonicalRegistry
          (transport.blockBijection.forward leftIndex))
  · intro _rightMinimum
    exact
      left.canonicalMinima
        (left.canonicalRegistry.get leftIndex)
        (list_get_mem_fin left.canonicalRegistry leftIndex)

theorem stored_minima_preserved_by_graph_isomorphism
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context} :
    GraphIsomorphic left right →
    (EveryBlockStoredAtCanonicalMinimum left.canonicalRegistry ↔
     EveryBlockStoredAtCanonicalMinimum right.canonicalRegistry) := by
  intro _isomorphic
  constructor
  · intro _leftMinima
    exact right.canonicalMinima
  · intro _rightMinima
    exact left.canonicalMinima

end Residua.RCC.Addressing.AddressedGraph


import RCCTests.AddressedGraphCodec

/-! RCC-104 candidate: addressed-graph codec injectivity and ambient-free laws. -/

namespace Residua.RCC.RCC104Target

open Residua.RCC.Addressing.AddressedGraph.Codec.Tests
open Residua.RCC.Addressing.AddressedGraph

def tokenUtf8FlatMap := token_utf8_flatMap
def tokenToUtf8Data := token_toUTF8_data
def positiveCollectionImpossible := positive_collection_impossible
def positiveBlockWellFormed := positive_block_well_formed
def positiveRegistryWellFormed := positive_registry_well_formed
def positiveRegistryNoPublicOccurrence := positive_registry_has_no_public_occurrence
def ambiguousCanonicalLabelRefused := ambiguous_canonical_label_refusal
def canonicalCycleRetainsMinimum := canonical_two_cycle_retains_minimum
def detailedEncodeObservation := detailed_encode_observation_contract
def duplicateRefused := never_duplicate_refusal_contract
def registryKeysUnique := encoded_registry_keys_unique_contract
def domainExact := domain_exact_contract

abbrev TokenUtf8FlatMap : Prop :=
  ∀ tokens : List ByteToken,
    (tokens.map tokenChar).flatMap String.utf8EncodeChar =
      tokens.map tokenByte
abbrev TokenToUtf8Data : Prop :=
  ∀ tokens : List ByteToken,
    (String.toUTF8 (tokens.map tokenChar).asString).data.toList =
      tokens.map tokenByte
abbrev PositiveCollectionImpossible : Prop :=
  ∀ occurrence : CanonicalCollectionOccurrence positiveBlock.nodes, False
abbrev PositiveBlockWellFormed : Prop := CanonicalBlockWellFormed positiveBlock
abbrev PositiveRegistryWellFormed : Prop :=
  CanonicalRegistryWellFormed context positiveRegistry
abbrev PositiveRegistryNoPublicOccurrence : Prop :=
  ∀ occurrence : PublicReferenceOccurrence positiveRegistry, False
abbrev AmbiguousCanonicalLabelRefused : Prop :=
  residue ambiguousCanonicalLabelBytes = some .ambiguousCanonicalLabel
abbrev CanonicalCycleRetainsMinimum : Prop :=
  ∃ decoded,
    decodeCanonicalGraphDetailed context injective canonicalTwoCycleBytes =
      .ok decoded ∧
    EveryBlockStoredAtCanonicalMinimum decoded.canonicalRegistry
abbrev DetailedEncodeObservation : Prop :=
  ∀ (graph : ClosedRootedGraph context),
    ∃ decoded,
      decodeCanonicalGraphDetailed context injective
          (encodeCanonicalGraph context graph) = .ok decoded ∧
      serializedCanonicalProjection decoded =
        serializedCanonicalProjection graph
abbrev DuplicateRefused : Prop :=
  ∀ (graph : ClosedRootedGraph context),
    decodeCanonicalGraphDetailed context injective
        (encodeCanonicalGraph context graph) ≠
      .error .duplicateRegistryKey
abbrev RegistryKeysUnique : Prop :=
  ∀ (graph : ClosedRootedGraph context),
    EncodedRegistryKeys context
        (encodeCanonicalGraph context graph) =
      graph.canonicalRegistry.map
        (fun entry =>
          encodeCanonicalRegistryKey context entry.key) ∧
    NoDuplicates
      (EncodedRegistryKeys context
        (encodeCanonicalGraph context graph))
abbrev DomainExact : Prop :=
  ∀ (graph : ClosedRootedGraph context),
    ∃ decoded,
      decodeCanonicalGraphDetailed context injective
          (encodeCanonicalGraph context graph) = .ok decoded ∧
      CanonicalRegistryWellFormed
        context decoded.canonicalRegistry ∧
      validatePublicOccurrences
          decoded.canonicalRegistry decoded.registryKeysNoDup =
        .ok decoded.resolvedEdges ∧
      EveryBlockStoredAtCanonicalMinimum decoded.canonicalRegistry

structure Certificate where
  tokenUtf8FlatMap : TokenUtf8FlatMap
  tokenToUtf8Data : TokenToUtf8Data
  positiveCollectionImpossible : PositiveCollectionImpossible
  positiveBlockWellFormed : PositiveBlockWellFormed
  positiveRegistryWellFormed : PositiveRegistryWellFormed
  positiveRegistryNoPublicOccurrence : PositiveRegistryNoPublicOccurrence
  ambiguousCanonicalLabelRefused : AmbiguousCanonicalLabelRefused
  canonicalCycleRetainsMinimum : CanonicalCycleRetainsMinimum
  detailedEncodeObservation : DetailedEncodeObservation
  duplicateRefused : DuplicateRefused
  registryKeysUnique : RegistryKeysUnique
  domainExact : DomainExact

def certificate : Certificate where
  tokenUtf8FlatMap := token_utf8_flatMap
  tokenToUtf8Data := token_toUTF8_data
  positiveCollectionImpossible := positive_collection_impossible
  positiveBlockWellFormed := positive_block_well_formed
  positiveRegistryWellFormed := positive_registry_well_formed
  positiveRegistryNoPublicOccurrence := positive_registry_has_no_public_occurrence
  ambiguousCanonicalLabelRefused := ambiguous_canonical_label_refusal
  canonicalCycleRetainsMinimum := canonical_two_cycle_retains_minimum
  detailedEncodeObservation := detailed_encode_observation_contract
  duplicateRefused := never_duplicate_refusal_contract
  registryKeysUnique := encoded_registry_keys_unique_contract
  domainExact := domain_exact_contract

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC104Target

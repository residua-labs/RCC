import RCCTests.AddressedGraphClosure

/-! RCC-103 candidate: addressed-graph closure validator and residue coverage. -/

namespace Residua.RCC.RCC103Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph.Closure
open Residua.RCC.Addressing.AddressedGraph.Closure.Tests

def noncanonicalUnreachableRefused := fixture_noncanonical_unreachable
def notFoundMapped := validator_maps_not_found
def rehashMismatchMapped := validator_maps_rehash_mismatch
def decodeRefusalMapped := validator_maps_decode_refused
def emptyRegistryRefused := validator_refuses_empty_registry
def duplicateKeyRefused := validator_refuses_duplicate_typed_key
def missingRootRefused := validator_refuses_missing_root
def unreachableBlockRefused := validator_refuses_unreachable_registry_block
def localDagReferenceRefused := validator_refuses_local_reference_in_dag
def emptyCycleRefused := validator_refuses_empty_cyclic_block
def connectivityRequired := validator_requires_supplied_connectivity
def connectivityBeforeEvidence := validator_computes_connectivity_before_evidence
def localIndexBoundsRefused := validator_refuses_local_index_out_of_bounds
def localKindMismatchRefused := validator_refuses_local_expected_kind_mismatch
def targetKindCheckedFirst := validator_checks_target_kind_first
def unregisteredTargetRefused := validator_refuses_resolved_unregistered_target
def danglingChildRefused := validator_refuses_dangling_child
def danglingGrandchildRefused := validator_refuses_dangling_grandchild
def asymmetricResolutionRefused := validator_refuses_raw_one_resolved_two
def reverseAsymmetricResolutionRefused := validator_refuses_raw_two_resolved_one
def sameBlockSelfReferenceRefused := validator_refuses_same_block_external_self_reference
def externalCycleRefused := validator_refuses_two_block_external_cycle
def distinctPayloadCycleAccepted := validator_accepts_distinct_payload_two_node_local_cycle
def externalDagAccepted := validator_accepts_external_dag_chain
def externalDagClosed := external_dag_closed_is_evaluator_result
def externalDagOccurrenceExported := external_dag_chain_exports_resolved_occurrence
def acceptedCycleRetainsBounds := accepted_cycle_exposes_both_root_bounds

abbrev NoncanonicalUnreachableRefused : Prop :=
  ∀ (ingest : RawIngestProfile fixtureContext)
    (kind : fixtureContext.kindSchema.Kind)
    (requested : Address (fixtureContext.kindSchema.toAddressKind kind)),
    resolveAddressed
        (fixtureContext.blockBinding kind)
        (ingest.blockRuntimeCodec kind)
        (ingest.blockStore kind)
        requested ≠ .noncanonicalBytes
abbrev NotFoundMapped : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective notFoundIngest notFoundGraph =
    .error .externalBlockNotFound
abbrev RehashMismatchMapped : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective rehashIngest rehashMismatchGraph =
    .error .externalRehashMismatch
abbrev DecodeRefusalMapped : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective decodeRefusingIngest decodeRefusedGraph =
    .error .externalDecodeRefused
abbrev EmptyRegistryRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest emptyRegistryGraph =
    .error .emptyRegistry
abbrev DuplicateKeyRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest duplicateRegistryGraph =
    .error .duplicateBlockKey
abbrev MissingRootRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest rootNotInRegistryGraph =
    .error .rootNotInRegistry
abbrev UnreachableBlockRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest unreachableRegistryGraph =
    .error .unreachableRegistryBlock
abbrev LocalDagReferenceRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest localRefInDagGraph =
    .error .localRefInDag
abbrev EmptyCycleRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest emptyCyclicGraph =
    .error .emptyCyclicBlock
abbrev ConnectivityRequired : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest
        connectedMissingCertificateGraph =
    .error .connectivityCertificateMissing
abbrev ConnectivityBeforeEvidence : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest disconnectedCyclicGraph =
    .error .localConnectivityRefused
abbrev LocalIndexBoundsRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest localOutOfBoundsGraph =
    .error .localIndexOutOfBounds
abbrev LocalKindMismatchRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest localKindMismatchGraph =
    .error .targetKindMismatch
abbrev TargetKindCheckedFirst : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactFixtureIngest targetKindMismatchGraph =
    .error .targetKindMismatch
abbrev UnregisteredTargetRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactSourceTargetIngest
        resolvedButUnregisteredGraph =
    .error .externalTargetNotInRegistry
abbrev DanglingChildRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective notFoundIngest notFoundGraph =
    .error .externalBlockNotFound
abbrev DanglingGrandchildRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactSourceTargetIngest
        danglingGrandchildGraph =
    .error .externalBlockNotFound
abbrev AsymmetricResolutionRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective acceptedTwoTwoIngest
        rawOneResolvedTwoGraph =
    .error .rawTargetMemberIndexOutOfBounds
abbrev ReverseAsymmetricResolutionRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective
        (ingestWith (canonicalStore .syntax [sourceCanonical])
          emptyAddressedStore)
        rawTwoResolvedOneGraph =
    .error .resolvedCanonicalMemberIndexOutOfBounds
abbrev SameBlockSelfReferenceRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective
        (ingestWith (canonicalStore .syntax [sourceCanonical])
          emptyAddressedStore)
        sameBlockExternalSelfReferenceGraph =
    .error .crossBlockRankNotStrict
abbrev ExternalCycleRefused : Prop :=
  validateRawRootedGraph
      fixtureContext fixtureInjective exactSourceTargetIngest
        twoBlockExternalCycleGraph =
    .error .crossBlockRankNotStrict
abbrev DistinctPayloadCycleAccepted : Prop :=
  validationSucceeded
      (validateRawRootedGraph
        fixtureContext fixtureInjective acceptedTwoTwoIngest acceptedTwoTwoGraph) =
    true
abbrev ExternalDagAccepted : Prop :=
  externalDagValidationSucceeded
      (validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          externalDagChainGraph) = true
abbrev ExternalDagClosed : Prop :=
    validateRawRootedGraph
      fixtureContext fixtureInjective exactSourceTargetIngest
        externalDagChainGraph =
    .ok Residua.RCC.Addressing.AddressedGraph.Closure.Tests.externalDagClosed
abbrev ExternalDagOccurrenceExported : Prop :=
  ∃ closed :
      StructurallyClosedRootedGraph fixtureContext exactSourceTargetIngest,
    validateRawRootedGraph
        fixtureContext fixtureInjective exactSourceTargetIngest
          externalDagChainGraph = .ok closed ∧
      ∃ occurs :
          RawReferenceOccurs closed.rawGraph
            (refForBlock .syntax targetCanonical 0),
        let evidence :=
          closed.resolvedTarget
            (refForBlock .syntax targetCanonical 0) occurs
        evidence.target.targetEntryMember.wrapped ∈
            closed.rawGraph.blockRegistry ∧
          evidence.target.targetEntry.claimedBlockQ =
            (refForBlock .syntax targetCanonical 0).targetKey.claimedBlockQ ∧
          RawTargetMemberBound evidence.target ∧
          resolveAddressed
              (fixtureContext.blockBinding
                (refForBlock .syntax targetCanonical 0).kind)
              (exactSourceTargetIngest.blockRuntimeCodec
                (refForBlock .syntax targetCanonical 0).kind)
              (exactSourceTargetIngest.blockStore
                (refForBlock .syntax targetCanonical 0).kind)
              ((refForBlock .syntax targetCanonical 0).targetKey.claimedBlockQ.toAddress) =
            .resolved evidence.resolved.canonicalBlock ∧
          (refForBlock .syntax targetCanonical 0).rawTargetMemberIndex <
            evidence.resolved.canonicalBlock.nodes.length
abbrev AcceptedCycleRetainsBounds : Prop :=
  ∃ closed :
      StructurallyClosedRootedGraph fixtureContext acceptedTwoTwoIngest,
    validateRawRootedGraph
        fixtureContext fixtureInjective acceptedTwoTwoIngest
          acceptedTwoTwoGraph = .ok closed ∧
      RawTargetMemberBound closed.rootMember ∧
      closed.rawGraph.root.rawTargetMemberIndex <
        closed.rootResolved.canonicalBlock.nodes.length

structure Certificate where
  noncanonicalUnreachableRefused : NoncanonicalUnreachableRefused
  notFoundMapped : NotFoundMapped
  rehashMismatchMapped : RehashMismatchMapped
  decodeRefusalMapped : DecodeRefusalMapped
  emptyRegistryRefused : EmptyRegistryRefused
  duplicateKeyRefused : DuplicateKeyRefused
  missingRootRefused : MissingRootRefused
  unreachableBlockRefused : UnreachableBlockRefused
  localDagReferenceRefused : LocalDagReferenceRefused
  emptyCycleRefused : EmptyCycleRefused
  connectivityRequired : ConnectivityRequired
  connectivityBeforeEvidence : ConnectivityBeforeEvidence
  localIndexBoundsRefused : LocalIndexBoundsRefused
  localKindMismatchRefused : LocalKindMismatchRefused
  targetKindCheckedFirst : TargetKindCheckedFirst
  unregisteredTargetRefused : UnregisteredTargetRefused
  danglingChildRefused : DanglingChildRefused
  danglingGrandchildRefused : DanglingGrandchildRefused
  asymmetricResolutionRefused : AsymmetricResolutionRefused
  reverseAsymmetricResolutionRefused : ReverseAsymmetricResolutionRefused
  sameBlockSelfReferenceRefused : SameBlockSelfReferenceRefused
  externalCycleRefused : ExternalCycleRefused
  distinctPayloadCycleAccepted : DistinctPayloadCycleAccepted
  externalDagAccepted : ExternalDagAccepted
  externalDagClosed : ExternalDagClosed
  externalDagOccurrenceExported : ExternalDagOccurrenceExported
  acceptedCycleRetainsBounds : AcceptedCycleRetainsBounds

def certificate : Certificate where
  noncanonicalUnreachableRefused := fixture_noncanonical_unreachable
  notFoundMapped := validator_maps_not_found
  rehashMismatchMapped := validator_maps_rehash_mismatch
  decodeRefusalMapped := validator_maps_decode_refused
  emptyRegistryRefused := validator_refuses_empty_registry
  duplicateKeyRefused := validator_refuses_duplicate_typed_key
  missingRootRefused := validator_refuses_missing_root
  unreachableBlockRefused := validator_refuses_unreachable_registry_block
  localDagReferenceRefused := validator_refuses_local_reference_in_dag
  emptyCycleRefused := validator_refuses_empty_cyclic_block
  connectivityRequired := validator_requires_supplied_connectivity
  connectivityBeforeEvidence := validator_computes_connectivity_before_evidence
  localIndexBoundsRefused := validator_refuses_local_index_out_of_bounds
  localKindMismatchRefused := validator_refuses_local_expected_kind_mismatch
  targetKindCheckedFirst := validator_checks_target_kind_first
  unregisteredTargetRefused := validator_refuses_resolved_unregistered_target
  danglingChildRefused := validator_refuses_dangling_child
  danglingGrandchildRefused := validator_refuses_dangling_grandchild
  asymmetricResolutionRefused := validator_refuses_raw_one_resolved_two
  reverseAsymmetricResolutionRefused := validator_refuses_raw_two_resolved_one
  sameBlockSelfReferenceRefused := validator_refuses_same_block_external_self_reference
  externalCycleRefused := validator_refuses_two_block_external_cycle
  distinctPayloadCycleAccepted := validator_accepts_distinct_payload_two_node_local_cycle
  externalDagAccepted := validator_accepts_external_dag_chain
  externalDagClosed := external_dag_closed_is_evaluator_result
  externalDagOccurrenceExported := external_dag_chain_exports_resolved_occurrence
  acceptedCycleRetainsBounds := accepted_cycle_exposes_both_root_bounds

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC103Target

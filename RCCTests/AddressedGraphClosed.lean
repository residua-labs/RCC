import RCC.AddressedGraphClosed

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph
open Residua.RCC.Addressing.AddressedGraph.Foundation

namespace Residua.RCC.Addressing.AddressedGraph.Closed.Tests

/-! A concrete occurrence retains all six coordinates consumed by resolution. -/

def fixtureSchema : GraphKindSchema where
  Kind := Unit
  decideKindEq := fun left right => inferInstanceAs (Decidable (left = right))
  enumerate := [()]
  enumerateNoDuplicates := by
    intro left right leftBound rightBound equal
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

def text (value : String) : GraphText := ⟨value.toList⟩
def frame : ExactFrame GraphBytes (DigestPreimage GraphBytes) where
  encode := fun bytes => bytes
  encode_injective := fun equality => equality

def binding :
    DigestBinding .syntax GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"fixture"⟩
  domainQ := ⟨"block"⟩
  schemaQ := ⟨"v1"⟩
  frame := frame
  hash := fun _ => ⟨""⟩

def wire (_bytes : GraphBytes) : GraphWireAddress .syntax where
  algorithm := text "fixture"
  domainQ := text "block"
  schemaQ := text "v1"
  digest := text ""

theorem wire_refines (bytes : GraphBytes) :
    (wire bytes).toAddress = binding.address bytes := by rfl

def rootBinding :
    DigestBinding .implementation GraphBytes (DigestPreimage GraphBytes) where
  algorithm := ⟨"fixture"⟩
  domainQ := ⟨"root"⟩
  schemaQ := ⟨"v1"⟩
  frame := frame
  hash := fun bytes => ⟨reprStr bytes.canonicalBytes⟩

def context : GraphCodecContext where
  kindSchema := fixtureSchema
  BlockWire := DigestPreimage GraphBytes
  RootWire := DigestPreimage GraphBytes
  blockBinding := fun _ => binding
  blockWireAddress := fun _ => wire
  blockWireAddressRefines := fun _ => wire_refines
  rootBinding := rootBinding

def targetBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton { payload := 1, edgeCollections := [] }
def targetEntry : SomeCanonicalBlock context :=
  ⟨(), wire (encodeCanonicalBlock targetBlock), targetBlock⟩
def targetRef : ExternalRef fixtureSchema :=
  ⟨(), ⟨targetEntry.blockQ, 0⟩⟩
def sourceCollection :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .ordered (text "e") .outgoing () [.external targetRef]
def sourceNode : CanonicalNode fixtureSchema :=
  { payload := 2, edgeCollections := [sourceCollection] }
def sourceBlock : CanonicalBlock fixtureSchema () :=
  .dagSingleton sourceNode
def sourceEntry : SomeCanonicalBlock context :=
  ⟨(), wire (encodeCanonicalBlock sourceBlock), sourceBlock⟩
def registry : List (SomeCanonicalBlock context) :=
  [targetEntry, sourceEntry]

def occurrence : PublicReferenceOccurrence registry where
  sourceBlockIndex := 1
  sourceBlockBound := by decide
  sourceBlock := sourceEntry
  sourceBlockLookup := rfl
  sourceNodeIndex := 0
  sourceNodeBound := by decide
  sourceNode := sourceNode
  sourceNodeLookup := rfl
  owningCollectionIndex := 0
  owningCollection := sourceCollection
  owningCollectionLookup := rfl
  expectedTargetKind := ()
  expectedTargetKindExact := rfl
  ref := targetRef
  targetPosition := 0
  targetOccurrence := rfl

example : occurrence.sourceBlockIndex = 1 := rfl
example : occurrence.sourceNodeIndex = 0 := rfl
example : occurrence.owningCollectionIndex = 0 := rfl
example : occurrence.expectedTargetKind = () := rfl
example : occurrence.ref = targetRef := rfl
example : occurrence.targetPosition = 0 := rfl

/-! The resolver owns three distinct exact residues before dependency work. -/
example :
    PublicReferenceResolutionResidue.targetKindMismatch ≠
      .targetMissing := by decide
example :
    PublicReferenceResolutionResidue.targetMissing ≠
      .canonicalMemberIndexOutOfBounds := by decide
#check resolvePublicReferenceOccurrence
#check validatePublicOccurrences

theorem dependency_sound_contract
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique : CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    {certificate : DependencyCertificate table}
    (built : buildDependencyCertificate table = .ok certificate)
    (edge : ResolvedEdge registry keysUnique)
    (edgeMember : edge ∈ table.edges) :
    certificate.height edge.resolved.targetBlockIndex <
      certificate.height edge.occurrence.sourceBlockIndex :=
  build_dependency_sound built edge edgeMember

theorem dependency_complete_contract
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique : CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    (ranked :
      ∃ rank : Nat → Nat, ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex) :
    ∃ certificate,
      buildDependencyCertificate table = .ok certificate :=
  build_dependency_complete ranked

theorem dependency_cycle_exact_contract
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique : CanonicalRegistryKeysNoDup context registry}
    (table : ResolvedEdgeTable registry keysUnique) :
    buildDependencyCertificate table = .error .crossBlockCycle ↔
      ¬ ∃ rank : Nat → Nat, ∀ edge, edge ∈ table.edges →
        rank edge.resolved.targetBlockIndex <
          rank edge.occurrence.sourceBlockIndex :=
  build_dependency_cycle_iff table

theorem dependency_height_canonical_contract
    {context : GraphCodecContext}
    {registry : List (SomeCanonicalBlock context)}
    {keysUnique : CanonicalRegistryKeysNoDup context registry}
    {table : ResolvedEdgeTable registry keysUnique}
    {left right : DependencyCertificate table}
    (leftBuilt : buildDependencyCertificate table = .ok left)
    (rightBuilt : buildDependencyCertificate table = .ok right) :
    left.height = right.height :=
  build_dependency_height_canonical leftBuilt rightBuilt

/-! Isomorphism uses one registry transport and explicitly requires the
lower-rank environment agreement at the block theorem boundary. -/
theorem stored_minimum_transport_contract
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (transport : RegistryNodeTransport left right)
    (index : Fin left.canonicalRegistry.length)
    (agreement : LowerRankCanonicalEnvironmentAgreement transport index)
    (blockIso : BlockIsomorphic transport index) :
    (BlockStoredAtCanonicalMinimum
        (left.canonicalRegistry.get index).block ↔
      BlockStoredAtCanonicalMinimum
        (right.canonicalRegistry.get
          (transport.blockBijection.forward index)).block) :=
  stored_minimum_preserved_by_block_isomorphism
    transport index agreement blockIso

theorem stored_minima_graph_transport_contract
    {context : GraphCodecContext}
    {left right : ClosedRootedGraph context}
    (isomorphic : GraphIsomorphic left right) :
    (EveryBlockStoredAtCanonicalMinimum left.canonicalRegistry ↔
      EveryBlockStoredAtCanonicalMinimum right.canonicalRegistry) :=
  stored_minima_preserved_by_graph_isomorphism isomorphic

example (graph : ClosedRootedGraph context) :
    GraphIsomorphic graph graph :=
  GraphIsomorphic.refl graph

/-!
Relabeling a canonical cyclic block must normalize unordered target
occurrences again.  Without that second normalization, these two presentations
were distinct unique local minima of one graph-isomorphism orbit.
-/
namespace RelabelNormalizationMutant

def collection (targets : List Nat) :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .unordered (text "") .outgoing ()
    (targets.map GraphRef.local)

def node (targets : List Nat) : CanonicalNode fixtureSchema :=
  { payload := 0
    edgeCollections := [collection targets] }

def leftBlock : CanonicalBlock fixtureSchema () :=
  .cyclic [node [0, 0, 1], node [0, 0, 1]]

def rightBlock : CanonicalBlock fixtureSchema () :=
  .cyclic [node [0, 1, 1], node [0, 1, 1]]

def swap : PermutationWitness 2 where
  values := [1, 0]
  permutesRange := by decide

example :
    pureMaterializeCanonicalBlock leftBlock swap = rightBlock := by
  rfl

example :
    pureMaterializeCanonicalBlock rightBlock swap = leftBlock := by
  rfl

example :
    lexicographicMinimum
        (pureCanonicalCandidateBytes leftBlock)
        (pure_candidate_bytes_nonempty leftBlock) =
      lexicographicMinimum
        (pureCanonicalCandidateBytes rightBlock)
        (pure_candidate_bytes_nonempty rightBlock) := by
  decide

end RelabelNormalizationMutant

#check TargetAtTransport.external
#check target_at_transport_external_anchored

#print axioms encode_canonical_registry_key_injective
#print axioms canonical_registry_strict_order_implies_keys_no_dup
#print axioms validatePublicOccurrences
#print axioms target_at_transport_external_anchored
#print axioms stored_minimum_preserved_by_block_isomorphism
#print axioms stored_minima_preserved_by_graph_isomorphism
#print axioms build_dependency_sound
#print axioms build_dependency_complete
#print axioms build_dependency_cycle_iff
#print axioms build_dependency_height_canonical

end Residua.RCC.Addressing.AddressedGraph.Closed.Tests


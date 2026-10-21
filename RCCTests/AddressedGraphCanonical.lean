import RCC.AddressedGraphCanonical

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph
open Residua.RCC.Addressing.AddressedGraph.Closure

namespace Residua.RCC.Addressing.AddressedGraph.Canonical.Tests

set_option maxRecDepth 8192
set_option maxHeartbeats 2000000

/-! AK-6B block normalization uses concrete structural references. -/

inductive FixtureKind
  | syntax
  | judgment
  deriving DecidableEq

def fixtureKinds : List FixtureKind := [.syntax, .judgment]

def fixtureSchema : GraphKindSchema where
  Kind := FixtureKind
  decideKindEq := fun left right => inferInstanceAs (Decidable (left = right))
  enumerate := fixtureKinds
  enumerateNoDuplicates := by
    intro leftIndex rightIndex leftBound rightBound equalKinds
    have leftCases : leftIndex = 0 ∨ leftIndex = 1 := by
      simp [fixtureKinds] at leftBound
      omega
    have rightCases : rightIndex = 0 ∨ rightIndex = 1 := by
      simp [fixtureKinds] at rightBound
      omega
    rcases leftCases with rfl | rfl <;>
      rcases rightCases with rfl | rfl <;>
      simp [fixtureKinds] at equalKinds ⊢
  enumerateComplete := by
    intro kind
    cases kind <;> simp [fixtureKinds]
  kindCode := fun
    | FixtureKind.syntax => 0
    | FixtureKind.judgment => 1
  kindCodeInjective := by
    intro left right equal
    cases left <;> cases right <;> simp_all
  toAddressKind := fun
    | FixtureKind.syntax => .syntax
    | FixtureKind.judgment => .judgment
  toAddressKindInjective := by
    intro left right equal
    cases left <;> cases right <;> simp_all

def text (value : String) : GraphText := ⟨value.toList⟩

def address
    (kind : FixtureKind) (digest : String) :
    GraphWireAddress (fixtureSchema.toAddressKind kind) where
  algorithm := text ""
  domainQ := text ""
  schemaQ := text ""
  digest := text digest

def external
    (kind : FixtureKind) (digest : String) (index : Nat) :
    ExternalRef fixtureSchema where
  kind := kind
  target := ⟨address kind digest, index⟩

def r1 : GraphRef (ExternalRef fixtureSchema) :=
  .external (external FixtureKind.syntax "" 0)
def r2 : GraphRef (ExternalRef fixtureSchema) :=
  .external (external FixtureKind.syntax "" 1)

def ordered12 : EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .ordered (text "e") .outgoing FixtureKind.syntax [r1, r2]
def ordered21 : EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .ordered (text "e") .outgoing FixtureKind.syntax [r2, r1]
def unordered12 : EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .unordered (text "e") .outgoing FixtureKind.syntax [r1, r2]
def unordered21 : EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .unordered (text "e") .outgoing FixtureKind.syntax [r2, r1]
def unorderedRepeated :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .unordered (text "e") .outgoing FixtureKind.syntax [r1, r1]
def unorderedSingle :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  .unordered (text "e") .outgoing FixtureKind.syntax [r1]

example : normalizeTargetList ordered12 = [r1, r2] := rfl
example : normalizeTargetList ordered21 = [r2, r1] := rfl
example : normalizeTargetList unordered12 = normalizeTargetList unordered21 := by
  exact
    normalize_target_list_permutation_invariant
      unordered12 rfl [r1, r2] [r2, r1]
        (List.Perm.swap r2 r1 [])
example : (normalizeTargetList unorderedRepeated).length = 2 := by
  exact normalize_target_list_length unorderedRepeated

def blockWith
    (collections :
      List (EdgeCollection fixtureSchema (ExternalRef fixtureSchema))) :
    CanonicalBlock fixtureSchema FixtureKind.syntax :=
  .dagSingleton { payload := 7, edgeCollections := collections }

def normalizeCollection
    (collection :
      EdgeCollection fixtureSchema (ExternalRef fixtureSchema)) :
    EdgeCollection fixtureSchema (ExternalRef fixtureSchema) :=
  collectionWithTargets collection (normalizeTargetList collection)

def normalizedBlockWith
    (collections :
      List (EdgeCollection fixtureSchema (ExternalRef fixtureSchema))) :
    CanonicalBlock fixtureSchema FixtureKind.syntax :=
  blockWith
    (normalizeOuterCollections (collections.map normalizeCollection))

example :
    encodeCanonicalBlock (blockWith [ordered12]) ≠
      encodeCanonicalBlock (blockWith [ordered21]) := by decide
example :
    encodeCanonicalBlock (normalizedBlockWith [unordered12]) =
      encodeCanonicalBlock (normalizedBlockWith [unordered21]) := by decide
example :
    encodeCanonicalBlock
        (blockWith [(.unordered (text "e") .outgoing FixtureKind.syntax
          [r1, r1])]) ≠
      encodeCanonicalBlock
        (blockWith [(.unordered (text "e") .outgoing FixtureKind.syntax
          [r1])]) := by decide
example :
    encodeCanonicalBlock (blockWith [ordered12, ordered12]) ≠
      encodeCanonicalBlock (blockWith [ordered12]) := by decide
example :
    encodeCanonicalBlock (blockWith [ordered12]) ≠
      encodeCanonicalBlock
        (blockWith [.ordered (text "e") .incoming FixtureKind.syntax [r1, r2]]) := by
  decide
example :
    encodeCanonicalBlock (blockWith [ordered12]) ≠
      encodeCanonicalBlock
        (blockWith [.ordered (text "x") .outgoing FixtureKind.syntax [r1, r2]]) := by
  decide
example :
    encodeCanonicalBlock (blockWith [ordered12]) ≠
      encodeCanonicalBlock
        (blockWith [.ordered (text "e") .outgoing FixtureKind.judgment [r1, r2]]) := by
  decide

/-! Complete collection encodings, rather than only labels or addresses,
control the stable outer order and retain duplicate occurrences. -/
example :
    normalizeOuterCollections [ordered21, ordered12] =
      normalizeOuterCollections [ordered12, ordered21] :=
  normalize_outer_collections_permutation_invariant
    [ordered21, ordered12] [ordered12, ordered21]
      (List.Perm.swap ordered12 ordered21 [])
example :
    (normalizeOuterCollections [ordered12, ordered12]).length = 2 :=
  normalize_outer_collections_length [ordered12, ordered12]

/-! Exact public laws.  These call the real candidate encoder and retain one
lower-rank environment on both sides. -/
theorem candidate_encoding_definition_contract
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    candidateEncoding source env permutation =
      encodeCanonicalBlock (materializeCandidate source env permutation) :=
  rfl

theorem candidate_encoding_equivariant_contract
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    candidateEncoding
      (relabelValidatedSource source bijection)
      env (transportPermutation bijection permutation) =
    candidateEncoding source env permutation :=
  candidate_encoding_equivariant source env bijection permutation

theorem minimizer_count_invariant_contract
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount) :
    graphMinimizerCount (relabelValidatedSource source bijection) env =
      graphMinimizerCount source env :=
  minimizer_count_invariant source env bijection

theorem materialize_ref_total_contract
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (occurrence : RawExternalReferenceOccurrence source.candidate) :
    ∃ finalized, materializeRef source env occurrence = finalized :=
  materialize_ref_total source env occurrence

theorem materialize_candidate_relabel_contract
    (source : ValidatedRawSourceBlock closed)
    (env :
      TargetFinalizationEnv
        closed source.sourceEntry.entry.dependencyRank)
    (bijection : LocalBijection source.candidate.nodeCount)
    (permutation : PermutationWitness source.candidate.nodeCount) :
    materializeCandidate (relabelValidatedSource source bijection) env
        (transportPermutation bijection permutation) =
      materializeCandidate source env permutation :=
  materialize_candidate_commutes_with_source_relabeling
    source env bijection permutation

theorem canonical_label_map_left_inverse_contract
    (labels : CanonicalLabelMap raw canonical) :
    ∀ index, labels.inverse (labels.forward index) = index :=
  labels.leftInverse

theorem canonical_label_map_right_inverse_contract
    (labels : CanonicalLabelMap raw canonical) :
    ∀ index, labels.forward (labels.inverse index) = index :=
  labels.rightInverse

/-!
The defensive mismatch residue remains public, but this is the corrected
reachable-state contract: AK-5 exact resolution plus equality of the selected
and resolved blocks forces equality of the claimed and derived wire address.
-/
theorem claimed_block_address_mismatch_unreachable_contract
    {context : GraphCodecContext}
    {ingest : RawIngestProfile context}
    {kind : context.kindSchema.Kind}
    {claimed :
      GraphWireAddress (context.kindSchema.toAddressKind kind)}
    {selectedBlock resolvedBlock :
      CanonicalBlock context.kindSchema kind}
    (resolvedByAK5 :
      resolveAddressed
          (context.blockBinding kind)
          (ingest.blockRuntimeCodec kind)
          (ingest.blockStore kind)
          claimed.toAddress =
        .resolved resolvedBlock)
    (selectedEqualsResolved : selectedBlock = resolvedBlock) :
    claimed =
      context.blockWireAddress kind
        (encodeCanonicalBlock selectedBlock) :=
  claimed_block_address_mismatch_unreachable
    resolvedByAK5 selectedEqualsResolved

#check GraphCanonicalizationResidue.resolvedBlockRegistryMismatch
#check GraphCanonicalizationResidue.claimedBlockAddressMismatch
#check GraphCanonicalizationResidue.ambiguousCanonicalLabel
#check canonicalizeStructurallyClosed

variable {schema : GraphKindSchema} {sourceKind : schema.Kind}
variable (detached : RawBlockCandidate schema sourceKind)
#check_failure materializeCandidate detached
#check_failure candidateEncoding detached
#check_failure relabelEntireRegistryWithOneBijection
#check_failure transportWholeRegistryFinalizationEnvironment

#print axioms candidate_encoding_equivariant
#print axioms minimizer_count_invariant
#print axioms materialize_ref_total
#print axioms materialize_candidate_commutes_with_source_relabeling
#print axioms finalized_blockQ_derived
#print axioms finalized_blockQ_claimed

end Residua.RCC.Addressing.AddressedGraph.Canonical.Tests


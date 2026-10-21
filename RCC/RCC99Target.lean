import RCCTests.AddressedGraph

/-! RCC-99 candidate: concrete addressed-graph codec and root exactness. -/

namespace Residua.RCC.RCC99Target

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph
open Residua.RCC.Addressing.AddressedGraph.Tests

def seedPayloadsDistinct := concrete_seed_payloads_distinct
def graphBDecodes := concrete_graph_b_decodes
def graphBObservesSeed := concrete_graph_b_observes_seed
def graphADecodeEncode := concrete_graph_a_decode_encode
def graphBDecodeEncode := concrete_graph_b_decode_encode
def graphBytesEqIffIsomorphic := concrete_graph_bytes_eq_iff_isomorphic
def rootAddressEqIffIsomorphic := concrete_root_address_eq_iff_isomorphic
def rootAddressSound := concrete_root_address_sound
def rootAddressComplete := concrete_root_address_complete
def graphDecodeEncode := graph_decode_encode_contract
def nonisomorphicRootsDiffer := nonisomorphic_root_addresses_differ
def rootSoundnessFullInjectivity := root_soundness_full_injectivity_contract

abbrev SeedPayloadsDistinct : Prop :=
  (concreteSingletonNode 1).payload ≠
    (concreteSingletonNode 2).payload
abbrev GraphBDecodes : Prop :=
  decodeCanonicalGraphDetailed
      concreteContext concreteInjective
      (encodeCanonicalGraph concreteContext concreteGraphBSeed) =
    .ok concreteGraphB
abbrev GraphBObservesSeed : Prop :=
  serializedCanonicalProjection concreteGraphB =
    serializedCanonicalProjection concreteGraphBSeed
abbrev GraphADecodeEncode : Prop :=
  decodeGraphBytes concreteContext concreteInjective
      (encodeCanonicalGraph concreteContext concreteGraphA) =
    some
      (qAbs (closedRootedGraphDomain concreteContext)
        (closedRootedGraphAdequate concreteContext) ()
        concreteGraphA)
abbrev GraphBDecodeEncode : Prop :=
  decodeGraphBytes concreteContext concreteInjective
      (encodeCanonicalGraph concreteContext concreteGraphB) =
    some
      (qAbs (closedRootedGraphDomain concreteContext)
        (closedRootedGraphAdequate concreteContext) ()
        concreteGraphB)
abbrev GraphBytesEqIffIsomorphic : Prop :=
  encodeCanonicalGraph concreteContext concreteGraphA =
      encodeCanonicalGraph concreteContext concreteGraphB ↔
    GraphIsomorphic concreteGraphA concreteGraphB
abbrev RootAddressEqIffIsomorphic : Prop :=
  rootAddress concreteContext concreteGraphA =
      rootAddress concreteContext concreteGraphB ↔
    GraphIsomorphic concreteGraphA concreteGraphB
abbrev RootAddressSound : Prop :=
  ∀ equal :
    rootAddress concreteContext concreteGraphA =
      rootAddress concreteContext concreteGraphB,
    GraphIsomorphic concreteGraphA concreteGraphB
abbrev RootAddressComplete : Prop :=
  ∀ isomorphic : GraphIsomorphic concreteGraphA concreteGraphB,
    rootAddress concreteContext concreteGraphA =
      rootAddress concreteContext concreteGraphB
abbrev GraphDecodeEncode : Prop :=
  ∀ (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (graph : ClosedRootedGraph context),
    decodeGraphBytes context injective
        (encodeCanonicalGraph context graph) =
      some
        (qAbs (closedRootedGraphDomain context)
          (closedRootedGraphAdequate context) () graph)
abbrev NonisomorphicRootsDiffer : Prop :=
  ∀ (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (different : ¬ GraphIsomorphic left right),
    rootAddress context left ≠ rootAddress context right
abbrev RootSoundnessFullInjectivity : Prop :=
  ∀ (context : GraphCodecContext)
    (injective : GraphDigestInjective context)
    (left right : ClosedRootedGraph context)
    (equal : rootAddress context left = rootAddress context right),
    GraphIsomorphic left right

structure Certificate where
  seedPayloadsDistinct : SeedPayloadsDistinct
  graphBDecodes : GraphBDecodes
  graphBObservesSeed : GraphBObservesSeed
  graphADecodeEncode : GraphADecodeEncode
  graphBDecodeEncode : GraphBDecodeEncode
  graphBytesEqIffIsomorphic : GraphBytesEqIffIsomorphic
  rootAddressEqIffIsomorphic : RootAddressEqIffIsomorphic
  rootAddressSound : RootAddressSound
  rootAddressComplete : RootAddressComplete
  graphDecodeEncode : GraphDecodeEncode
  nonisomorphicRootsDiffer : NonisomorphicRootsDiffer
  rootSoundnessFullInjectivity : RootSoundnessFullInjectivity

def certificate : Certificate where
  seedPayloadsDistinct := concrete_seed_payloads_distinct
  graphBDecodes := concrete_graph_b_decodes
  graphBObservesSeed := concrete_graph_b_observes_seed
  graphADecodeEncode := concrete_graph_a_decode_encode
  graphBDecodeEncode := concrete_graph_b_decode_encode
  graphBytesEqIffIsomorphic := concrete_graph_bytes_eq_iff_isomorphic
  rootAddressEqIffIsomorphic := concrete_root_address_eq_iff_isomorphic
  rootAddressSound := concrete_root_address_sound
  rootAddressComplete := concrete_root_address_complete
  graphDecodeEncode := graph_decode_encode_contract
  nonisomorphicRootsDiffer := nonisomorphic_root_addresses_differ
  rootSoundnessFullInjectivity := root_soundness_full_injectivity_contract

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC99Target

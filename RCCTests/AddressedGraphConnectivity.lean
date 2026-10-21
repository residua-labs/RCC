import RCC.AddressedGraphConnectivity

open Residua.RCC.Addressing
open Residua.RCC.Addressing.AddressedGraph.Closure

namespace Residua.RCC.Addressing.AddressedGraph.Connectivity.Tests

/-! AK-6A local path and certificate contracts. -/

inductive FixtureKind | syntax | judgment deriving DecidableEq, Repr

def fixtureSchema : GraphKindSchema where
  Kind := FixtureKind
  decideKindEq := fun a b => inferInstance
  enumerate := [.syntax, .judgment]
  enumerateNoDuplicates := by
    intro i j hi hj e
    have hi' : i = 0 ∨ i = 1 := by simp at hi; omega
    have hj' : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp at e ⊢
  enumerateComplete := by intro k; cases k <;> simp
  kindCode := fun | .syntax => 0 | .judgment => 1
  kindCodeInjective := by intro a b e; cases a <;> cases b <;> simp_all
  toAddressKind := fun | .syntax => .syntax | .judgment => .judgment
  toAddressKindInjective := by intro a b e; cases a <;> cases b <;> simp_all

def text (scalars : List Char) : GraphText := { scalars }

structure TestExternal where
  address : GraphWireAddress .syntax
  deriving DecidableEq, Repr

abbrev TestNode := GraphNode fixtureSchema TestExternal

def ownerOutgoingSource : TestNode :=
  { payload := 10
    edgeCollections := [.ordered (text ['o']) .outgoing FixtureKind.syntax [.local 1]] }

def ownerOutgoingTarget : TestNode :=
  { payload := 11
    edgeCollections := [.ordered (text ['b']) .outgoing FixtureKind.syntax [.local 0]] }

/-! Both endpoint rules encode the same directed incidence relation. -/
def ownerOutgoingCycle : List TestNode := [ownerOutgoingSource, ownerOutgoingTarget]

def targetIncomingSource : TestNode :=
  { payload := 10
    edgeCollections := [.unordered (text ['i']) .incoming FixtureKind.syntax [.local 1]] }

def targetIncomingTarget : TestNode :=
  { payload := 11
    edgeCollections := [.unordered (text ['q']) .incoming FixtureKind.syntax [.local 0]] }

def targetIncomingCycle : List TestNode := [targetIncomingSource, targetIncomingTarget]

def disconnectedNodes : List TestNode :=
  [{ payload := 20, edgeCollections := [] }, { payload := 21, edgeCollections := [] }]

def pathSearchSucceeded
    (nodes : List TestNode) (source target : Nat) : Bool :=
  match findLocalPath nodes source target with
  | some _ => true
  | none => false

def connectivityBuildSucceeded (nodes : List TestNode) : Bool :=
  match buildConnectivityCertificate nodes with
  | .ok _ => true
  | .error _ => false

/-! Both endpoint ownership conventions are exercised by the concrete finder. -/
theorem owner_outgoing_path_is_found :
    pathSearchSucceeded ownerOutgoingCycle 0 1 = true := by
  rfl

theorem target_incoming_path_is_found :
    pathSearchSucceeded targetIncomingCycle 0 1 = true := by
  rfl

theorem owner_outgoing_cycle_is_computed_connected :
    connectivityBuildSucceeded ownerOutgoingCycle = true := by
  rfl

theorem target_incoming_cycle_is_computed_connected :
    connectivityBuildSucceeded targetIncomingCycle = true := by
  rfl

/-! Exact empty and disconnected refusal outcomes. -/
theorem empty_nodes_are_refused :
    buildConnectivityCertificate ([] : List TestNode) = .error .emptyBlock := by
  rfl

theorem disconnected_pair_is_refused :
    buildConnectivityCertificate disconnectedNodes = .error (.noPath 0 1) := by
  rfl

/-! The six theorem wrappers deliberately have the exact public types. -/
theorem find_local_path_sound_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)} {source target : Nat}
    {witness : LocalPathWitness nodes source target}
    (found : findLocalPath nodes source target = some witness) :
    LocalPath nodes source target :=
  find_local_path_sound found

theorem find_local_path_complete_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)} {source target : Nat}
    (path : LocalPath nodes source target) :
    ∃ witness, findLocalPath nodes source target = some witness :=
  find_local_path_complete path

theorem find_local_path_none_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)} {source target : Nat} :
    findLocalPath nodes source target = none ↔ ¬ LocalPath nodes source target :=
  find_local_path_none_iff

theorem connectivity_sound_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)}
    {certificate : ConnectivityCertificate nodes}
    (built : buildConnectivityCertificate nodes = .ok certificate) :
    StronglyConnected nodes :=
  build_connectivity_sound built

theorem connectivity_complete_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)}
    (connected : StronglyConnected nodes) :
    ∃ certificate, buildConnectivityCertificate nodes = .ok certificate :=
  build_connectivity_complete connected

theorem connectivity_refuses_contract
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)} :
    (∃ residue, buildConnectivityCertificate nodes = .error residue) ↔
      ¬ StronglyConnected nodes :=
  build_connectivity_refuses_iff

/-!
These constructor and projector contracts pin the exact connectivity
authority.  A Boolean countermodel cannot satisfy the inductive path or
proof-carrying witness surface.
-/
theorem owner_outgoing_local_edge :
    LocalEdge ownerOutgoingCycle 0 1 := by
  rfl

theorem two_vertex_consecutive_pair_exact :
    EveryConsecutivePair [0, 1] (LocalEdge ownerOutgoingCycle) ↔
      LocalEdge ownerOutgoingCycle 0 1 := by
  simp [EveryConsecutivePair]

def ownerOutgoingConstructorPath :
    LocalPath ownerOutgoingCycle 0 1 :=
  LocalPath.step owner_outgoing_local_edge
    (LocalPath.refl (by decide))

theorem local_path_constructor_elimination
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)}
    {source target : Nat}
    (path : LocalPath nodes source target) :
    (source = target ∧ source < nodes.length) ∨
      ∃ second,
        LocalEdge nodes source second ∧
          LocalPath nodes second target := by
  cases path with
  | refl bounded =>
      exact .inl ⟨rfl, bounded⟩
  | step edge tail =>
      exact .inr ⟨_, edge, tail⟩

def ownerOutgoingExactWitness :
    LocalPathWitness ownerOutgoingCycle 0 1 where
  vertices := [0, 1]
  startsAt := rfl
  endsAt := rfl
  allBounded := by
    intro member membership
    simp [ownerOutgoingCycle] at membership ⊢
    omega
  consecutiveEdges := by
    simp [EveryConsecutivePair]
    exact owner_outgoing_local_edge

theorem exact_witness_projects_all_fields :
    ownerOutgoingExactWitness.vertices = [0, 1] ∧
      ownerOutgoingExactWitness.vertices.head? = some 0 ∧
      ownerOutgoingExactWitness.vertices.getLast? = some 1 ∧
      (∀ member ∈ ownerOutgoingExactWitness.vertices,
        member < ownerOutgoingCycle.length) ∧
      EveryConsecutivePair ownerOutgoingExactWitness.vertices
        (LocalEdge ownerOutgoingCycle) := by
  exact
    ⟨rfl, ownerOutgoingExactWitness.startsAt,
      ownerOutgoingExactWitness.endsAt,
      ownerOutgoingExactWitness.allBounded,
      ownerOutgoingExactWitness.consecutiveEdges⟩

def stronglyConnectedIntro
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)}
    (nonempty : nodes ≠ [])
    (paths :
      ∀ source target,
        source < nodes.length →
        target < nodes.length →
        LocalPath nodes source target) :
    StronglyConnected nodes :=
  ⟨nonempty, paths⟩

theorem strongly_connected_elimination
    {schema : GraphKindSchema} {External : Type}
    {nodes : List (GraphNode schema External)}
    (connected : StronglyConnected nodes) :
    nodes ≠ [] ∧
      ∀ source target,
        source < nodes.length →
        target < nodes.length →
        LocalPath nodes source target :=
  connected

/-! Labels, addresses, collection mode, and multiplicity cannot be reachability inputs. -/
def incidenceVariant : List TestNode :=
  [{ payload := 999
     edgeCollections := [.unordered (text ['z']) .outgoing FixtureKind.judgment [.local 1, .local 1]] },
   { payload := 111
     edgeCollections := [.unordered (text ['y']) .outgoing FixtureKind.judgment [.local 0]] }]

/-! Labels, modes, payloads, target kinds, and multiplicity do not alter incidence. -/
theorem incidence_variant_is_computed_connected :
    connectivityBuildSucceeded incidenceVariant = true := by
  rfl

def externalRefWithDigest (digestScalar : Char) : TestExternal where
  address :=
    { algorithm := text ['f']
      domainQ := text ['s']
      schemaQ := text ['v', '1']
      digest := text [digestScalar] }

def externalAddressVariantA : List TestNode :=
  [{ payload := 10
     edgeCollections :=
       [.ordered (text ['o']) .outgoing .syntax
         [.local 1, .external (externalRefWithDigest 'a')]] },
   { payload := 11
     edgeCollections :=
       [.ordered (text ['b']) .outgoing .syntax
         [.local 0, .external (externalRefWithDigest 'a')]] }]

def externalAddressVariantB : List TestNode :=
  [{ payload := 10
     edgeCollections :=
       [.ordered (text ['o']) .outgoing .syntax
         [.local 1, .external (externalRefWithDigest 'z')]] },
   { payload := 11
     edgeCollections :=
       [.ordered (text ['b']) .outgoing .syntax
         [.local 0, .external (externalRefWithDigest 'z')]] }]

theorem external_address_a_local_edge :
    LocalEdge externalAddressVariantA 0 1 := by
  rfl

theorem external_address_b_local_edge :
    LocalEdge externalAddressVariantB 0 1 := by
  rfl

theorem local_edge_is_external_address_insensitive :
    LocalEdge externalAddressVariantA 0 1 ↔
      LocalEdge externalAddressVariantB 0 1 :=
  ⟨fun _ => external_address_b_local_edge,
    fun _ => external_address_a_local_edge⟩

theorem external_address_a_path : LocalPath externalAddressVariantA 0 1 := by
  exact
    LocalPath.step external_address_a_local_edge
      (LocalPath.refl (by decide))

theorem external_address_b_path : LocalPath externalAddressVariantB 0 1 := by
  exact
    LocalPath.step external_address_b_local_edge
      (LocalPath.refl (by decide))

theorem local_path_is_external_address_insensitive :
    LocalPath externalAddressVariantA 0 1 ↔
      LocalPath externalAddressVariantB 0 1 :=
  ⟨fun _ => external_address_b_path, fun _ => external_address_a_path⟩

theorem external_address_a_connected :
    StronglyConnected externalAddressVariantA := by
  cases built : buildConnectivityCertificate externalAddressVariantA with
  | error residue =>
      have succeeded :
          connectivityBuildSucceeded externalAddressVariantA = true := by
        rfl
      rw [connectivityBuildSucceeded, built] at succeeded
      contradiction
  | ok certificate =>
      exact build_connectivity_sound built

theorem external_address_b_connected :
    StronglyConnected externalAddressVariantB := by
  cases built : buildConnectivityCertificate externalAddressVariantB with
  | error residue =>
      have succeeded :
          connectivityBuildSucceeded externalAddressVariantB = true := by
        rfl
      rw [connectivityBuildSucceeded, built] at succeeded
      contradiction
  | ok certificate =>
      exact build_connectivity_sound built

theorem strong_connectivity_is_external_address_insensitive :
    StronglyConnected externalAddressVariantA ↔
      StronglyConnected externalAddressVariantB :=
  ⟨fun _ => external_address_b_connected,
    fun _ => external_address_a_connected⟩

/-! Reversing only the endpoint convention is an observable direction mutant. -/
def directionMutant : List TestNode :=
  [{ payload := 10
     edgeCollections := [.ordered (text ['o']) .incoming FixtureKind.syntax [.local 1]] },
   { payload := 11, edgeCollections := [] }]

theorem direction_mutant_is_refused :
    buildConnectivityCertificate directionMutant = .error (.noPath 0 1) := by
  rfl

/-! Both endpoint representations must return a path whenever the finder does. -/
theorem owner_outgoing_finder_is_sound
    {witness : LocalPathWitness ownerOutgoingCycle 0 1}
    (found : findLocalPath ownerOutgoingCycle 0 1 = some witness) :
    LocalPath ownerOutgoingCycle 0 1 :=
  find_local_path_sound_contract found

theorem target_incoming_finder_is_sound
    {witness : LocalPathWitness targetIncomingCycle 0 1}
    (found : findLocalPath targetIncomingCycle 0 1 = some witness) :
    LocalPath targetIncomingCycle 0 1 :=
  find_local_path_sound_contract found

#print axioms find_local_path_sound_contract
#print axioms find_local_path_complete_contract
#print axioms find_local_path_none_contract
#print axioms connectivity_sound_contract
#print axioms connectivity_complete_contract
#print axioms connectivity_refuses_contract
#print axioms local_edge_is_external_address_insensitive
#print axioms local_path_is_external_address_insensitive
#print axioms strong_connectivity_is_external_address_insensitive
#print axioms find_local_path_sound
#print axioms find_local_path_complete
#print axioms find_local_path_none_iff
#print axioms build_connectivity_sound
#print axioms build_connectivity_complete
#print axioms build_connectivity_refuses_iff

end Residua.RCC.Addressing.AddressedGraph.Connectivity.Tests


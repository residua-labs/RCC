import RCC.TransactionFootprint

/-!
# RCC-48 Sealed Transaction-Footprint Countermodels

The positive fixture seals all four singleton universes and derives the
existing `CompleteFootprint`.  Two adversarial families are load-bearing:

* an under-quotiented universe omits a real semantic coordinate;
* a complete universe is supplied, but the claimed footprint omits that
  coordinate.

Both families are rejected independently for reads, writes, effects, and
invariant domains.
-/

namespace Residua.RCC.TransactionFootprint.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability
open Residua.RCC.TransactionFootprint

inductive State
  | current
  deriving DecidableEq

inductive Slot
  | apply
  deriving DecidableEq

inductive Head
  | parent | successor
  deriving DecidableEq

inductive Judgment
  | update
  deriving DecidableEq

inductive OperationId
  | update
  deriving DecidableEq

inductive ReadDomain
  | account
  deriving DecidableEq

inductive WriteDomain
  | balance
  deriving DecidableEq

inductive EffectDomain
  | durableStore
  deriving DecidableEq

inductive InvariantDomain
  | nonnegative
  deriving DecidableEq

def proposal : Proposal Slot Head Judgment :=
  ⟨.apply, .parent, .update⟩

/-- Every singleton coordinate is semantically load-bearing. -/
def surface :
    TransactionSurface
      State Slot Head Judgment OperationId
        ReadDomain WriteDomain EffectDomain InvariantDomain where
  stateRoot := fun _ => .parent
  apply := fun _ _ => .current
  operationOf := fun _ => .update
  Reads := fun _ _ domain => domain = .account
  Writes := fun _ _ domain => domain = .balance
  Effects := fun _ _ domain => domain = .durableStore
  InvariantDomains := fun _ _ domain => domain = .nonnegative

def singletonUniverse {Domain : Type}
    (coordinate : Domain) :
    SealedDomainUniverse Domain where
  InUniverse := fun domain => domain = coordinate
  coordinates := [coordinate]
  coverage := {
    sound := by
      intro domain member
      simpa using member
    complete := by
      intro domain inUniverse
      simp [inUniverse]
  }

def emptyUniverse (Domain : Type) :
    SealedDomainUniverse Domain where
  InUniverse := fun _ => False
  coordinates := []
  coverage := {
    sound := by
      intro _ impossible
      cases impossible
    complete := by
      intro _ impossible
      cases impossible
  }

def fullUniverses :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := singletonUniverse .account
  writes := singletonUniverse .balance
  effects := singletonUniverse .durableStore
  invariantDomains := singletonUniverse .nonnegative

def fullFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := [.account]
  writes := [.balance]
  effects := [.durableStore]
  invariantDomains := [.nonnegative]

def fullSeal :
    UniverseCompleteFootprint
      surface .current proposal fullUniverses fullFootprint where
  reads := {
    semanticInUniverse := by
      intro domain semantic
      exact semantic
    claimedCovered := by
      intro domain claimed
      exact claimed
    classifiedAtCoordinate := by
      intro domain _
      simp [fullFootprint, surface]
  }
  writes := {
    semanticInUniverse := by
      intro domain semantic
      exact semantic
    claimedCovered := by
      intro domain claimed
      exact claimed
    classifiedAtCoordinate := by
      intro domain _
      simp [fullFootprint, surface]
  }
  effects := {
    semanticInUniverse := by
      intro domain semantic
      exact semantic
    claimedCovered := by
      intro domain claimed
      exact claimed
    classifiedAtCoordinate := by
      intro domain _
      simp [fullFootprint, surface]
  }
  invariantDomains := {
    semanticInUniverse := by
      intro domain semantic
      exact semantic
    claimedCovered := by
      intro domain claimed
      exact claimed
    classifiedAtCoordinate := by
      intro domain _
      simp [fullFootprint, surface]
  }

theorem sealed_fixture_derives_existing_exact_footprint :
    CompleteFootprint surface .current proposal fullFootprint :=
  fullSeal.toCompleteFootprint

theorem sealed_fixture_covers_all_four_semantic_coordinates :
    ReadDomain.account ∈ fullFootprint.reads ∧
      WriteDomain.balance ∈ fullFootprint.writes ∧
      EffectDomain.durableStore ∈ fullFootprint.effects ∧
      InvariantDomain.nonnegative ∈ fullFootprint.invariantDomains := by
  exact
    ⟨semantic_read_is_in_footprint fullSeal rfl,
      semantic_write_is_in_footprint fullSeal rfl,
      semantic_effect_is_in_footprint fullSeal rfl,
      semantic_invariant_is_in_footprint fullSeal rfl⟩

theorem sealed_fixture_claimed_coordinates_come_from_universes :
    fullUniverses.reads.InUniverse .account ∧
      fullUniverses.writes.InUniverse .balance ∧
      fullUniverses.effects.InUniverse .durableStore ∧
      fullUniverses.invariantDomains.InUniverse .nonnegative := by
  exact
    ⟨fullSeal.reads.claimedInUniverse (by simp [fullFootprint]),
      fullSeal.writes.claimedInUniverse (by simp [fullFootprint]),
      fullSeal.effects.claimedInUniverse (by simp [fullFootprint]),
      fullSeal.invariantDomains.claimedInUniverse (by simp [fullFootprint])⟩

/-! ## Under-quotiented sealed universes -/

def missingReadUniverse :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullUniverses with reads := emptyUniverse ReadDomain }

def missingWriteUniverse :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullUniverses with writes := emptyUniverse WriteDomain }

def missingEffectUniverse :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullUniverses with effects := emptyUniverse EffectDomain }

def missingInvariantUniverse :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullUniverses with invariantDomains := emptyUniverse InvariantDomain }

theorem underquotient_read_universe_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingReadUniverse fullFootprint) := by
  rintro ⟨sealed⟩
  exact sealed.reads.semanticInUniverse .account rfl

theorem underquotient_write_universe_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingWriteUniverse fullFootprint) := by
  rintro ⟨sealed⟩
  exact sealed.writes.semanticInUniverse .balance rfl

theorem underquotient_effect_universe_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingEffectUniverse fullFootprint) := by
  rintro ⟨sealed⟩
  exact sealed.effects.semanticInUniverse .durableStore rfl

theorem underquotient_invariant_universe_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingInvariantUniverse fullFootprint) := by
  rintro ⟨sealed⟩
  exact sealed.invariantDomains.semanticInUniverse .nonnegative rfl

/-! ## Complete universes with shortened claimed footprints -/

def missingReadFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullFootprint with reads := [] }

def missingWriteFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullFootprint with writes := [] }

def missingEffectFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullFootprint with effects := [] }

def missingInvariantFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { fullFootprint with invariantDomains := [] }

theorem omitted_semantic_read_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingReadFootprint) := by
  rintro ⟨sealed⟩
  have listed :
      ReadDomain.account ∈ missingReadFootprint.reads :=
    semantic_read_is_in_footprint sealed rfl
  cases listed

theorem omitted_semantic_write_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingWriteFootprint) := by
  rintro ⟨sealed⟩
  have listed :
      WriteDomain.balance ∈ missingWriteFootprint.writes :=
    semantic_write_is_in_footprint sealed rfl
  cases listed

theorem omitted_semantic_effect_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingEffectFootprint) := by
  rintro ⟨sealed⟩
  have listed :
      EffectDomain.durableStore ∈ missingEffectFootprint.effects :=
    semantic_effect_is_in_footprint sealed rfl
  cases listed

theorem omitted_semantic_invariant_cannot_certify :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingInvariantFootprint) := by
  rintro ⟨sealed⟩
  have listed :
      InvariantDomain.nonnegative ∈
        missingInvariantFootprint.invariantDomains :=
    semantic_invariant_is_in_footprint sealed rfl
  cases listed

#print axioms DomainFootprintSeal.claimedInUniverse
#print axioms DomainFootprintSeal.exact
#print axioms UniverseCompleteFootprint.toCompleteFootprint
#print axioms sealed_fixture_derives_existing_exact_footprint
#print axioms underquotient_read_universe_cannot_certify
#print axioms underquotient_write_universe_cannot_certify
#print axioms underquotient_effect_universe_cannot_certify
#print axioms underquotient_invariant_universe_cannot_certify
#print axioms omitted_semantic_read_cannot_certify
#print axioms omitted_semantic_write_cannot_certify
#print axioms omitted_semantic_effect_cannot_certify
#print axioms omitted_semantic_invariant_cannot_certify

end Residua.RCC.TransactionFootprint.Tests

import RCCTests.TransactionFootprint

/-! RCC-88 candidate: sealed transaction-footprint completeness. -/

namespace Residua.RCC.RCC88Target

open Residua.RCC.TransactionFootprint
open Residua.RCC.TransactionFootprint.Tests
open Residua.RCC.GlobalSerializability

def exactFootprint :
    CompleteFootprint surface .current proposal fullFootprint where
  readsExact := by
    intro domain
    cases domain
    change ReadDomain.account ∈ [ReadDomain.account] ↔
      ReadDomain.account = ReadDomain.account
    constructor
    · intro member
      rcases List.mem_cons.mp member with equal | impossible
      · exact equal
      · cases impossible
    · intro _
      exact List.Mem.head _
  writesExact := by
    intro domain
    cases domain
    change WriteDomain.balance ∈ [WriteDomain.balance] ↔
      WriteDomain.balance = WriteDomain.balance
    constructor
    · intro member
      rcases List.mem_cons.mp member with equal | impossible
      · exact equal
      · cases impossible
    · intro _
      exact List.Mem.head _
  effectsExact := by
    intro domain
    cases domain
    change EffectDomain.durableStore ∈ [EffectDomain.durableStore] ↔
      EffectDomain.durableStore = EffectDomain.durableStore
    constructor
    · intro member
      rcases List.mem_cons.mp member with equal | impossible
      · exact equal
      · cases impossible
    · intro _
      exact List.Mem.head _
  invariantDomainsExact := by
    intro domain
    cases domain
    change InvariantDomain.nonnegative ∈ [InvariantDomain.nonnegative] ↔
      InvariantDomain.nonnegative = InvariantDomain.nonnegative
    constructor
    · intro member
      rcases List.mem_cons.mp member with equal | impossible
      · exact equal
      · cases impossible
    · intro _
      exact List.Mem.head _

def coordinatesCovered :
    ReadDomain.account ∈ fullFootprint.reads ∧
      WriteDomain.balance ∈ fullFootprint.writes ∧
      EffectDomain.durableStore ∈ fullFootprint.effects ∧
      InvariantDomain.nonnegative ∈ fullFootprint.invariantDomains := by
  exact ⟨List.Mem.head _, List.Mem.head _, List.Mem.head _, List.Mem.head _⟩

def coordinatesFromUniverses :
    fullUniverses.reads.InUniverse .account ∧
      fullUniverses.writes.InUniverse .balance ∧
      fullUniverses.effects.InUniverse .durableStore ∧
      fullUniverses.invariantDomains.InUniverse .nonnegative := by
  exact ⟨rfl, rfl, rfl, rfl⟩

def footprintExact := exactFootprint
def footprintCoordinatesCovered := coordinatesCovered
def missingReadUniverseRefused := underquotient_read_universe_cannot_certify
def missingWriteUniverseRefused := underquotient_write_universe_cannot_certify
def missingEffectUniverseRefused := underquotient_effect_universe_cannot_certify
def missingInvariantUniverseRefused := underquotient_invariant_universe_cannot_certify
def omittedReadRefused := omitted_semantic_read_cannot_certify
def omittedWriteRefused := omitted_semantic_write_cannot_certify
def omittedEffectRefused := omitted_semantic_effect_cannot_certify
def omittedInvariantRefused := omitted_semantic_invariant_cannot_certify

structure Certificate where
  footprintExact :
    CompleteFootprint surface .current proposal fullFootprint
  footprintCoordinatesCovered :
    ReadDomain.account ∈ fullFootprint.reads ∧
      WriteDomain.balance ∈ fullFootprint.writes ∧
      EffectDomain.durableStore ∈ fullFootprint.effects ∧
      InvariantDomain.nonnegative ∈ fullFootprint.invariantDomains
  coordinatesFromUniverses :
    fullUniverses.reads.InUniverse .account ∧
      fullUniverses.writes.InUniverse .balance ∧
      fullUniverses.effects.InUniverse .durableStore ∧
      fullUniverses.invariantDomains.InUniverse .nonnegative
  missingReadUniverseRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingReadUniverse fullFootprint)
  missingWriteUniverseRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingWriteUniverse fullFootprint)
  missingEffectUniverseRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingEffectUniverse fullFootprint)
  missingInvariantUniverseRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal missingInvariantUniverse fullFootprint)
  omittedReadRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingReadFootprint)
  omittedWriteRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingWriteFootprint)
  omittedEffectRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingEffectFootprint)
  omittedInvariantRefused :
    ¬ Nonempty
      (UniverseCompleteFootprint
        surface .current proposal fullUniverses missingInvariantFootprint)

def certificate : Certificate where
  footprintExact := exactFootprint
  footprintCoordinatesCovered := coordinatesCovered
  coordinatesFromUniverses := coordinatesFromUniverses
  missingReadUniverseRefused := underquotient_read_universe_cannot_certify
  missingWriteUniverseRefused := underquotient_write_universe_cannot_certify
  missingEffectUniverseRefused := underquotient_effect_universe_cannot_certify
  missingInvariantUniverseRefused := underquotient_invariant_universe_cannot_certify
  omittedReadRefused := omitted_semantic_read_cannot_certify
  omittedWriteRefused := omitted_semantic_write_cannot_certify
  omittedEffectRefused := omitted_semantic_effect_cannot_certify
  omittedInvariantRefused := omitted_semantic_invariant_cannot_certify

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC88Target

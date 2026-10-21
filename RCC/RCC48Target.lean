import RCCTests.TransactionFootprint

/-!
# RCC-48 target package

This candidate packages complete sealed transaction footprints.  Every
semantic read/write/effect/invariant coordinate is covered, while empty or
under-quotiented universes are rejected independently.
-/

namespace Residua.RCC.RCC48Target

open Residua.RCC.TransactionFootprint
open Residua.RCC.TransactionFootprint.Tests
open Residua.RCC.GlobalSerializability

structure Certificate : Prop where
  exactFootprint : CompleteFootprint surface .current proposal fullFootprint
  allCoordinates :
    ReadDomain.account ∈ fullFootprint.reads ∧
      WriteDomain.balance ∈ fullFootprint.writes ∧
      EffectDomain.durableStore ∈ fullFootprint.effects ∧
      InvariantDomain.nonnegative ∈ fullFootprint.invariantDomains
  missingReadRefused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingReadUniverse fullFootprint)
  missingWriteRefused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingWriteUniverse fullFootprint)
  missingEffectRefused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingEffectUniverse fullFootprint)
  missingInvariantRefused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingInvariantUniverse fullFootprint)

def certificate : Certificate where
  exactFootprint := sealed_fixture_derives_existing_exact_footprint
  allCoordinates := sealed_fixture_covers_all_four_semantic_coordinates
  missingReadRefused := underquotient_read_universe_cannot_certify
  missingWriteRefused := underquotient_write_universe_cannot_certify
  missingEffectRefused := underquotient_effect_universe_cannot_certify
  missingInvariantRefused := underquotient_invariant_universe_cannot_certify

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC48Target

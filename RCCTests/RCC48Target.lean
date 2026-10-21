import RCC.RCC48Target

/-! Thin admission checks for RCC-48 complete transaction footprints. -/

namespace Residua.RCC.RCC48Target.Tests

open Residua.RCC.TransactionFootprint
open Residua.RCC.TransactionFootprint.Tests
open Residua.RCC.GlobalSerializability

theorem target_certificate_nonempty :
    Nonempty Certificate :=
  certificate_is_nonempty

theorem target_covers_all_semantic_coordinates :
    ReadDomain.account ∈ fullFootprint.reads ∧
      WriteDomain.balance ∈ fullFootprint.writes ∧
      EffectDomain.durableStore ∈ fullFootprint.effects ∧
      InvariantDomain.nonnegative ∈ fullFootprint.invariantDomains :=
  certificate.allCoordinates

theorem target_missing_read_refused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingReadUniverse fullFootprint) :=
  certificate.missingReadRefused

theorem target_missing_write_refused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingWriteUniverse fullFootprint) :=
  certificate.missingWriteRefused

theorem target_missing_effect_refused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingEffectUniverse fullFootprint) :=
  certificate.missingEffectRefused

theorem target_missing_invariant_refused :
    ¬ Nonempty (UniverseCompleteFootprint
      surface .current proposal missingInvariantUniverse fullFootprint) :=
  certificate.missingInvariantRefused

#print axioms target_certificate_nonempty
#print axioms target_covers_all_semantic_coordinates
#print axioms target_missing_read_refused
#print axioms target_missing_write_refused
#print axioms target_missing_effect_refused
#print axioms target_missing_invariant_refused

end Residua.RCC.RCC48Target.Tests

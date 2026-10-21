import RCCTests.FormalCoreInvalidationClosure

/-! RCC-14 candidate: invalidation reopens dependent judgments without rewriting history. -/

namespace Residua.RCC.RCC14Target

open Residua.RCC.InvalidationClosureTests

structure Certificate where
  transitiveSourceDetected :
    Invalidated demoSystem .sourceEdit .staleGreen
  staleGreenSelected :
    NeedsResolution demoSystem initialSnapshot .sourceEdit certifiedMode .staleGreen
  staleGreenReopened :
    invalidatedSnapshot.currentState .staleGreen = .reopened
  staleGreenCannotRemainUsable :
    invalidatedSnapshot.currentState .staleGreen ≠ .usable
  historicalValidityPreserved :
    invalidatedSnapshot.historicalValid .staleGreen = true
  projectionRecomputed :
    invalidatedSnapshot.projection = .newProjectionWithStaleReopened
  directOnlyMissesTransitiveSource :
    ¬ DirectInvalidated .sourceEdit .staleGreen
  directOnlyLeavesStaleGreenUsable :
    directOnlyMutant.currentState .staleGreen = .usable
  fullClosureRejectsDirectOnly :
    invalidatedSnapshot.currentState .staleGreen ≠
      directOnlyMutant.currentState .staleGreen
  fullRederiveSelectsUnrelated :
    NeedsResolution demoSystem initialSnapshot .sourceEdit .fullRederive
      .unrelatedGreen
  unrelatedStatePreserved :
    invalidatedSnapshot.currentState .unrelatedGreen = .usable

def certificate : Certificate where
  transitiveSourceDetected := transitive_closure_catches_source_edit
  staleGreenSelected := stale_green_is_required
  staleGreenReopened := stale_green_is_reopened
  staleGreenCannotRemainUsable := stale_green_cannot_remain_usable
  historicalValidityPreserved := historical_validity_is_immutable
  projectionRecomputed := projection_is_rederived
  directOnlyMissesTransitiveSource := direct_only_mutant_misses_transitive_source
  directOnlyLeavesStaleGreenUsable := direct_only_mutant_leaves_stale_green_usable
  fullClosureRejectsDirectOnly := full_closure_refuses_direct_only_mutant
  fullRederiveSelectsUnrelated := full_rederive_requires_unrelated_terminal
  unrelatedStatePreserved := unrelated_state_is_preserved_in_certified_mode

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC14Target

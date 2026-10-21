import RCCTests.ObservationCompleteness

/-! RCC-81 candidate: sealed observation-window completeness. -/

namespace Residua.RCC.RCC81Target

open Residua.RCC.ObservationCompleteness.Tests
open Residua.RCC.ObservationCompleteness

def bothEventsObserved := both_events_are_observed
def unsealedAuthorityRefused := unsealed_universe_has_no_coverage_authority
def unsealedCompletenessRefused := unsealed_universe_cannot_certify_completeness
def emptyScanRefused := empty_scan_does_not_prove_absence
def partialScanRefused := partial_scan_cannot_hide_beta
def unfaithfulObservationRefused := event_name_without_faithful_observation_is_not_coverage
def emptyScanRequiresEmptyScope := any_complete_empty_scan_forces_no_in_scope_event

structure Certificate where
  bothEventsObserved :
    ScopedObservationComplete sealedUniverse completeScan Faithful
  unsealedAuthorityRefused :
    FiniteEventUniverseSeal unsealedUniverse → False
  unsealedCompletenessRefused :
    ObservationCompletenessCertificate unsealedUniverse completeScan Faithful → False
  emptyScanRefused :
    ObservationCompletenessCertificate sealedUniverse emptyScan Faithful → False
  partialScanRefused :
    ObservationCompletenessCertificate sealedUniverse alphaOnlyScan Faithful → False
  unfaithfulObservationRefused :
    ObservationCompletenessCertificate sealedUniverse malformedScan Faithful → False
  emptyScanRequiresEmptyScope :
    ∀ (certificate : ObservationCompletenessCertificate sealedUniverse emptyScan Faithful),
      ∀ event, ¬ sealedUniverse.inScope event

def certificate : Certificate where
  bothEventsObserved := bothEventsObserved
  unsealedAuthorityRefused := unsealedAuthorityRefused
  unsealedCompletenessRefused := unsealedCompletenessRefused
  emptyScanRefused := emptyScanRefused
  partialScanRefused := partialScanRefused
  unfaithfulObservationRefused := unfaithfulObservationRefused
  emptyScanRequiresEmptyScope := emptyScanRequiresEmptyScope

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC81Target

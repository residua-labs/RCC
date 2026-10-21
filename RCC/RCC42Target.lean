import RCCTests.AdmissionLinearizer

/-!
# RCC-42 target package

This candidate packages the canonical admission-linearizer boundary: local
successes are not global finality, and one canonical slot/parent cannot carry
conflicting decisions.  The official registry is intentionally unchanged.
-/

namespace Residua.RCC.RCC42Target

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AdmissionLinearizer.RealizationTests

structure Certificate : Prop where
  globalInterface :
    globalLinearizer.finalize
        0 activatedState (activatedCanonicalSnapshot 0) activateRequest =
      .Ok (globallyActivated 0)
  sameSlotUnique :
    ∀ {firstVersion secondVersion : Nat}
      {firstState secondState :
        FencedWriterState Slot Head Judgment Generation}
      {firstRequest secondRequest :
        FencedFinalizeRequest
          Slot Head Judgment AuthorityEvidence Generation},
      (first :
        GloballySuccessfulFinalize
          globalLinearizer firstVersion firstState firstRequest) →
      (second :
        GloballySuccessfulFinalize
          globalLinearizer secondVersion secondState secondRequest) →
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot →
      firstState.generation = secondState.generation →
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent →
      judgmentEq.Equivalent
        firstRequest.authorization.proposal.judgment
        secondRequest.authorization.proposal.judgment
  localConflictRejected :
    ∀ (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Nat writerSpec judgmentEq)
      (firstVersion secondVersion : Nat)
      (activateCanonical :
        CanonicalWriterSnapshot linearizer firstVersion activatedState)
      (rollbackCanonical :
        CanonicalWriterSnapshot linearizer secondVersion rollbackState),
      False

def certificate : Certificate where
  globalInterface := global_interface_finalizes
  sameSlotUnique := by
    intro firstVersion secondVersion firstState secondState
      firstRequest secondRequest first second
      sameSlot sameGeneration sameParent
    exact globalLinearizer.atMostOneFinalized
      first second sameSlot sameGeneration sameParent
  localConflictRejected := conflicting_local_successes_cannot_both_be_globally_certified

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC42Target

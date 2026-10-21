import RCC.GlobalIntentCoverage
import RCCTests.CompositionGluing

/-! C3 candidate: local component and seam claims imply the declared global
    intent only through an explicit, one-way coverage contract. -/

namespace Residua.RCC.C3Target

open Residua.RCC.GlobalIntentCoverage
open Residua.RCC.CompositionGluing.Tests
open Residua.RCC.FacetCoherence

structure Certificate where
  positiveEvidence :
    CompositionClosureEvidence Positive.World
  positiveContract :
    CompositionIntentContract
      Positive.World
      Positive.World.componentClosed
      Positive.World.seamExact
      Positive.World.globalClosed
  positiveGlobalIntent : Positive.World.globalClosed
  falseIntentRefused :
    ¬ CompositionIntentContract
      Positive.World
      Positive.World.componentClosed
      Positive.World.seamExact
      False

def certificate : Certificate where
  positiveEvidence := integrated_local_evidence_constructs_c3_evidence
  positiveContract := Positive.globalContract
  positiveGlobalIntent :=
    integrated_local_evidence_constructs_c3_evidence.coversGlobalIntent
      Positive.globalContract
  falseIntentRefused := local_evidence_does_not_manufacture_false_global_intent

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.C3Target

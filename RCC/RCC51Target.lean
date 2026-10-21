import RCCTests.GlobalInvariant

/-!
# RCC-51 target package

This candidate binds the global invariant intent to the actual finalized cut
and records the mandatory-universe, footprint, partition, and caller-claim
countermodels.
-/

namespace Residua.RCC.RCC51Target

open Residua.RCC.GlobalInvariant.Tests
open Residua.RCC.GlobalInvariant
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.ConflictSerializability
open Residua.RCC.GlobalSerializability

structure Certificate : Prop where
  positive : GlobalIntent globalSerial.finalState
  mandatoryCoordinateRefused :
    ¬ Nonempty
      (MandatoryInvariantUniverse
        (emptyUniverse Residua.RCC.GlobalSerializability.Tests.InvariantDomain)
        Residua.RCC.GlobalInvariant.Tests.Mandatory)
  omittedFootprintRefused :
    ¬ Nonempty
      (InvariantPreservingExecution
        Residua.RCC.GlobalSerializability.Tests.Concrete.AuthorityEvidence
        Residua.RCC.GlobalSerializability.Tests.Concrete.Generation
        Residua.RCC.GlobalSerializability.Tests.Concrete.Epoch
        Residua.RCC.GlobalSerializability.Tests.Concrete.EffectSlot
        Residua.RCC.GlobalSerializability.Tests.Concrete.FailureName
        Residua.RCC.GlobalInvariant.Tests.invariantSurface
        Residua.RCC.GlobalSerializability.Tests.Concrete.finalizedHistory
        Residua.RCC.GlobalSerializability.Tests.Concrete.configLawful
          (emptyUniverse Residua.RCC.GlobalSerializability.Tests.InvariantDomain)
          Residua.RCC.GlobalInvariant.Tests.Claim
        Residua.RCC.GlobalSerializability.Tests.Concrete.Head.root0
          [Residua.RCC.GlobalSerializability.Tests.Concrete.Occurrence.setAtRoot0]
        Residua.RCC.GlobalSerializability.Tests.Concrete.Head.afterSet)
  localCutRefused :
    ¬ Nonempty
      (Residua.RCC.GlobalInvariant.FinalizedCutBinding
        Residua.RCC.GlobalInvariant.Tests.localSerial
        Residua.RCC.GlobalInvariant.Tests.globalCut)
  callerClaimRefused :
    ¬ Nonempty
      (Residua.RCC.GlobalInvariant.InvariantIntentContract
        Residua.RCC.GlobalInvariant.Tests.Mandatory
        Residua.RCC.GlobalInvariant.Tests.AlwaysTrueClaim
        Residua.RCC.GlobalInvariant.Tests.StrictIntent)

def certificate : Certificate where
  positive := actual_global_finalized_cut_satisfies_intent
  mandatoryCoordinateRefused := empty_universe_cannot_represent_mandatory_invariant
  omittedFootprintRefused := step_touching_omitted_invariant_cannot_enter_checked_execution
  localCutRefused := partition_local_history_cannot_bind_global_finalized_cut
  callerClaimRefused := caller_true_invariant_cannot_prove_strict_intent

theorem certificate_is_nonempty : Nonempty Certificate := ⟨certificate⟩

end Residua.RCC.RCC51Target

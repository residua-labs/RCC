import RCCTests.SupportClosure

/-! RCC-R5 candidate: mandatory support is a sealed, non-vacuous, exact
    projection and every support token is grounded at one snapshot. -/

namespace Residua.RCC.R5Target

open Residua.RCC.SupportClosure.Tests
open Residua.RCC.SupportClosure

structure Certificate where
  nonvacuous :
    ∃ node,
      RequiredAt system carrierFirst.value node ∧
        SupportClosureAt system snapshotFirst carrierFirst node
  forgedRootRejected :
    ∀ witness : RootWitnessAt system snapshotFirst carrierFirst Node.root,
      witness.certificate ≠ RootCertificate.forged
  emptyMandatoryRejected :
    ¬ Nonempty
      (MandatorySupportProjectionAt emptyMandatorySystem carrierFirst.value)
  partialMandatoryRejected :
    ¬ Nonempty
      (MandatorySupportProjectionAt partialMandatorySystem carrierFirst.value)
  emptySupportRejected :
    ¬ Nonempty
      (MandatorySupportProjectionAt emptySupportSystem carrierFirst.value)
  cycleRejected :
    ¬ (Nonempty
          (RuleWitnessAt twoCycleSystem snapshotFirst carrierFirst Node.derived) ∧
        Nonempty
          (RuleWitnessAt twoCycleSystem snapshotFirst carrierFirst Node.leaf))
  staleSnapshotRejected :
    ¬ ∃ witness : RootWitnessAt system snapshotFirst carrierFirst Node.root,
      witness.observedSnapshot = snapshotSecond ∧
        SupportClosureAt system snapshotFirst carrierFirst Node.root

def certificate : Certificate where
  nonvacuous := positive_support_is_nonvacuous
  forgedRootRejected := forged_root_flag_cannot_bypass_checker
  emptyMandatoryRejected := empty_mandatory_universe_cannot_seal
  partialMandatoryRejected := partial_mandatory_universe_cannot_seal
  emptySupportRejected := live_mandatory_cannot_project_empty_support
  cycleRejected := concrete_two_cycle_cannot_have_both_rules
  staleSnapshotRejected := cross_snapshot_closure_token_rejected

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.R5Target

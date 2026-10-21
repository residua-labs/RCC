import RCCTests.SupportClosure

/-! RCC-69 candidate: grounded support closure and non-vacuity boundaries. -/

namespace Residua.RCC.RCC69Target

open Residua.RCC.SupportClosure
open Residua.RCC.SupportClosure.Tests

def positiveSupportNonvacuous := positive_support_is_nonvacuous
def forgedRootRefused := forged_root_flag_cannot_bypass_checker
def unsoundAlwaysTrueCheckerRefused := always_true_checker_has_no_soundness
def emptyMandatorySealRefused := empty_mandatory_universe_cannot_seal
def partialMandatorySealRefused := partial_mandatory_universe_cannot_seal
def emptyLiveSupportRefused := live_mandatory_cannot_project_empty_support
def rootlessLeafRefused := rootless_leaf_cannot_close
def selfLoopRefused := self_loop_cannot_have_checked_rule
def twoCycleRefused := concrete_two_cycle_cannot_have_both_rules
def crossSnapshotRefused := cross_snapshot_closure_token_rejected

structure Certificate where
  positiveSupportNonvacuous :
    ∃ node,
      RequiredAt system carrierFirst.value node ∧
        SupportClosureAt system snapshotFirst carrierFirst node
  forgedRootRefused :
    ∀ (witness : RootWitnessAt system snapshotFirst carrierFirst Node.root),
      witness.certificate ≠ RootCertificate.forged
  unsoundAlwaysTrueCheckerRefused :
    ¬ ∀ carrier node certificate,
      alwaysTrueRoot carrier node certificate = true →
        impossibleRootClaim carrier node certificate
  emptyMandatorySealRefused :
    ¬ Nonempty (MandatorySupportProjectionAt emptyMandatorySystem carrierFirst.value)
  partialMandatorySealRefused :
    ¬ Nonempty (MandatorySupportProjectionAt partialMandatorySystem carrierFirst.value)
  emptyLiveSupportRefused :
    ¬ Nonempty (MandatorySupportProjectionAt emptySupportSystem carrierFirst.value)
  rootlessLeafRefused :
    ¬ SupportClosureAt system snapshotFirst carrierFirst Node.leaf
  selfLoopRefused :
    ¬ Nonempty (RuleWitnessAt selfLoopSystem snapshotFirst carrierFirst Node.derived)
  twoCycleRefused :
    ¬ (Nonempty (RuleWitnessAt twoCycleSystem snapshotFirst carrierFirst Node.derived) ∧
      Nonempty (RuleWitnessAt twoCycleSystem snapshotFirst carrierFirst Node.leaf))
  crossSnapshotRefused :
    ¬ ∃ witness : RootWitnessAt system snapshotFirst carrierFirst Node.root,
      witness.observedSnapshot = snapshotSecond ∧
        SupportClosureAt system snapshotFirst carrierFirst Node.root

def certificate : Certificate where
  positiveSupportNonvacuous := positive_support_is_nonvacuous
  forgedRootRefused := forged_root_flag_cannot_bypass_checker
  unsoundAlwaysTrueCheckerRefused := always_true_checker_has_no_soundness
  emptyMandatorySealRefused := empty_mandatory_universe_cannot_seal
  partialMandatorySealRefused := partial_mandatory_universe_cannot_seal
  emptyLiveSupportRefused := live_mandatory_cannot_project_empty_support
  rootlessLeafRefused := rootless_leaf_cannot_close
  selfLoopRefused := self_loop_cannot_have_checked_rule
  twoCycleRefused := concrete_two_cycle_cannot_have_both_rules
  crossSnapshotRefused := cross_snapshot_closure_token_rejected

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC69Target

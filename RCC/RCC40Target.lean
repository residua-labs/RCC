import RCCTests.QuorumIntersectionSafety

/-!
# RCC-40 target package

This candidate packages quorum-intersection safety as a fixture-level
law, and keeps the two-of-three split-vote countermodel as a refusal witness.
It does not turn a finite fixture into a production quorum extractor.
-/

namespace Residua.RCC.RCC40Target

open Residua.RCC.QuorumIntersectionSafety
open Residua.RCC.QuorumIntersectionSafety.Tests

structure Certificate : Prop where
  concreteSafe : QuorumIntersectionSafe twoOfTwo
  countermodel :
    AllowedFaultSet twoOfThree [.a] ∧
      HonestNonEquivocation twoOfThree splitVoteLocks [.a] ∧
      Nonempty (ValidQC twoOfThree splitVoteLocks .deploy .left) ∧
      Nonempty (ValidQC twoOfThree splitVoteLocks .deploy .right) ∧
      ¬ twoOfThree.equivalent .left .right ∧
      ¬ QuorumIntersectionSafe twoOfThree

def certificate : Certificate where
  concreteSafe := two_of_two_f_one_general_intersection_safe
  countermodel := two_of_three_double_sign_split_countermodel

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC40Target


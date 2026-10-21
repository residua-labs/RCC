import RCCTests.CommutativeJoin

/-!
# RCC-50 target package

This candidate packages the exact commutative-join checker over actual
finalized, state-basis-bound, footprint-sealed steps. One-sided, reused-
occurrence, and noncommuting false joins are refused.
-/

namespace Residua.RCC.RCC50Target

open Residua.RCC.CommutativeJoin
open Residua.RCC.CommutativeJoin.Tests
open Residua.RCC.GlobalSerializability

structure Certificate : Prop where
  checkerAdmits :
    verifyExactJoin concreteCandidate = .admit concreteCertificate
  tracesBound :
    Nonempty
        (SerialExecution
          (State := Residua.RCC.GlobalSerializability.Tests.Concrete.Head)
          (Slot := Residua.RCC.GlobalSerializability.Tests.Concrete.Slot)
          (Head := Residua.RCC.GlobalSerializability.Tests.Concrete.Head)
          (Judgment := Residua.RCC.GlobalSerializability.Tests.Concrete.Judgment)
          (OperationId := Residua.RCC.GlobalSerializability.Tests.OperationId)
          (ReadDomain := Residua.RCC.GlobalSerializability.Tests.ReadDomain)
          (WriteDomain := Residua.RCC.GlobalSerializability.Tests.WriteDomain)
          (EffectDomain := Residua.RCC.GlobalSerializability.Tests.EffectDomain)
          (InvariantDomain := Residua.RCC.GlobalSerializability.Tests.InvariantDomain)
          (Generation := Residua.RCC.GlobalSerializability.Tests.Concrete.Generation)
          (Epoch := Residua.RCC.GlobalSerializability.Tests.Concrete.Epoch)
          (EffectSlot := Residua.RCC.GlobalSerializability.Tests.Concrete.EffectSlot)
          (OccurrenceId := Residua.RCC.GlobalSerializability.Tests.Concrete.Occurrence)
          (FailureName := Residua.RCC.GlobalSerializability.Tests.Concrete.FailureName)
          (EventQ := Residua.RCC.GlobalSerializability.Tests.Concrete.EventQ)
          (Config := Unit)
          (AuthorityEvidence := Residua.RCC.GlobalSerializability.Tests.Concrete.AuthorityEvidence)
          Residua.RCC.GlobalSerializability.Tests.Concrete.concreteSurface
            Residua.RCC.GlobalSerializability.Tests.Concrete.finalizedHistory
            Residua.RCC.GlobalSerializability.Tests.Concrete.configLawful
            Residua.RCC.GlobalSerializability.Tests.Concrete.Head.root0
            Residua.RCC.CommutativeJoin.Tests.concreteLeftThenRight.occurrences
            Residua.RCC.CommutativeJoin.Tests.concreteLeftThenRight.finalState) ∧
      Nonempty
        (SerialExecution
          (State := Residua.RCC.GlobalSerializability.Tests.Concrete.Head)
          (Slot := Residua.RCC.GlobalSerializability.Tests.Concrete.Slot)
          (Head := Residua.RCC.GlobalSerializability.Tests.Concrete.Head)
          (Judgment := Residua.RCC.GlobalSerializability.Tests.Concrete.Judgment)
          (OperationId := Residua.RCC.GlobalSerializability.Tests.OperationId)
          (ReadDomain := Residua.RCC.GlobalSerializability.Tests.ReadDomain)
          (WriteDomain := Residua.RCC.GlobalSerializability.Tests.WriteDomain)
          (EffectDomain := Residua.RCC.GlobalSerializability.Tests.EffectDomain)
          (InvariantDomain := Residua.RCC.GlobalSerializability.Tests.InvariantDomain)
          (Generation := Residua.RCC.GlobalSerializability.Tests.Concrete.Generation)
          (Epoch := Residua.RCC.GlobalSerializability.Tests.Concrete.Epoch)
          (EffectSlot := Residua.RCC.GlobalSerializability.Tests.Concrete.EffectSlot)
          (OccurrenceId := Residua.RCC.GlobalSerializability.Tests.Concrete.Occurrence)
          (FailureName := Residua.RCC.GlobalSerializability.Tests.Concrete.FailureName)
          (EventQ := Residua.RCC.GlobalSerializability.Tests.Concrete.EventQ)
          (Config := Unit)
          (AuthorityEvidence := Residua.RCC.GlobalSerializability.Tests.Concrete.AuthorityEvidence)
          Residua.RCC.GlobalSerializability.Tests.Concrete.concreteSurface
            Residua.RCC.GlobalSerializability.Tests.Concrete.finalizedHistory
            Residua.RCC.GlobalSerializability.Tests.Concrete.configLawful
            Residua.RCC.GlobalSerializability.Tests.Concrete.Head.root0
            Residua.RCC.CommutativeJoin.Tests.concreteRightThenLeft.occurrences
            Residua.RCC.CommutativeJoin.Tests.concreteRightThenLeft.finalState) ∧
      Residua.RCC.CommutativeJoin.Tests.concreteLeftThenRight.finalState =
        Residua.RCC.CommutativeJoin.Tests.concreteRightThenLeft.finalState
  oneSidedRefused :
    verifyExactJoin oneSidedCandidate =
      .refuse .rightOperationOrderMismatch
  reusedOccurrenceRefused :
    verifyExactJoin reusedOccurrenceCandidate =
      .refuse .occurrenceNotRebased
  noncommutingRefused :
    verifyExactJoin noncommutingCandidate =
      .refuse .finalStateMismatch

def certificate : Certificate where
  checkerAdmits := executable_checker_admits_the_actual_exact_join
  tracesBound := admitted_join_contains_both_actual_rcc45_rcc47_rcc48_traces
  oneSidedRefused := exact_checker_rejects_one_sided_join
  reusedOccurrenceRefused := exact_checker_rejects_reused_occurrence
  noncommutingRefused := exact_checker_rejects_noncommuting_false_join

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC50Target

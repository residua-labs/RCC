import RCCTests.PrimitiveOperationalTotality

/-! RCC-78 candidate: primitive total-or-residue operational boundary. -/

namespace Residua.RCC.RCC78Target

open Residua.RCC.PrimitiveOperationalTotalityTests

def resultExhaustive (result : OpResult Unit DemoWake DemoResidue) :=
  op_result_exactly_four_statement_pin result
def primitiveBoundary := every_declared_primitive_has_four_way_boundary
def parametricBoundary := rcc18_parametric_boundary_statement_pin
def exhaustedFullyExhausted := exhausted_contract_is_fully_exhausted
def exhaustedReturnsResource := exhausted_contract_returns_resource_exhausted
def sourceScanOk := source_scan_returns_ok
def extractionAwaits := evidence_extraction_returns_await
def verificationRefuses := certificate_verification_returns_refuse
def resolutionExhausted := resolution_resource_limit_is_explicit
def measurementExhausted := binary_measurement_timeout_is_resource_exhausted
def appendRefuses := effect_append_exception_is_refused
def reconciliationOk := history_reconciliation_returns_ok
def exhaustionNotTruthRefutation :=
  Residua.RCC.PrimitiveOperationalTotalityTests.resource_exhaustion_does_not_refute_truth
def timeoutNotClosed := timeout_does_not_close_open_state
def timeoutNoWitness := timeout_produces_no_closed_witness
def silentTimeoutRejected := silent_timeout_countermodel_rejected
def lostExceptionRejected := exception_lost_countermodel_rejected
def timeoutRefutationRejected := timeout_as_refutation_countermodel_rejected
def classifierAccepted := canonical_classifier_is_accepted
def blindMutantRejected := contract_blind_mutant_cannot_meet_headline_precondition

/-!
The candidate is an explicit proof packet rather than a vacuous existential.
Each field names its exact operational claim, so callers cannot choose an
unrelated inhabited proposition while constructing the packet.
-/
structure Certificate where
  resultExhaustive :
    ∀ {A Wake Residue : Type}, (result : OpResult A Wake Residue) →
      (∃ value, result = .Ok value) ∨
        (∃ wake, result = .Await wake) ∨
        (∃ residue, result = .Refuse residue) ∨
        (∃ residue, result = .ResourceExhausted residue)
  primitiveBoundary :
    ∀ primitive : PrimitiveKind,
      (∃ value, execute demoFamily primitive demoContract () = .Ok value) ∨
        (∃ wake, execute demoFamily primitive demoContract () = .Await wake) ∨
        (∃ residue, execute demoFamily primitive demoContract () = .Refuse residue) ∨
        (∃ residue,
          execute demoFamily primitive demoContract () = .ResourceExhausted residue)
  parametricBoundary :
    ∀ primitive : PrimitiveKind,
      ((∃ value, execute demoFamily primitive exhaustedContract () = .Ok value) ∨
          (∃ wake, execute demoFamily primitive exhaustedContract () = .Await wake) ∨
          (∃ residue, execute demoFamily primitive exhaustedContract () = .Refuse residue) ∨
          (∃ residue,
            execute demoFamily primitive exhaustedContract () =
              .ResourceExhausted residue)) ∧
        (demoPolicy.insufficient primitive exhaustedContract →
          ∃ residue,
            execute demoFamily primitive exhaustedContract () = .ResourceExhausted residue)
  exhaustedFullyExhausted : exhaustedContract.FullyExhausted
  exhaustedReturnsResource :
    ∀ primitive : PrimitiveKind,
      execute demoFamily primitive exhaustedContract () =
        .ResourceExhausted .fuelDepleted
  sourceScanOk : execute demoFamily .SourceScan demoContract () = .Ok ()
  extractionAwaits :
    execute demoFamily .EvidenceExtraction demoContract () = .Await .sourceChanged
  verificationRefuses :
    execute demoFamily .CertificateVerification demoContract () =
      .Refuse .invalidCertificate
  resolutionExhausted :
    execute demoFamily .Resolution demoContract () =
      .ResourceExhausted .fuelDepleted
  measurementExhausted :
    execute demoFamily .BinaryMeasurement demoContract () =
      .ResourceExhausted .processTimeout
  appendRefuses :
    execute demoFamily .EffectAppend demoContract () = .Refuse .caughtException
  reconciliationOk :
    execute demoFamily .HistoryReconciliation demoContract () = .Ok ()
  exhaustionNotTruthRefutation :
    True ∧
      OpResult.IsResourceExhausted
        (execute demoFamily .Resolution demoContract ())
  timeoutNotClosed :
    ¬ (OpResult.IsResourceExhausted
          (execute demoFamily .BinaryMeasurement demoContract ()) →
        DemoClosed .open)
  timeoutNoWitness :
    OpResult.value?
        (classify
          (.ProcessTimeout .processTimeout :
            OperationalObservation DemoClosedWitness DemoWake DemoResidue)) =
      none
  silentTimeoutRejected :
    ¬ ClassifierConforms
      (silentTimeoutMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue))
  lostExceptionRejected :
    ¬ ClassifierConforms
      (exceptionLostMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue))
  timeoutRefutationRejected :
    ¬ ClassifierConforms
      (timeoutAsRefutationMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue))
  classifierAccepted :
    ClassifierConforms
      (canonicalCandidate
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue))
  blindMutantRejected :
    ∀ policy, ¬ LawfulPrimitiveFamily policy contractBlindFamily

def certificate : Certificate where
  resultExhaustive := @op_result_exactly_four_statement_pin
  primitiveBoundary := every_declared_primitive_has_four_way_boundary
  parametricBoundary := rcc18_parametric_boundary_statement_pin
  exhaustedFullyExhausted := exhaustedFullyExhausted
  exhaustedReturnsResource := exhausted_contract_returns_resource_exhausted
  sourceScanOk := sourceScanOk
  extractionAwaits := extractionAwaits
  verificationRefuses := verificationRefuses
  resolutionExhausted := resolutionExhausted
  measurementExhausted := measurementExhausted
  appendRefuses := appendRefuses
  reconciliationOk := reconciliationOk
  exhaustionNotTruthRefutation := exhaustionNotTruthRefutation
  timeoutNotClosed := timeoutNotClosed
  timeoutNoWitness := timeoutNoWitness
  silentTimeoutRejected := silentTimeoutRejected
  lostExceptionRejected := lostExceptionRejected
  timeoutRefutationRejected := timeoutRefutationRejected
  classifierAccepted := classifierAccepted
  blindMutantRejected := blindMutantRejected

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC78Target

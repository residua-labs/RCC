import RCC.PrimitiveOperationalTotality

/-!
# RCC-18 Primitive Operational Totality Witnesses

RED-first statement pins and adversarial countermodels for
`ResiduaRCCPrimitiveOperationalTotality`.

The production change that makes this file pass is a resource-bounded primitive family
whose observations are totalized into exactly `Ok`, `Await`, `Refuse`, or
`ResourceExhausted`.  In particular, timeout is not proposition refutation or closure,
and a classifier that drops timeout/exception observations or turns timeout into
refutation must be rejected.
-/

open Residua.RCC

namespace Residua.RCC.PrimitiveOperationalTotalityTests

inductive DemoWake
  | sourceChanged
  deriving DecidableEq

inductive DemoResidue
  | invalidCertificate
  | fuelDepleted
  | processTimeout
  | caughtException
  deriving DecidableEq

def demoContract : ResourceContract where
  fuel := 32
  deadlineTicks := 100
  searchBound := 16
  processTimeoutTicks := 20
  leaseTicks := 50

def exhaustedContract : ResourceContract where
  fuel := 0
  deadlineTicks := 0
  searchBound := 0
  processTimeoutTicks := 0
  leaseTicks := 0

/-- Frozen test policy: zero fuel is mechanically insufficient for every primitive. -/
def demoPolicy : ResourcePolicy where
  insufficient := fun _ contract => contract.fuel = 0
  fullyExhaustedInsufficient := fun _ _ exhausted => exhausted.1

/--
One concrete family exercises all seven primitives named by ADR §7.14 and all four
lawful result constructors.  Timeout and a caught exception remain explicit boundary
observations rather than disappearing control flow.
-/
def demoFamily : PrimitiveFamily where
  Input := fun _ => Unit
  Output := fun _ => Unit
  Wake := DemoWake
  Residue := DemoResidue
  observe := fun primitive contract _ =>
    if contract.fuel = 0 then
      .ResourceLimit .fuelDepleted
    else
      match primitive with
      | .SourceScan => .Completed ()
      | .EvidenceExtraction => .Waiting .sourceChanged
      | .CertificateVerification => .Rejected .invalidCertificate
      | .Resolution => .ResourceLimit .fuelDepleted
      | .BinaryMeasurement => .ProcessTimeout .processTimeout
      | .EffectAppend => .CaughtException .caughtException
      | .HistoryReconciliation => .Completed ()

/-- The demonstration family consumes the policy at the execution boundary. -/
def demoFamilyLawful : LawfulPrimitiveFamily demoPolicy demoFamily where
  resourceBound := by
    intro primitive contract input insufficient
    refine ⟨.fuelDepleted, ?_⟩
    exact if_pos insufficient

/-! ## Statement pins -/

/--
Pin the exact RCC-18 `OpResult` elimination surface.  Adding a fifth result or changing
the payload of any named constructor invalidates this theorem statement.
-/
theorem op_result_exactly_four_statement_pin
    {A : Type} {Wake : Type} {Residue : Type}
    (result : OpResult A Wake Residue) :
    (∃ value, result = .Ok value) ∨
      (∃ wake, result = .Await wake) ∨
      (∃ residue, result = .Refuse residue) ∨
      (∃ residue, result = .ResourceExhausted residue) := by
  exact OpResult.exhaustive result

/--
The raw Lean datatype still has an exhaustive four-way boundary; this statement is
deliberately not the RCC-18 resource-totality headline.
-/
theorem every_declared_primitive_has_four_way_boundary
    (primitive : PrimitiveKind) :
    (∃ value, execute demoFamily primitive demoContract () = .Ok value) ∨
      (∃ wake, execute demoFamily primitive demoContract () = .Await wake) ∨
      (∃ residue, execute demoFamily primitive demoContract () = .Refuse residue) ∨
      (∃ residue,
        execute demoFamily primitive demoContract () = .ResourceExhausted residue) := by
  exact primitive_result_boundary_exhaustive demoFamily primitive demoContract ()

/--
The RCC-18 headline is explicitly parametric in a supplied resource policy and a
load-bearing proof that insufficient contracts totalize as resource exhaustion.
-/
theorem rcc18_parametric_boundary_statement_pin
    (primitive : PrimitiveKind) :
    ((∃ value, execute demoFamily primitive exhaustedContract () = .Ok value) ∨
        (∃ wake, execute demoFamily primitive exhaustedContract () = .Await wake) ∨
        (∃ residue, execute demoFamily primitive exhaustedContract () = .Refuse residue) ∨
        (∃ residue,
          execute demoFamily primitive exhaustedContract () =
            .ResourceExhausted residue)) ∧
      (demoPolicy.insufficient primitive exhaustedContract →
        ∃ residue,
          execute demoFamily primitive exhaustedContract () =
            .ResourceExhausted residue) := by
  exact rcc18_parametric_boundary
    demoPolicy demoFamily demoFamilyLawful primitive exhaustedContract ()

theorem exhausted_contract_is_fully_exhausted :
    exhaustedContract.FullyExhausted := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem exhausted_contract_returns_resource_exhausted
    (primitive : PrimitiveKind) :
    execute demoFamily primitive exhaustedContract () =
      .ResourceExhausted .fuelDepleted := by
  rfl

theorem source_scan_returns_ok :
    execute demoFamily .SourceScan demoContract () = .Ok () := by
  rfl

theorem evidence_extraction_returns_await :
    execute demoFamily .EvidenceExtraction demoContract () =
      .Await .sourceChanged := by
  rfl

theorem certificate_verification_returns_refuse :
    execute demoFamily .CertificateVerification demoContract () =
      .Refuse .invalidCertificate := by
  rfl

theorem resolution_resource_limit_is_explicit :
    execute demoFamily .Resolution demoContract () =
      .ResourceExhausted .fuelDepleted := by
  rfl

theorem binary_measurement_timeout_is_resource_exhausted :
    execute demoFamily .BinaryMeasurement demoContract () =
      .ResourceExhausted .processTimeout := by
  rfl

theorem effect_append_exception_is_refused :
    execute demoFamily .EffectAppend demoContract () =
      .Refuse .caughtException := by
  rfl

theorem history_reconciliation_returns_ok :
    execute demoFamily .HistoryReconciliation demoContract () = .Ok () := by
  rfl

/-! ## Timeout/resource exhaustion is not semantic refutation or closure -/

/-- Resource exhaustion is constructively compatible with a true proposition. -/
theorem resource_exhaustion_does_not_refute_truth :
    True ∧
      OpResult.IsResourceExhausted
        (execute demoFamily .Resolution demoContract ()) := by
  exact resource_exhaustion_compatible_with
    (P := True) trivial
    (Wake := DemoWake) (Residue := DemoResidue) .fuelDepleted

inductive DemoState
  | open
  | closed
  deriving DecidableEq

def DemoClosed : DemoState → Prop
  | .open => False
  | .closed => True

/-- A timeout cannot manufacture `Closed` for a state known to be open. -/
theorem timeout_does_not_close_open_state :
    ¬ (OpResult.IsResourceExhausted
          (execute demoFamily .BinaryMeasurement demoContract ()) →
        DemoClosed .open) := by
  exact resource_exhaustion_does_not_close_open_state
    (closed := DemoClosed) (state := DemoState.open)
    (fun impossible => impossible)
    (Wake := DemoWake) (Residue := DemoResidue) .processTimeout

abbrev DemoClosedWitness := { state : DemoState // DemoClosed state }

/-- Timeout has no successful payload from which a closed-state witness could be read. -/
theorem timeout_produces_no_closed_witness :
    OpResult.value?
        (classify
          (.ProcessTimeout .processTimeout :
            OperationalObservation DemoClosedWitness DemoWake DemoResidue)) =
      none := by
  exact timeout_has_no_value
    (A := DemoClosedWitness) (Wake := DemoWake) (Residue := DemoResidue)
      .processTimeout

/-! ## Adversarial countermodels -/

/-- Silent-timeout mutant: the timeout observation disappears as `none`. -/
theorem silent_timeout_countermodel_rejected :
    ¬ ClassifierConforms
      (silentTimeoutMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue)) := by
  exact canonical_rejects_silent_timeout
    (A := Unit) (Wake := DemoWake) (Residue := DemoResidue) .processTimeout

/-- Exception-lost mutant: a caught exception disappears instead of becoming refusal. -/
theorem exception_lost_countermodel_rejected :
    ¬ ClassifierConforms
      (exceptionLostMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue)) := by
  exact canonical_rejects_exception_lost
    (A := Unit) (Wake := DemoWake) (Residue := DemoResidue) .caughtException

/-- Timeout-as-refutation mutant: timeout is mislabeled `Refuse` on the same residue. -/
theorem timeout_as_refutation_countermodel_rejected :
    ¬ ClassifierConforms
      (timeoutAsRefutationMutant
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue)) := by
  exact canonical_rejects_timeout_as_refutation
    (A := Unit) (Wake := DemoWake) (Residue := DemoResidue) .processTimeout

/-- The real total classifier satisfies the exact contract rejected by all three mutants. -/
theorem canonical_classifier_is_accepted :
    ClassifierConforms
      (canonicalCandidate
        (A := Unit) (Wake := DemoWake) (Residue := DemoResidue)) := by
  exact canonical_candidate_conforms

/-! ## Review mutant: contract-blind completion -/

/--
Mutant under review: it accepts a contract argument but ignores every field and always
reports completion, including under the fully exhausted contract.
-/
def contractBlindFamily : PrimitiveFamily where
  Input := fun _ => Unit
  Output := fun _ => Unit
  Wake := DemoWake
  Residue := DemoResidue
  observe := fun _ _ _ => .Completed ()

theorem contract_blind_mutant_completes_when_exhausted
    (primitive : PrimitiveKind) :
    execute contractBlindFamily primitive exhaustedContract () = .Ok () := by
  rfl

/--
The same mutant cannot supply the exact lawful-family precondition required by
`rcc18_parametric_boundary`.
-/
theorem contract_blind_mutant_cannot_meet_headline_precondition :
    ∀ policy, ¬ LawfulPrimitiveFamily policy contractBlindFamily :=
  fun policy lawful =>
    let insufficient :=
      policy.fullyExhaustedInsufficient
        .SourceScan exhaustedContract exhausted_contract_is_fully_exhausted
    let ⟨_, impossible⟩ :=
      lawful.resourceBound .SourceScan exhaustedContract () insufficient
    nomatch impossible

end Residua.RCC.PrimitiveOperationalTotalityTests

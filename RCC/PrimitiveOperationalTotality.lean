/-!
# RCC-18 Parametric Primitive Operational Boundary Kernel

Every primitive in ADR §7.14 receives an explicit finite resource contract and returns
exactly `Ok`, `Await`, `Refuse`, or `ResourceExhausted`.  Four-way datatype
exhaustiveness alone is not operational totality: the load-bearing theorem below also
requires a supplied resource policy and a `LawfulPrimitiveFamily` proof that every
policy-insufficient contract becomes `ResourceLimit`.

This kernel begins at the typed observation boundary.  It does not claim that an
arbitrary host function, subprocess, or network operation terminates.  A lawful
adapter must turn completion, waiting, rejection, resource exhaustion, process
timeout, and caught exceptions into `OperationalObservation`; uncaught exceptions,
silent timeout, unbounded loops, and hung subprocesses therefore cannot inhabit
`PrimitiveFamily`.

Consequently `rcc18_parametric_boundary` is an adapter-boundary theorem, not an
end-to-end discharge of RCC-18.  Runtime refinement showing that concrete host
adapters enforce their declared resource policy remains OPEN.

Prelude-only Lean 4.14; all proofs are closed without extra assumptions.
-/

namespace Residua.RCC

universe u v w x

/-- Finite bounds supplied to every primitive execution. -/
structure ResourceContract where
  fuel : Nat
  deadlineTicks : Nat
  searchBound : Nat
  processTimeoutTicks : Nat
  leaseTicks : Nat
  deriving DecidableEq, Repr

namespace ResourceContract

/-- No resource dimension is available.  Every policy must classify this as insufficient. -/
def FullyExhausted (contract : ResourceContract) : Prop :=
  contract.fuel = 0 ∧
    contract.deadlineTicks = 0 ∧
    contract.searchBound = 0 ∧
    contract.processTimeoutTicks = 0 ∧
    contract.leaseTicks = 0

end ResourceContract

/-- The complete primitive family named by ADR §7.14. -/
inductive PrimitiveKind
  | SourceScan
  | EvidenceExtraction
  | CertificateVerification
  | Resolution
  | BinaryMeasurement
  | EffectAppend
  | HistoryReconciliation
  deriving DecidableEq, Repr

/--
Parametric resource policy.  A concrete adapter chooses finer insufficiency rules, but
no policy may call a fully exhausted contract sufficient.
-/
structure ResourcePolicy where
  insufficient : PrimitiveKind → ResourceContract → Prop
  fullyExhaustedInsufficient :
    ∀ primitive contract,
      contract.FullyExhausted → insufficient primitive contract

/--
The exact operational result boundary.  There is deliberately no exception, timeout,
silent, skipped, or proposition-false constructor.
-/
inductive OpResult (A : Type u) (Wake : Type v) (Residue : Type w) where
  | Ok (value : A)
  | Await (wake : Wake)
  | Refuse (residue : Residue)
  | ResourceExhausted (residue : Residue)
  deriving DecidableEq, Repr

namespace OpResult

/-- Successful payload projection; non-success results cannot manufacture a value. -/
def value? : OpResult A Wake Residue → Option A
  | .Ok value => some value
  | .Await _ => none
  | .Refuse _ => none
  | .ResourceExhausted _ => none

/-- Proposition-level recognition of the resource-exhaustion constructor. -/
def IsResourceExhausted (result : OpResult A Wake Residue) : Prop :=
  ∃ residue, result = .ResourceExhausted residue

/-- Exhaustive elimination theorem pinning the four and only four constructors. -/
theorem exhaustive (result : OpResult A Wake Residue) :
    (∃ value, result = .Ok value) ∨
      (∃ wake, result = .Await wake) ∨
      (∃ residue, result = .Refuse residue) ∨
      (∃ residue, result = .ResourceExhausted residue) :=
  match result with
  | .Ok value => Or.inl ⟨value, rfl⟩
  | .Await wake => Or.inr (Or.inl ⟨wake, rfl⟩)
  | .Refuse residue => Or.inr (Or.inr (Or.inl ⟨residue, rfl⟩))
  | .ResourceExhausted residue =>
      Or.inr (Or.inr (Or.inr ⟨residue, rfl⟩))

end OpResult

/--
Boundary observations that a host adapter must totalize before entering RCC.
`CaughtException` is caught at the adapter boundary; an uncaught exception has no
constructor here and is not a lawful primitive.
-/
inductive OperationalObservation
    (A : Type u) (Wake : Type v) (Residue : Type w) where
  | Completed (value : A)
  | Waiting (wake : Wake)
  | Rejected (residue : Residue)
  | ResourceLimit (residue : Residue)
  | ProcessTimeout (residue : Residue)
  | CaughtException (residue : Residue)
  deriving DecidableEq, Repr

/-- The single real classifier from boundary observations to RCC-18 results. -/
def classify :
    OperationalObservation A Wake Residue → OpResult A Wake Residue
  | .Completed value => .Ok value
  | .Waiting wake => .Await wake
  | .Rejected residue => .Refuse residue
  | .ResourceLimit residue => .ResourceExhausted residue
  | .ProcessTimeout residue => .ResourceExhausted residue
  | .CaughtException residue => .Refuse residue

/--
A heterogeneous family: each named primitive may have its own input and output types,
but all share the explicit resource contract and the four-result boundary.
-/
structure PrimitiveFamily where
  Input : PrimitiveKind → Type u
  Output : PrimitiveKind → Type v
  Wake : Type w
  Residue : Type x
  observe : (primitive : PrimitiveKind) → ResourceContract → Input primitive →
    OperationalObservation (Output primitive) Wake Residue

/--
Load-bearing adapter law: every policy-insufficient contract produces an explicit
resource-limit observation.  A contract-blind family cannot inhabit this proposition.
-/
structure LawfulPrimitiveFamily
    (policy : ResourcePolicy) (family : PrimitiveFamily) : Prop where
  resourceBound :
    ∀ primitive contract input,
      policy.insufficient primitive contract →
        ∃ residue,
          family.observe primitive contract input = .ResourceLimit residue

/-- Execute only by classifying a total boundary observation. -/
def execute (family : PrimitiveFamily)
    (primitive : PrimitiveKind) (contract : ResourceContract)
    (input : family.Input primitive) :
    OpResult (family.Output primitive) family.Wake family.Residue :=
  classify (family.observe primitive contract input)

/--
Raw datatype exhaustiveness.  This theorem deliberately makes no resource-contract
claim and is not the RCC-18 headline.
-/
theorem primitive_result_boundary_exhaustive (family : PrimitiveFamily)
    (primitive : PrimitiveKind) (contract : ResourceContract)
    (input : family.Input primitive) :
    (∃ value, execute family primitive contract input = .Ok value) ∨
      (∃ wake, execute family primitive contract input = .Await wake) ∨
      (∃ residue, execute family primitive contract input = .Refuse residue) ∨
      (∃ residue,
        execute family primitive contract input = .ResourceExhausted residue) := by
  exact OpResult.exhaustive (execute family primitive contract input)

/--
Parametric RCC-18 boundary theorem.  Besides four-way result exhaustiveness, it emits
the concrete contract-use obligation: policy-insufficient execution is explicitly
`ResourceExhausted`.
-/
theorem rcc18_parametric_boundary
    (policy : ResourcePolicy) (family : PrimitiveFamily)
    (lawful : LawfulPrimitiveFamily policy family)
    (primitive : PrimitiveKind) (contract : ResourceContract)
    (input : family.Input primitive) :
    ((∃ value, execute family primitive contract input = .Ok value) ∨
        (∃ wake, execute family primitive contract input = .Await wake) ∨
        (∃ residue, execute family primitive contract input = .Refuse residue) ∨
        (∃ residue,
          execute family primitive contract input = .ResourceExhausted residue)) ∧
      (policy.insufficient primitive contract →
        ∃ residue,
          execute family primitive contract input = .ResourceExhausted residue) := by
  constructor
  · exact primitive_result_boundary_exhaustive family primitive contract input
  · intro insufficient
    rcases lawful.resourceBound primitive contract input insufficient with
      ⟨residue, observed⟩
    refine ⟨residue, ?_⟩
    exact congrArg classify observed

/-- Resource exhaustion is compatible with any proposition for which evidence exists. -/
theorem resource_exhaustion_compatible_with
    (P : Prop) (hP : P) {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    P ∧ OpResult.IsResourceExhausted
      (.ResourceExhausted residue : OpResult Unit Wake Residue) :=
  ⟨hP, ⟨residue, rfl⟩⟩

/-- There is no valid elimination from resource exhaustion to refutation of `True`. -/
theorem resource_exhaustion_does_not_refute_truth
    {Wake : Type v} {Residue : Type w} (residue : Residue) :
    ¬ (OpResult.IsResourceExhausted
          (.ResourceExhausted residue : OpResult Unit Wake Residue) →
        ¬ True) :=
  fun refutes => refutes ⟨residue, rfl⟩ trivial

/-- A resource result cannot establish `Closed` for a state already proved open. -/
theorem resource_exhaustion_does_not_close_open_state
    {State : Type u} (closed : State → Prop) (state : State)
    (hopen : ¬ closed state)
    {Wake : Type v} {Residue : Type w} (residue : Residue) :
    ¬ (OpResult.IsResourceExhausted
          (.ResourceExhausted residue : OpResult Unit Wake Residue) →
        closed state) :=
  fun closes => hopen (closes ⟨residue, rfl⟩)

/-- Resource exhaustion carries no successful payload, including no `Closed` witness. -/
theorem resource_exhaustion_has_no_value
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    OpResult.value?
        (.ResourceExhausted residue : OpResult A Wake Residue) = none :=
  rfl

/-- Process timeout is resource exhaustion and likewise carries no successful payload. -/
theorem timeout_has_no_value
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    OpResult.value?
        (classify
          (.ProcessTimeout residue :
            OperationalObservation A Wake Residue)) = none :=
  rfl

/-! ## Classifier conformance and adversarial candidates -/

/--
A host classifier conforms only when it returns the canonical result for every
observation.  `Option` exists solely on the candidate side so silence is expressible
and rejectable; lawful `execute` never returns `Option`.
-/
def ClassifierConforms
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (candidate : OperationalObservation A Wake Residue →
      Option (OpResult A Wake Residue)) : Prop :=
  ∀ observation, candidate observation = some (classify observation)

/-- Total candidate induced by the real classifier. -/
def canonicalCandidate
    {A : Type u} {Wake : Type v} {Residue : Type w} :
    OperationalObservation A Wake Residue →
      Option (OpResult A Wake Residue) :=
  fun observation => some (classify observation)

/-- Countermodel: process timeout silently produces no result. -/
def silentTimeoutMutant
    {A : Type u} {Wake : Type v} {Residue : Type w} :
    OperationalObservation A Wake Residue →
      Option (OpResult A Wake Residue)
  | .Completed value => some (.Ok value)
  | .Waiting wake => some (.Await wake)
  | .Rejected residue => some (.Refuse residue)
  | .ResourceLimit residue => some (.ResourceExhausted residue)
  | .ProcessTimeout _ => none
  | .CaughtException residue => some (.Refuse residue)

/-- Countermodel: a caught exception is lost instead of becoming a typed refusal. -/
def exceptionLostMutant
    {A : Type u} {Wake : Type v} {Residue : Type w} :
    OperationalObservation A Wake Residue →
      Option (OpResult A Wake Residue)
  | .Completed value => some (.Ok value)
  | .Waiting wake => some (.Await wake)
  | .Rejected residue => some (.Refuse residue)
  | .ResourceLimit residue => some (.ResourceExhausted residue)
  | .ProcessTimeout residue => some (.ResourceExhausted residue)
  | .CaughtException _ => none

/-- Countermodel: process timeout is mislabeled as semantic rejection. -/
def timeoutAsRefutationMutant
    {A : Type u} {Wake : Type v} {Residue : Type w} :
    OperationalObservation A Wake Residue →
      Option (OpResult A Wake Residue)
  | .Completed value => some (.Ok value)
  | .Waiting wake => some (.Await wake)
  | .Rejected residue => some (.Refuse residue)
  | .ResourceLimit residue => some (.ResourceExhausted residue)
  | .ProcessTimeout residue => some (.Refuse residue)
  | .CaughtException residue => some (.Refuse residue)

/-- The real classifier satisfies its conformance contract by construction. -/
theorem canonical_candidate_conforms
    {A : Type u} {Wake : Type v} {Residue : Type w} :
    ClassifierConforms
      (canonicalCandidate (A := A) (Wake := Wake) (Residue := Residue)) :=
  fun _ => rfl

/-- The real contract rejects the silent-timeout countermodel on the same timeout. -/
theorem canonical_rejects_silent_timeout
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    ¬ ClassifierConforms
      (silentTimeoutMutant (A := A) (Wake := Wake) (Residue := Residue)) := by
  intro conforms
  have timeoutCase :
      (none : Option (OpResult A Wake Residue)) =
        some (.ResourceExhausted residue) :=
    conforms (.ProcessTimeout residue)
  cases timeoutCase

/-- The real contract rejects the exception-lost countermodel on the same exception. -/
theorem canonical_rejects_exception_lost
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    ¬ ClassifierConforms
      (exceptionLostMutant (A := A) (Wake := Wake) (Residue := Residue)) := by
  intro conforms
  have exceptionCase :
      (none : Option (OpResult A Wake Residue)) =
        some (.Refuse residue) :=
    conforms (.CaughtException residue)
  cases exceptionCase

/-- The real contract rejects timeout-as-refutation on the same timeout and residue. -/
theorem canonical_rejects_timeout_as_refutation
    {A : Type u} {Wake : Type v} {Residue : Type w}
    (residue : Residue) :
    ¬ ClassifierConforms
      (timeoutAsRefutationMutant
        (A := A) (Wake := Wake) (Residue := Residue)) := by
  intro conforms
  have timeoutCase :
      (some (.Refuse residue) : Option (OpResult A Wake Residue)) =
        some (.ResourceExhausted residue) :=
    conforms (.ProcessTimeout residue)
  have resultCase :
      (.Refuse residue : OpResult A Wake Residue) =
        .ResourceExhausted residue :=
    Option.some.inj timeoutCase
  cases resultCase

end Residua.RCC

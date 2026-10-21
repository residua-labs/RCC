import RCC.ConflictSerializability
import RCC.TransactionFootprint

/-!
# RCC-51 Global Invariant from the Finalized Serializable Cut

The legacy `GlobalInvariantLaw` is a useful induction skeleton, but its
predicate and one-step law are supplied directly by the caller.  This module
adds the missing proof-carrying bridges:

* every step carries an RCC-48 sealed four-dimensional footprint;
* every invariant coordinate in that footprint belongs to one complete
  mandatory-invariant universe;
* every step preserves every coordinate in that mandatory universe;
* the checked execution is the exact RCC-49 global serial execution;
* the RCC-49 event universe is exact for one sealed finalized cut; and
* mandatory coordinate claims are sufficient for the declared global intent.

The kernel remains relative to the supplied semantic predicates and finalized
cut.  Runtime/source derivation of those predicates is an adapter obligation.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.GlobalInvariant

open Residua.RCC.AuthorizationFinality
open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability
open Residua.RCC.TransactionFootprint

universe u

/--
Exact realization of the mandatory invariant predicate by one sealed finite
universe.  The predicate belongs to the intent contract; a caller cannot
shrink it merely by shortening the enumeration.
-/
structure MandatoryInvariantUniverse
    {InvariantDomain : Type u}
    (mandatoryUniverse : SealedDomainUniverse InvariantDomain)
    (Mandatory : InvariantDomain → Prop) : Prop where
  exact :
    ∀ domain,
      mandatoryUniverse.InUniverse domain ↔ Mandatory domain

/--
The explicit bridge from all mandatory coordinate claims to the declared
global intent.  A vacuous or always-`True` claim family cannot prove a stronger
intent unless this implication is actually inhabited.
-/
structure InvariantIntentContract
    {State InvariantDomain : Type u}
    (Mandatory : InvariantDomain → Prop)
    (Claim : InvariantDomain → State → Prop)
    (GlobalIntent : State → Prop) : Prop where
  mandatoryClaimsSuffice :
    ∀ state,
      (∀ domain, Mandatory domain → Claim domain state) →
      GlobalIntent state

/--
One existing finalized step strengthened by an RCC-48 universe-complete
footprint.  The old `CompleteFootprint` remains inside `step`, but the new seal
is an independent, stronger realization witness.
-/
structure RCC48CertifiedStep
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain)
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (preState : State) where
  step :
    CertifiedFinalizedStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      (history := history)
      (ConfigLawful := ConfigLawful)
      surface preState
  universes :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain
  footprintSeal :
    UniverseCompleteFootprint
      surface preState step.finalized.proposal universes step.footprint

/--
An actual serial execution whose every step is RCC-48 sealed and carries
coordinate-wise mandatory-invariant preservation.
-/
inductive InvariantPreservingExecution
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain OccurrenceId EventQ Config : Type u}
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    (Generation Epoch EffectSlot FailureName : Type u)
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (mandatoryUniverse : SealedDomainUniverse InvariantDomain)
    (Claim : InvariantDomain → State → Prop) :
    State → List OccurrenceId → State → Type u
  | nil (state : State) :
      InvariantPreservingExecution
        AuthorityEvidence Generation Epoch EffectSlot FailureName
        surface history ConfigLawful mandatoryUniverse Claim
        state [] state
  | cons
      {preState finalState : State}
      {tailOccurrences : List OccurrenceId}
      (step :
        RCC48CertifiedStep
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (OccurrenceId := OccurrenceId)
          (FailureName := FailureName)
          (history := history)
          (ConfigLawful := ConfigLawful)
          surface preState)
      (footprintMandatory :
        ∀ domain,
          domain ∈ step.step.footprint.invariantDomains →
          domain ∈ mandatoryUniverse.coordinates)
      (preservesMandatory :
        ∀ domain,
          domain ∈ mandatoryUniverse.coordinates →
          Claim domain preState →
          Claim domain
            (surface.apply preState step.step.finalized.proposal))
      (tail :
        InvariantPreservingExecution
          AuthorityEvidence Generation Epoch EffectSlot FailureName
          surface history ConfigLawful mandatoryUniverse Claim
          (surface.apply preState step.step.finalized.proposal)
          tailOccurrences finalState)
      (fresh : step.step.finalized.occurrenceId ∉ tailOccurrences) :
      InvariantPreservingExecution
        AuthorityEvidence Generation Epoch EffectSlot FailureName
        surface history ConfigLawful mandatoryUniverse Claim
        preState (step.step.finalized.occurrenceId :: tailOccurrences)
          finalState

/-- Erasing RCC-48 and invariant evidence yields the exact RCC-49 execution. -/
def InvariantPreservingExecution.toSerialExecution
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {mandatoryUniverse : SealedDomainUniverse InvariantDomain}
    {Claim : InvariantDomain → State → Prop}
    {initial final : State}
    {occurrences : List OccurrenceId}
    (execution :
      InvariantPreservingExecution
        AuthorityEvidence
        Generation Epoch EffectSlot FailureName
        surface history ConfigLawful mandatoryUniverse Claim
        initial occurrences final) :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful initial occurrences final :=
  match execution with
  | .nil state => .nil state
  | .cons step _footprintMandatory _preservesMandatory tail fresh =>
      .cons step.step tail.toSerialExecution fresh

/--
Induction over the checked execution preserves every coordinate in the sealed
mandatory enumeration.
-/
theorem InvariantPreservingExecution.preservesAllEnumerated
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {mandatoryUniverse : SealedDomainUniverse InvariantDomain}
    {Claim : InvariantDomain → State → Prop}
    {initial final : State}
    {occurrences : List OccurrenceId}
    (execution :
      InvariantPreservingExecution
        AuthorityEvidence
        Generation Epoch EffectSlot FailureName
        surface history ConfigLawful mandatoryUniverse Claim
        initial occurrences final)
    (initialClaims :
      ∀ domain,
        domain ∈ mandatoryUniverse.coordinates →
        Claim domain initial) :
    ∀ domain,
      domain ∈ mandatoryUniverse.coordinates →
      Claim domain final := by
  induction execution with
  | nil =>
      exact initialClaims
  | @cons preState _ tailOccurrences step footprintMandatory
      preservesMandatory tail fresh inductionHypothesis =>
      apply inductionHypothesis
      intro domain enumerated
      exact preservesMandatory domain enumerated
        (initialClaims domain enumerated)

/--
Expose the RCC-48 seal and mandatory-footprint proof for the first occurrence
of any nonempty checked execution.  Keeping this inversion theorem in the
kernel prevents downstream countermodels from depending on fragile indexed
constructor elimination.
-/
theorem InvariantPreservingExecution.headFootprintMandatory
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {mandatoryUniverse : SealedDomainUniverse InvariantDomain}
    {Claim : InvariantDomain → State → Prop}
    {initial final : State}
    {first : OccurrenceId}
    {rest : List OccurrenceId}
    (execution :
      InvariantPreservingExecution
        AuthorityEvidence
        Generation Epoch EffectSlot FailureName
        surface history ConfigLawful mandatoryUniverse Claim
        initial (first :: rest) final) :
    ∃ step :
        RCC48CertifiedStep
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (OccurrenceId := OccurrenceId)
          (FailureName := FailureName)
          (history := history)
          (ConfigLawful := ConfigLawful)
          surface initial,
      step.step.finalized.occurrenceId = first ∧
        ∀ domain,
          domain ∈ step.step.footprint.invariantDomains →
          domain ∈ mandatoryUniverse.coordinates := by
  cases execution with
  | cons step footprintMandatory _preservesMandatory _tail _fresh =>
      exact ⟨step, rfl, footprintMandatory⟩

/--
The RCC-49 event universe is exact for one independently sealed finalized cut.
This excludes a partition-local `InUniverse` predicate that silently omits a
globally finalized event.
-/
structure FinalizedCutBinding
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    (serial :
      ConflictSerializableHistory
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface history ConfigLawful initial)
    (finalizedCut :
      SealedDomainUniverse
        (FinalizedEvent
          (Judgment := Judgment)
          (AuthorityEvidence := AuthorityEvidence)
          (Generation := Generation)
          (Epoch := Epoch)
          (EffectSlot := EffectSlot)
          (OccurrenceId := OccurrenceId)
          (FailureName := FailureName)
          history ConfigLawful)) : Prop where
  exact :
    ∀ event,
      serial.eventUniverse.InUniverse event ↔
        finalizedCut.InUniverse event

/--
Complete RCC-51 evidence: one sealed finalized cut, its exact RCC-49 global
serial history, the same RCC-48/invariant checked execution, and an intent
decomposition over a sealed mandatory-invariant universe.
-/
structure GlobalInvariantCertificate
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State)
    (Mandatory : InvariantDomain → Prop)
    (Claim : InvariantDomain → State → Prop)
    (GlobalIntent : State → Prop) where
  serial :
    ConflictSerializableHistory
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface history ConfigLawful initial
  finalizedCut :
    SealedDomainUniverse
      (FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
  cutBinding : FinalizedCutBinding serial finalizedCut
  mandatoryUniverse : SealedDomainUniverse InvariantDomain
  mandatoryBinding :
    MandatoryInvariantUniverse mandatoryUniverse Mandatory
  intent : InvariantIntentContract Mandatory Claim GlobalIntent
  checkedExecution :
    InvariantPreservingExecution
      AuthorityEvidence
      Generation Epoch EffectSlot FailureName
      surface history ConfigLawful mandatoryUniverse Claim
      initial serial.occurrences serial.finalState
  executionBound :
    checkedExecution.toSerialExecution = serial.execution
  initialClaims :
    ∀ domain,
      domain ∈ mandatoryUniverse.coordinates →
      Claim domain initial

/--
RCC-51: the final state of the actual globally serializable finalized cut
satisfies the declared global intent.
-/
theorem global_finalized_cut_satisfies_intent
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
          InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {Mandatory : InvariantDomain → Prop}
    {Claim : InvariantDomain → State → Prop}
    {GlobalIntent : State → Prop}
    (certificate :
      GlobalInvariantCertificate
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        surface history ConfigLawful initial Mandatory Claim GlobalIntent) :
    GlobalIntent certificate.serial.finalState := by
  apply certificate.intent.mandatoryClaimsSuffice
  intro domain mandatory
  have inUniverse : certificate.mandatoryUniverse.InUniverse domain :=
    (certificate.mandatoryBinding.exact domain).mpr mandatory
  have enumerated : domain ∈ certificate.mandatoryUniverse.coordinates :=
    certificate.mandatoryUniverse.coverage.complete domain inUniverse
  exact
    certificate.checkedExecution.preservesAllEnumerated
      certificate.initialClaims domain enumerated

end Residua.RCC.GlobalInvariant

import RCC.ConflictSerializability

/-!
# RCC-56 Serializable Finalized Epoch Cut

An epoch-closure candidate must be one canonical RCC-45 finalized cut whose
complete finite event universe is executed by an actual RCC-49 global serial
execution and whose final state satisfies an RCC-51 global invariant.

The canonical head event is present in the complete RCC-49 universe, occupies
the final occurrence position, and agrees with the RCC-45 closure head/config.
Consequently local, nonfinal, unserializable, pending-transition, or
coverage-empty projections cannot inhabit the eligibility certificate.

This is a finite safety kernel.  Source/history adapters still establish the
truth of RCC-45 and RCC-49 universes.  Prelude-only Lean 4.14; no Mathlib,
axioms, or proof placeholders.
-/

namespace Residua.RCC.SerializableEpochClosure

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability

universe u

/--
The only RCC-56 eligibility certificate.

`headEventFinal` prevents a valid event from being buried before a later cut;
the two head/config bindings and the final-state root binding identify the
serial execution endpoint with the canonical RCC-45 snapshot.
-/
structure SerializableEpochClosureEvidence
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State)
    (GlobalInvariant : State → Prop)
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          OccurrenceId FailureName EventQ}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    (closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)) : Type u where
  serial :
    ConflictSerializableHistory
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface history ConfigLawful initial
  headEvent :
    FinalizedEvent
      (Judgment := Judgment)
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      history ConfigLawful
  headEventInUniverse : serial.eventUniverse.InUniverse headEvent
  headEventIsClosureEvent :
    headEvent.eventQ =
      closure.finalizedHead.certificate.admission.history.event
  headEventFinal :
    ∃ priorOccurrences,
      serial.occurrences = priorOccurrences ++ [headEvent.occurrenceId]
  headEventHeadBound :
    headEvent.certificate.head = closure.snapshot.head
  headEventConfigBound :
    headEvent.config = closure.snapshot.config
  finalHeadBound :
    surface.stateRoot serial.finalState = closure.snapshot.head
  invariantLaw :
    GlobalInvariantLaw
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := OccurrenceId)
      (FailureName := FailureName)
      surface history ConfigLawful GlobalInvariant
  initialInvariant : GlobalInvariant initial

/-- RCC-51 derives the global invariant at the exact RCC-49 final state. -/
theorem serializable_epoch_closure_final_invariant
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {GlobalInvariant : State → Prop}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          OccurrenceId FailureName EventQ}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (certificate :
      SerializableEpochClosureEvidence
        surface history ConfigLawful initial GlobalInvariant closure) :
    GlobalInvariant certificate.serial.finalState :=
  serial_history_preserves_global_invariant
    certificate.invariantLaw certificate.serial.execution
      certificate.initialInvariant

/-- The canonical RCC-45 head event occurs in the actual RCC-49 schedule. -/
theorem closure_head_occurrence_is_serialized
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {GlobalInvariant : State → Prop}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          OccurrenceId FailureName EventQ}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (certificate :
      SerializableEpochClosureEvidence
        surface history ConfigLawful initial GlobalInvariant closure) :
    certificate.headEvent.occurrenceId ∈ certificate.serial.occurrences :=
  inUniverse_occurrence_mem
    certificate.serial certificate.headEvent certificate.headEventInUniverse

/-- RCC-56 retains RCC-45's complete source-partition coverage. -/
theorem serializable_epoch_closure_source_coverage
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {GlobalInvariant : State → Prop}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          OccurrenceId FailureName EventQ}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (_certificate :
      SerializableEpochClosureEvidence
        surface history ConfigLawful initial GlobalInvariant closure) :
    CoverageCertificate
      sourceProtocol.InUniverse closure.snapshot.priorPartitions := by
  rw [← closure.partitionsMatch]
  exact closure.finalizedWindow.windowSeal.coverage

/-- A complete universe containing the canonical head event cannot be empty. -/
theorem empty_event_coverage_cannot_contain_canonical_head
    {Event : Type u}
    (eventUniverse : FinalizedEventUniverse Event)
    (headEvent : Event)
    (headInUniverse : eventUniverse.InUniverse headEvent)
    (empty : eventUniverse.enumeration = []) :
    False := by
  have covered := eventUniverse.complete headEvent headInUniverse
  rw [empty] at covered
  cases covered

/-- An eligible serial cut cannot have an empty occurrence schedule. -/
theorem serializable_epoch_closure_schedule_nonempty
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {initial : State}
    {GlobalInvariant : State → Prop}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          OccurrenceId FailureName EventQ}
    {sourceProtocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    {closure :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := sourceProtocol)
        (ConfigStable := ConfigStable)}
    (certificate :
      SerializableEpochClosureEvidence
        surface history ConfigLawful initial GlobalInvariant closure) :
    certificate.serial.occurrences ≠ [] := by
  intro empty
  have member := closure_head_occurrence_is_serialized certificate
  rw [empty] at member
  cases member

/-- Named RCC-56 ineligibility: no weaker cut form is accepted. -/
inductive SerializableEpochClosureResidue
  | canonicalFinalizedSerializableCutRequired
  deriving DecidableEq, Repr

/-- Eligibility is mechanically projected only from the full certificate. -/
inductive SerializableEpochClosureAssessment (Certificate : Type u)
  | eligible :
      Certificate → SerializableEpochClosureAssessment Certificate
  | refuse :
      SerializableEpochClosureResidue →
      SerializableEpochClosureAssessment Certificate

def assessSerializableEpochClosure
    {Certificate : Type u}
    (certificate? : Option Certificate) :
    SerializableEpochClosureAssessment Certificate :=
  match certificate? with
  | some certificate => .eligible certificate
  | none => .refuse .canonicalFinalizedSerializableCutRequired

end Residua.RCC.SerializableEpochClosure

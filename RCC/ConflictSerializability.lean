import RCC.GlobalSerializability

/-!
# RCC-49 Conflict Serializability

RCC-49 strengthens pairwise ordering inside one supplied execution into a
closed-world global theorem: every finalized event in one complete finite
event universe is represented in the same actual serial execution, so every
distinct semantically noncommuting occurrence pair is comparable in one
global order.

Order identity is the durable occurrence carried by the RCC-43/RCC-45 event.
It is deliberately not operation identity, payload/value identity, proposal
bytes, or certificate identity.

The kernel is finite and safety-only.  A runtime adapter still has to derive
the complete finalized-event universe and the actual RCC-45 certificates.
Prelude-only Lean 4.14; no Mathlib or proof placeholders.
-/

namespace Residua.RCC.ConflictSerializability

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalSerializability

universe u

/--
A finite, proof-carrying closed world of finalized events.  An empty or
partition-local enumeration cannot stand for the global event universe unless
its `complete` proof covers every event selected by `InUniverse`.
-/
structure FinalizedEventUniverse (Event : Type u) where
  InUniverse : Event → Prop
  enumeration : List Event
  sound : ∀ event, event ∈ enumeration → InUniverse event
  complete : ∀ event, InUniverse event → event ∈ enumeration

/-- The homogeneous actual-finalized-event carrier used by RCC-49. -/
abbrev FinalizedEvent
    {Slot Head Judgment Generation Epoch EffectSlot OccurrenceId FailureName
      EventQ Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop) :=
  RCC45FinalizedEvent
    (Judgment := Judgment)
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := OccurrenceId)
    (FailureName := FailureName)
    history ConfigLawful

/-- Durable event identity retained alongside occurrence identity. -/
def FinalizedEvent.eventQ
    {Slot Head Judgment Generation Epoch EffectSlot OccurrenceId FailureName
      EventQ Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    (event :
      FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful) : EventQ :=
  event.certificate.admission.history.event

/--
One global conflict-serializable finalized history.

All enumerated RCC-45 events occur in the same `SerialExecution`; conversely
every occurrence in that execution is backed by an in-universe RCC-45 event.
The occurrence schedule is therefore neither a union of unrelated local
orders nor a value-deduplicated projection.
-/
structure ConflictSerializableHistory
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (initial : State) where
  eventUniverse :
    FinalizedEventUniverse
      (FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
  occurrences : List OccurrenceId
  finalState : State
  execution :
    SerialExecution
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (FailureName := FailureName)
      surface history ConfigLawful initial occurrences finalState
  enumeratedOccurrenceComplete :
    ∀ event,
      event ∈ eventUniverse.enumeration →
      event.occurrenceId ∈ occurrences
  occurrenceSound :
    ∀ occurrence,
      occurrence ∈ occurrences →
      ∃ event,
        eventUniverse.InUniverse event ∧
          event.occurrenceId = occurrence
  occurrenceFaithful :
    ∀ left right,
      eventUniverse.InUniverse left →
      eventUniverse.InUniverse right →
      left.occurrenceId = right.occurrenceId →
      left.eventQ = right.eventQ

/-- Every finalized in-universe event is represented in the global schedule. -/
theorem inUniverse_occurrence_mem
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
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
    (event :
      FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (inUniverse : serial.eventUniverse.InUniverse event) :
    event.occurrenceId ∈ serial.occurrences :=
  serial.enumeratedOccurrenceComplete event
    (serial.eventUniverse.complete event inUniverse)

/--
RCC-49: all distinct semantically noncommuting finalized occurrence pairs in
the complete universe are comparable in one global order, and the reverse
direction is excluded by occurrence freshness.
-/
theorem all_noncommuting_finalized_occurrence_pairs_globally_ordered
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
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
    (left right :
      FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (leftFinalized : serial.eventUniverse.InUniverse left)
    (rightFinalized : serial.eventUniverse.InUniverse right)
    (distinct : left.occurrenceId ≠ right.occurrenceId)
    (noncommuting :
      ¬ OperationsCommuteAt
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (FailureName := FailureName)
        surface initial left right) :
    OccursBefore
          left.occurrenceId right.occurrenceId serial.occurrences ∧
        ¬ OccursBefore
          right.occurrenceId left.occurrenceId serial.occurrences
      ∨
      OccursBefore
          right.occurrenceId left.occurrenceId serial.occurrences ∧
        ¬ OccursBefore
          left.occurrenceId right.occurrenceId serial.occurrences :=
  noncommuting_finalized_events_ordered
    serial.execution left right
      (inUniverse_occurrence_mem serial left leftFinalized)
      (inUniverse_occurrence_mem serial right rightFinalized)
      distinct noncommuting

/--
No occurrence can occupy two positions in the one global order.  This law is
about occurrence identity even when the two events carry equal values.
-/
theorem global_occurrence_order_nodup
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
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
        surface history ConfigLawful initial) :
    serial.occurrences.Nodup :=
  serial.execution.occurrences_nodup

/--
Occurrence identity cannot alias two different durable finalized events inside
the certified global universe.
-/
theorem same_occurrence_same_durable_event
    {State Slot Head Judgment OperationId ReadDomain WriteDomain EffectDomain
      InvariantDomain Generation Epoch EffectSlot OccurrenceId FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {surface :
      TransactionSurface
        State Slot Head Judgment OperationId ReadDomain WriteDomain
          EffectDomain InvariantDomain}
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
    (left right :
      FinalizedEvent
        (Judgment := Judgment)
        (AuthorityEvidence := AuthorityEvidence)
        (Generation := Generation)
        (Epoch := Epoch)
        (EffectSlot := EffectSlot)
        (OccurrenceId := OccurrenceId)
        (FailureName := FailureName)
        history ConfigLawful)
    (leftFinalized : serial.eventUniverse.InUniverse left)
    (rightFinalized : serial.eventUniverse.InUniverse right)
    (sameOccurrence : left.occurrenceId = right.occurrenceId) :
    left.eventQ = right.eventQ :=
  serial.occurrenceFaithful
    left right leftFinalized rightFinalized sameOccurrence

end Residua.RCC.ConflictSerializability

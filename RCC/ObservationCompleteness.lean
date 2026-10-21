/-!
# RCC WI-2 observation completeness

WI-2 is deliberately scoped.  It does not claim that an observer sees every
event in the external world.  It proves that every event in one explicitly
sealed finite world-event universe has a faithful observation record.

The load-bearing premises are separate:

* `FiniteEventUniverseSeal` proves that the declared list is sound, complete,
  and sealed for the stated scope;
* `ObservationCompletenessCertificate` proves that the scan is scoped and
  faithfully covers every event in that exact list.

An empty scan is therefore not an absence proof by itself.  It can certify
completeness only when the sealed coverage theorem proves that the in-scope
universe itself is empty.  An unsealed universe cannot construct the premise.

This module is independent of WI-1 observation soundness.  Its relation
`Faithful` is an explicit certificate boundary; WI-1 may later discharge that
relation for a concrete world interface.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or declared axioms.
-/

namespace Residua.RCC.ObservationCompleteness

universe u v

/-- A proposed finite world-event scope. -/
structure FiniteEventUniverse (Event : Type u) where
  scopeQ : String
  events : List Event
  inScope : Event → Prop
  sealed : Bool

/--
The only authority for treating `events` as the complete finite universe.
The Boolean prevents an unsealed view from acquiring authority merely by
supplying enumeration theorems.
-/
structure FiniteEventUniverseSeal
    {Event : Type u}
    (scope : FiniteEventUniverse Event) : Prop where
  sealed : scope.sealed = true
  enumerationSound :
    ∀ event,
      event ∈ scope.events →
        scope.inScope event
  enumerationComplete :
    ∀ event,
      scope.inScope event →
        event ∈ scope.events

/-- One concrete event/observation record returned by a scan. -/
structure ObservationRecord (Event : Type u) (Observation : Type v) where
  event : Event
  observation : Observation

/-- A scan is data, not a completeness claim. -/
structure ObservationScan (Event : Type u) (Observation : Type v) where
  records : List (ObservationRecord Event Observation)

/-- A record faithfully covers an event under the declared observation relation. -/
def RecordCovers
    {Event : Type u}
    {Observation : Type v}
    (Faithful : Event → Observation → Prop)
    (record : ObservationRecord Event Observation)
    (event : Event) : Prop :=
  record.event = event ∧
    Faithful event record.observation

/--
Proof-carrying WI-2 evidence.

`coversEnumerated` quantifies over the exact sealed enumeration, while
`recordsScoped` prevents an unrelated out-of-scope record from being used as
coverage evidence.
-/
structure ObservationCompletenessCertificate
    {Event : Type u}
    {Observation : Type v}
    (scope : FiniteEventUniverse Event)
    (scan : ObservationScan Event Observation)
    (Faithful : Event → Observation → Prop) : Prop where
  universeSeal : FiniteEventUniverseSeal scope
  recordsScoped :
    ∀ record,
      record ∈ scan.records →
        scope.inScope record.event
  coversEnumerated :
    ∀ event,
      event ∈ scope.events →
        ∃ record,
          record ∈ scan.records ∧
            RecordCovers Faithful record event

/-- The semantic WI-2 conclusion, explicitly relative to one sealed scope. -/
def ScopedObservationComplete
    {Event : Type u}
    {Observation : Type v}
    (scope : FiniteEventUniverse Event)
    (scan : ObservationScan Event Observation)
    (Faithful : Event → Observation → Prop) : Prop :=
  ∀ event,
    scope.inScope event →
      ∃ record,
        record ∈ scan.records ∧
          RecordCovers Faithful record event

/-- Every in-scope event has a faithful scan record. -/
theorem observation_complete_within_sealed_scope
    {Event : Type u}
    {Observation : Type v}
    {scope : FiniteEventUniverse Event}
    {scan : ObservationScan Event Observation}
    {Faithful : Event → Observation → Prop}
    (certificate :
      ObservationCompletenessCertificate scope scan Faithful) :
    ScopedObservationComplete scope scan Faithful := by
  intro event inScope
  exact
    certificate.coversEnumerated event
      (certificate.universeSeal.enumerationComplete event inScope)
  done

/--
An empty scan can be complete only when the sealed coverage theorem proves
there are no in-scope events.  Empty data alone never establishes absence.
-/
theorem complete_empty_scan_forces_empty_scope
    {Event : Type u}
    {Observation : Type v}
    {scope : FiniteEventUniverse Event}
    {Faithful : Event → Observation → Prop}
    (certificate :
      ObservationCompletenessCertificate
        scope ⟨[]⟩ Faithful) :
    ∀ event, ¬ scope.inScope event := by
  intro event inScope
  have covered :=
    observation_complete_within_sealed_scope certificate event inScope
  obtain ⟨record, member, relation⟩ := covered
  cases member
  done

/-- A concrete missed event refutes a purported WI-2 certificate. -/
structure ObservationGap
    {Event : Type u}
    {Observation : Type v}
    (scope : FiniteEventUniverse Event)
    (scan : ObservationScan Event Observation)
    (Faithful : Event → Observation → Prop) where
  event : Event
  inScope : scope.inScope event
  uncovered :
    ∀ record,
      record ∈ scan.records →
        ¬ RecordCovers Faithful record event

theorem ObservationGap.refutesCompleteness
    {Event : Type u}
    {Observation : Type v}
    {scope : FiniteEventUniverse Event}
    {scan : ObservationScan Event Observation}
    {Faithful : Event → Observation → Prop}
    (gap : ObservationGap scope scan Faithful) :
    ObservationCompletenessCertificate scope scan Faithful →
      False := by
  intro certificate
  obtain ⟨record, member, covers⟩ :=
    observation_complete_within_sealed_scope
      certificate gap.event gap.inScope
  exact gap.uncovered record member covers
  done

/-- Named WI-2 refusal reasons for executable adapters. -/
inductive ObservationCompletenessResidue
  | universeUnsealed
  | universeCoverageIncomplete
  | eventUnobserved
  | observationUnfaithful
  | recordOutOfScope
  deriving DecidableEq, Repr

end Residua.RCC.ObservationCompleteness

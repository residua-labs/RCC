import RCC.ObservationCompleteness

/-!
# RCC WI-2 observation-completeness tests

The positive fixture seals a two-event universe and faithfully observes both
events.  Countermodels show that:

* an unsealed universe cannot acquire a coverage certificate;
* an empty scan cannot cover a nonempty sealed scope;
* a partial scan cannot silently omit one declared event; and
* merely mentioning an event with an unfaithful observation is not coverage.
-/

namespace Residua.RCC.ObservationCompleteness.Tests

open Residua.RCC.ObservationCompleteness

inductive Event
  | alpha
  | beta
  deriving DecidableEq, Repr

inductive Observation
  | sawAlpha
  | sawBeta
  | malformed
  deriving DecidableEq, Repr

def InScope : Event → Prop
  | .alpha => True
  | .beta => True

def Faithful (event : Event) (observation : Observation) : Prop :=
  match event with
  | .alpha =>
      match observation with
      | .sawAlpha => True
      | .sawBeta => False
      | .malformed => False
  | .beta =>
      match observation with
      | .sawAlpha => False
      | .sawBeta => True
      | .malformed => False

def sealedUniverse : FiniteEventUniverse Event where
  scopeQ := "wi2:demo:world-events:v1"
  events := [.alpha, .beta]
  inScope := InScope
  sealed := true

def sealedUniverseCertificate :
    FiniteEventUniverseSeal sealedUniverse where
  sealed := rfl
  enumerationSound := by
    intro event member
    cases event <;> exact True.intro
  enumerationComplete := by
    intro event inScope
    cases event
    · exact List.Mem.head _
    · exact List.Mem.tail _ (List.Mem.head _)

def alphaRecord : ObservationRecord Event Observation :=
  ⟨.alpha, .sawAlpha⟩

def betaRecord : ObservationRecord Event Observation :=
  ⟨.beta, .sawBeta⟩

def completeScan : ObservationScan Event Observation :=
  ⟨[alphaRecord, betaRecord]⟩

def completeCertificate :
    ObservationCompletenessCertificate
      sealedUniverse completeScan Faithful where
  universeSeal := sealedUniverseCertificate
  recordsScoped := by
    intro record member
    simp only [completeScan] at member
    cases member with
    | head =>
        exact True.intro
    | tail _ tailMember =>
        cases tailMember with
        | head =>
            exact True.intro
        | tail _ impossible =>
            cases impossible
  coversEnumerated := by
    intro event member
    cases event
    · exact
        ⟨alphaRecord,
          List.Mem.head _,
          ⟨rfl, True.intro⟩⟩
    · exact
        ⟨betaRecord,
          List.Mem.tail _ (List.Mem.head _),
          ⟨rfl, True.intro⟩⟩

theorem both_events_are_observed :
    ScopedObservationComplete
      sealedUniverse completeScan Faithful :=
  observation_complete_within_sealed_scope completeCertificate

/-! ## Mutant 1: the enumeration is not sealed -/

def unsealedUniverse : FiniteEventUniverse Event where
  scopeQ := "wi2:demo:world-events:unsealed"
  events := [.alpha, .beta]
  inScope := InScope
  sealed := false

theorem unsealed_universe_has_no_coverage_authority :
    FiniteEventUniverseSeal unsealedUniverse →
      False := by
  intro certificate
  cases certificate.sealed
  done

theorem unsealed_universe_cannot_certify_completeness :
    ObservationCompletenessCertificate
      unsealedUniverse completeScan Faithful →
      False := by
  intro certificate
  exact
    unsealed_universe_has_no_coverage_authority
      certificate.universeSeal
  done

/-! ## Mutant 2: an empty scan of a nonempty scope -/

def emptyScan : ObservationScan Event Observation :=
  ⟨[]⟩

def alphaMissingFromEmpty :
    ObservationGap sealedUniverse emptyScan Faithful where
  event := .alpha
  inScope := True.intro
  uncovered := by
    intro record member
    cases member

theorem empty_scan_does_not_prove_absence :
    ObservationCompletenessCertificate
      sealedUniverse emptyScan Faithful →
      False :=
  alphaMissingFromEmpty.refutesCompleteness

/-! ## Mutant 3: a shortened scan omits beta -/

def alphaOnlyScan : ObservationScan Event Observation :=
  ⟨[alphaRecord]⟩

def betaMissingFromPartial :
    ObservationGap sealedUniverse alphaOnlyScan Faithful where
  event := .beta
  inScope := True.intro
  uncovered := by
    intro record member covers
    cases member with
    | head =>
        exact Event.noConfusion covers.1
    | tail _ impossible =>
        cases impossible

theorem partial_scan_cannot_hide_beta :
    ObservationCompletenessCertificate
      sealedUniverse alphaOnlyScan Faithful →
      False :=
  betaMissingFromPartial.refutesCompleteness

/-! ## Mutant 4: the event is listed with an unfaithful observation -/

def malformedBetaRecord : ObservationRecord Event Observation :=
  ⟨.beta, .malformed⟩

def malformedScan : ObservationScan Event Observation :=
  ⟨[alphaRecord, malformedBetaRecord]⟩

def betaUnfaithful :
    ObservationGap sealedUniverse malformedScan Faithful where
  event := .beta
  inScope := True.intro
  uncovered := by
    intro record member covers
    cases member with
    | head =>
        exact Event.noConfusion covers.1
    | tail _ tailMember =>
        cases tailMember with
        | head =>
            exact covers.2
        | tail _ impossible =>
            cases impossible

theorem event_name_without_faithful_observation_is_not_coverage :
    ObservationCompletenessCertificate
      sealedUniverse malformedScan Faithful →
      False :=
  betaUnfaithful.refutesCompleteness

/-!
The generic empty-scan theorem records the precise boundary: only a sealed
proof that the scope itself is empty can make an empty scan complete.
-/
theorem any_complete_empty_scan_forces_no_in_scope_event
    (certificate :
      ObservationCompletenessCertificate
        sealedUniverse emptyScan Faithful) :
    ∀ event, ¬ sealedUniverse.inScope event :=
  complete_empty_scan_forces_empty_scope certificate

#print axioms observation_complete_within_sealed_scope
#print axioms complete_empty_scan_forces_empty_scope
#print axioms ObservationGap.refutesCompleteness
#print axioms both_events_are_observed
#print axioms unsealed_universe_has_no_coverage_authority
#print axioms unsealed_universe_cannot_certify_completeness
#print axioms empty_scan_does_not_prove_absence
#print axioms partial_scan_cannot_hide_beta
#print axioms event_name_without_faithful_observation_is_not_coverage
#print axioms any_complete_empty_scan_forces_no_in_scope_event
end Residua.RCC.ObservationCompleteness.Tests

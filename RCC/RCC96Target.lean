import RCCTests.MetaFailureExhaustion

/-! RCC-96 candidate: sealed meta-failure exhaustion and named-gap discipline. -/

namespace Residua.RCC.RCC96Target

open Residua.RCC.MetaFailureExhaustion.Tests
open Residua.RCC.MetaFailureExhaustion
open Residua.RCC.FailureCoverage

def nodeFailureDerived := node_failure_is_derived
def bridgeFailureDerived := bridge_failure_is_derived
def assumptionFailureDerived := assumption_failure_is_derived
def scopeEscapeFailureDerived := scope_escape_failure_is_derived
def overlappingClassifiersRefused := overlapping_classifiers_are_ambiguous
def unknownEvidenceIsGap := unknown_evidence_is_gap
def allRefutedEvidenceIsGap := true_in_scope_all_refuted_is_evidence_gap
def ambiguousWindowNotExhaustive := ambiguous_window_cannot_be_exhaustive
def unknownWindowNotExhaustive := unknown_window_cannot_be_exhaustive
def allRefutedWindowNotExhaustive := all_refuted_window_cannot_be_exhaustive
def rawExceptionNamed := raw_exception_is_named_not_green
def unknownReadoutIsGap := unknown_readout_is_gap_not_green
def omittedFailureRefused := fifth_in_scope_failure_cannot_be_omitted_from_seal
def emptyUniverseRefused := empty_universe_cannot_seal_nonempty_scope
def unsealedUniverseRefused := unsealed_universe_is_refused
def wrongSnapshotRefused := wrong_snapshot_is_refused
def wrongFailureModelRefused := wrong_failure_model_is_refused
def outsideFailureNotScopeEscape := outside_failure_is_not_mislabeled_scope_escape
def declaredFailureHasPacket := every_declared_failure_has_admitted_packet

abbrev NodeFailureDerived : Prop :=
  ∃ classification,
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .nodeFault) =
      .classified classification ∧
    classification.tag = .nodeResidue
abbrev BridgeFailureDerived : Prop :=
  ∃ classification,
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .bridgeFault) =
      .classified classification ∧
    classification.tag = .bridgeResidue
abbrev AssumptionFailureDerived : Prop :=
  ∃ classification,
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .assumptionFault) =
      .classified classification ∧
    classification.tag = .assumptionViolation
abbrev ScopeEscapeFailureDerived : Prop :=
  ∃ classification,
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .scopeEscape) =
      .classified classification ∧
    classification.tag = .scopeEscape
abbrev OverlappingClassifiersRefused : Prop :=
  deriveEndToEndFailure badSemantics currentContext (some badWindow)
      (badObservation .overlap) = .refuse .ambiguousEvidence
abbrev UnknownEvidenceIsGap : Prop :=
  deriveEndToEndFailure badSemantics currentContext (some badWindow)
      (badObservation .nodeFault) = .refuse .evidenceGap
abbrev AllRefutedEvidenceIsGap : Prop :=
  deriveEndToEndFailure badSemantics currentContext (some badWindow)
      (badObservation .outside) = .refuse .evidenceGap
abbrev AmbiguousWindowNotExhaustive : Prop :=
  ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
      exhaustive.admitted = badWindow
abbrev UnknownWindowNotExhaustive : Prop :=
  ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
      exhaustive.admitted = badWindow
abbrev AllRefutedWindowNotExhaustive : Prop :=
  ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
      exhaustive.admitted = badWindow
abbrev RawExceptionNamed : Prop :=
  deriveEndToEndFailure semantics currentContext (some admittedWindow)
      (observation .nodeFault (.exception .scannerCrashed)) =
    .refuse (.rawException .scannerCrashed)
abbrev UnknownReadoutIsGap : Prop :=
  deriveEndToEndFailure semantics currentContext (some admittedWindow)
      (observation .nodeFault .unknown) = .refuse .evidenceGap
abbrev OmittedFailureRefused : Prop :=
  ¬ FailureUniverseSeal omittedFifthUniverse
abbrev EmptyUniverseRefused : Prop :=
  ¬ FailureUniverseSeal emptyUniverse
abbrev UnsealedUniverseRefused : Prop :=
  deriveEndToEndFailure semantics currentContext none
      (observation .nodeFault) = .refuse .universeUnsealed
abbrev WrongSnapshotRefused : Prop :=
  deriveEndToEndFailure semantics currentContext (some admittedWindow)
      staleObservation = .refuse .staleSnapshot
abbrev WrongFailureModelRefused : Prop :=
  deriveEndToEndFailure semantics currentContext (some admittedWindow)
      wrongModelObservation = .refuse .failureModelMismatch
abbrev OutsideFailureNotScopeEscape : Prop :=
  deriveEndToEndFailure semantics currentContext (some admittedWindow)
      (observation .outside) = .refuse .outsideSealedUniverse
abbrev DeclaredFailureHasPacket : Prop :=
  ∀ failure, mainUniverse.inScope failure →
    ∃ facts,
      admittedWindow.factsAt failure = some facts ∧
        semantics.AdmittedAt currentContext failure

structure Certificate where
  nodeFailureDerived : NodeFailureDerived
  bridgeFailureDerived : BridgeFailureDerived
  assumptionFailureDerived : AssumptionFailureDerived
  scopeEscapeFailureDerived : ScopeEscapeFailureDerived
  overlappingClassifiersRefused : OverlappingClassifiersRefused
  unknownEvidenceIsGap : UnknownEvidenceIsGap
  allRefutedEvidenceIsGap : AllRefutedEvidenceIsGap
  ambiguousWindowNotExhaustive : AmbiguousWindowNotExhaustive
  unknownWindowNotExhaustive : UnknownWindowNotExhaustive
  allRefutedWindowNotExhaustive : AllRefutedWindowNotExhaustive
  rawExceptionNamed : RawExceptionNamed
  unknownReadoutIsGap : UnknownReadoutIsGap
  omittedFailureRefused : OmittedFailureRefused
  emptyUniverseRefused : EmptyUniverseRefused
  unsealedUniverseRefused : UnsealedUniverseRefused
  wrongSnapshotRefused : WrongSnapshotRefused
  wrongFailureModelRefused : WrongFailureModelRefused
  outsideFailureNotScopeEscape : OutsideFailureNotScopeEscape
  declaredFailureHasPacket : DeclaredFailureHasPacket

def certificate : Certificate where
  nodeFailureDerived := node_failure_is_derived
  bridgeFailureDerived := bridge_failure_is_derived
  assumptionFailureDerived := assumption_failure_is_derived
  scopeEscapeFailureDerived := scope_escape_failure_is_derived
  overlappingClassifiersRefused := overlapping_classifiers_are_ambiguous
  unknownEvidenceIsGap := unknown_evidence_is_gap
  allRefutedEvidenceIsGap := true_in_scope_all_refuted_is_evidence_gap
  ambiguousWindowNotExhaustive := ambiguous_window_cannot_be_exhaustive
  unknownWindowNotExhaustive := unknown_window_cannot_be_exhaustive
  allRefutedWindowNotExhaustive := all_refuted_window_cannot_be_exhaustive
  rawExceptionNamed := raw_exception_is_named_not_green
  unknownReadoutIsGap := unknown_readout_is_gap_not_green
  omittedFailureRefused := fifth_in_scope_failure_cannot_be_omitted_from_seal
  emptyUniverseRefused := empty_universe_cannot_seal_nonempty_scope
  unsealedUniverseRefused := unsealed_universe_is_refused
  wrongSnapshotRefused := wrong_snapshot_is_refused
  wrongFailureModelRefused := wrong_failure_model_is_refused
  outsideFailureNotScopeEscape := outside_failure_is_not_mislabeled_scope_escape
  declaredFailureHasPacket := every_declared_failure_has_admitted_packet

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC96Target

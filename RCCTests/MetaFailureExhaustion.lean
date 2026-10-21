import RCC.MetaFailureExhaustion

/-!
# RCC ME-1 end-to-end failure exhaustion witnesses

The positive window contains one example of each frozen class plus one
deliberately overlapping packet.  Mutants cover an omitted fifth in-scope
failure, empty/unsealed universes, overlapping classifiers, unknown evidence,
raw exception, and snapshot/failure-model substitution.
-/

namespace Residua.RCC.MetaFailureExhaustion.Tests

open Residua.RCC.EffectClassification
open Residua.RCC.FailureCoverage
open Residua.RCC.MetaFailureExhaustion

inductive Snapshot
  | current
  | stale
  deriving DecidableEq, Repr

inductive FailureModel
  | v1
  | v2
  deriving DecidableEq, Repr

inductive Failure
  | nodeFault
  | bridgeFault
  | assumptionFault
  | scopeEscape
  | overlap
  | omittedFifth
  | outside
  deriving DecidableEq, Repr

inductive ExceptionName
  | scannerCrashed
  deriving DecidableEq, Repr

def mainUniverse : FailureUniverse Failure where
  inScope := fun failure =>
    failure = .nodeFault ∨
      failure = .bridgeFault ∨
      failure = .assumptionFault ∨
      failure = .scopeEscape
  mandatory := fun failure =>
    failure = .nodeFault ∨
      failure = .bridgeFault ∨
      failure = .assumptionFault ∨
      failure = .scopeEscape
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared :=
    [.nodeFault, .bridgeFault, .assumptionFault, .scopeEscape]

def mainSeal : FailureUniverseSeal mainUniverse where
  declaredSound := by
    intro failure member
    cases failure <;> simp [mainUniverse] at member ⊢
  declaredComplete := by
    intro failure inScope
    cases failure <;> simp [mainUniverse] at inScope ⊢

abbrev Context := FailureContext Snapshot FailureModel

def coverageSystem :
    FailureEvidenceSystem Context Failure Failure where
  modelAt := fun _ => mainUniverse
  AdmittedAt := fun _ evidence => mainUniverse.inScope evidence
  CoversAt := fun _ evidence failure grade =>
    grade = .mandatory ∧ evidence = failure

def semantics : MetaFailureSemantics where
  Snapshot := Snapshot
  FailureModel := FailureModel
  Failure := Failure
  CoverageEvidence := Failure
  ExceptionName := ExceptionName
  snapshotDecidableEq := inferInstance
  failureModelDecidableEq := inferInstance
  failureDecidableEq := inferInstance
  coverage := coverageSystem
  AdmittedAt := fun _ failure => mainUniverse.inScope failure
  NodeResidueAt := fun _ failure =>
    failure = .nodeFault ∨ failure = .overlap
  BridgeResidueAt := fun _ failure =>
    failure = .bridgeFault ∨ failure = .overlap
  AssumptionViolationAt := fun _ failure =>
    failure = .assumptionFault
  ScopeEscapeAt := fun _ failure =>
    failure = .scopeEscape

abbrev currentContext : FailureContext Snapshot FailureModel where
  snapshot := .current
  failureModel := .v1

def coverageEvidence : List Failure :=
  [.nodeFault, .bridgeFault, .assumptionFault, .scopeEscape]

def coverageCertificate :
    FailureCoverageCertificate
      coverageSystem currentContext mainSeal coverageEvidence where
  mandatoryNonempty := ⟨.nodeFault, Or.inl rfl⟩
  everyMandatoryCovered := by
    intro failure mandatory
    refine ⟨failure, ?_, ?_⟩
    · rcases mandatory with node | bridge | assumption | escape
      · subst failure
        simp [coverageEvidence]
      · subst failure
        simp [coverageEvidence]
      · subst failure
        simp [coverageEvidence]
      · subst failure
        simp [coverageEvidence]
    · exact
        ⟨mainUniverse.mandatoryInScope failure mandatory,
          rfl, rfl⟩

abbrev nodeFacts :
    FailureFacts semantics currentContext .nodeFault where
  node := .supported (Or.inl rfl)
  bridge := .refuted (by simp [semantics])
  assumption := .refuted (by simp [semantics])
  scopeEscape := .refuted (by simp [semantics])

abbrev bridgeFacts :
    FailureFacts semantics currentContext .bridgeFault where
  node := .refuted (by simp [semantics])
  bridge := .supported (Or.inl rfl)
  assumption := .refuted (by simp [semantics])
  scopeEscape := .refuted (by simp [semantics])

abbrev assumptionFacts :
    FailureFacts semantics currentContext .assumptionFault where
  node := .refuted (by simp [semantics])
  bridge := .refuted (by simp [semantics])
  assumption := .supported rfl
  scopeEscape := .refuted (by simp [semantics])

abbrev scopeEscapeFacts :
    FailureFacts semantics currentContext .scopeEscape where
  node := .refuted (by simp [semantics])
  bridge := .refuted (by simp [semantics])
  assumption := .refuted (by simp [semantics])
  scopeEscape := .supported rfl

abbrev overlapFacts :
    FailureFacts semantics currentContext .overlap where
  node := .supported (Or.inr rfl)
  bridge := .supported (Or.inr rfl)
  assumption := .refuted (by simp [semantics])
  scopeEscape := .refuted (by simp [semantics])

def factsAt :
    (failure : Failure) →
      Option (FailureFacts semantics currentContext failure)
  | .nodeFault => some nodeFacts
  | .bridgeFault => some bridgeFacts
  | .assumptionFault => some assumptionFacts
  | .scopeEscape => some scopeEscapeFacts
  | .overlap => none
  | .omittedFifth => none
  | .outside => none

def admittedWindow : AdmittedFailureWindow semantics currentContext where
  universeSeal := mainSeal
  coverageEvidence := coverageEvidence
  coverageCertificate := coverageCertificate
  factsAt := factsAt
  packetSound := by
    intro failure facts found
    cases failure with
    | nodeFault =>
      simp [factsAt] at found
      subst facts
      simp [semantics, coverageSystem, mainUniverse]
    | bridgeFault =>
      simp [factsAt] at found
      subst facts
      simp [semantics, coverageSystem, mainUniverse]
    | assumptionFault =>
      simp [factsAt] at found
      subst facts
      simp [semantics, coverageSystem, mainUniverse]
    | scopeEscape =>
      simp [factsAt] at found
      subst facts
      simp [semantics, coverageSystem, mainUniverse]
    | overlap =>
      simp [factsAt] at found
    | omittedFifth =>
      simp [factsAt] at found
    | outside =>
      simp [factsAt] at found
  packetComplete := by
    intro failure inScope
    cases failure with
    | nodeFault => exact ⟨nodeFacts, rfl⟩
    | bridgeFault => exact ⟨bridgeFacts, rfl⟩
    | assumptionFault => exact ⟨assumptionFacts, rfl⟩
    | scopeEscape => exact ⟨scopeEscapeFacts, rfl⟩
    | overlap =>
        simp [semantics, coverageSystem, mainUniverse] at inScope
    | omittedFifth =>
        simp [semantics, coverageSystem, mainUniverse] at inScope
    | outside =>
        simp [semantics, coverageSystem, mainUniverse] at inScope

def exhaustiveWindow : ExhaustiveFailureWindow semantics currentContext where
  admitted := admittedWindow
  packetClassified := by
    intro failure inScope
    cases failure with
    | nodeFault =>
        exact
          ⟨nodeFacts,
            .node (Or.inl rfl)
              (by simp [semantics])
              (by simp [semantics])
              (by simp [semantics]),
            rfl, rfl⟩
    | bridgeFault =>
        exact
          ⟨bridgeFacts,
            .bridge
              (by simp [semantics])
              (Or.inl rfl)
              (by simp [semantics])
              (by simp [semantics]),
            rfl, rfl⟩
    | assumptionFault =>
        exact
          ⟨assumptionFacts,
            .assumption
              (by simp [semantics])
              (by simp [semantics])
              rfl
              (by simp [semantics]),
            rfl, rfl⟩
    | scopeEscape =>
        exact
          ⟨scopeEscapeFacts,
            .scopeEscape
              (by simp [semantics])
              (by simp [semantics])
              (by simp [semantics])
              rfl,
            rfl, rfl⟩
    | overlap =>
        simp [semantics, coverageSystem, mainUniverse] at inScope
    | omittedFifth =>
        simp [semantics, coverageSystem, mainUniverse] at inScope
    | outside =>
        simp [semantics, coverageSystem, mainUniverse] at inScope

def observation
    (failure : Failure)
    (readout : RawFailureReadout ExceptionName := .observed) :
    RawFailureObservation semantics where
  claimedSnapshot := .current
  claimedFailureModel := .v1
  failure := failure
  readout := readout

/-! ## One positive witness per frozen class -/

theorem node_failure_is_derived :
    ∃ classification,
      deriveEndToEndFailure semantics currentContext (some admittedWindow)
          (observation .nodeFault) =
        .classified classification ∧
      classification.tag = .nodeResidue := by
  refine ⟨.node (Or.inl rfl) ?_ ?_ ?_, rfl, rfl⟩ <;>
    simp [semantics, observation]

theorem bridge_failure_is_derived :
    ∃ classification,
      deriveEndToEndFailure semantics currentContext (some admittedWindow)
          (observation .bridgeFault) =
        .classified classification ∧
      classification.tag = .bridgeResidue := by
  refine ⟨.bridge ?_ (Or.inl rfl) ?_ ?_, rfl, rfl⟩ <;>
    simp [semantics, observation]

theorem assumption_failure_is_derived :
    ∃ classification,
      deriveEndToEndFailure semantics currentContext (some admittedWindow)
          (observation .assumptionFault) =
        .classified classification ∧
      classification.tag = .assumptionViolation := by
  refine ⟨.assumption ?_ ?_ rfl ?_, rfl, rfl⟩ <;>
    simp [semantics, observation]

theorem scope_escape_failure_is_derived :
    ∃ classification,
      deriveEndToEndFailure semantics currentContext (some admittedWindow)
          (observation .scopeEscape) =
        .classified classification ∧
      classification.tag = .scopeEscape := by
  refine ⟨.scopeEscape ?_ ?_ ?_ rfl, rfl, rfl⟩ <;>
    simp [semantics, observation]

/-! ## Ambiguity, gaps, and raw exceptions never become green -/

def badUniverse : FailureUniverse Failure where
  inScope := fun failure =>
    failure = .nodeFault ∨ failure = .overlap ∨ failure = .outside
  mandatory := fun failure =>
    failure = .nodeFault ∨ failure = .overlap ∨ failure = .outside
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared := [.nodeFault, .overlap, .outside]

def badSeal : FailureUniverseSeal badUniverse where
  declaredSound := by
    intro failure member
    cases failure <;> simp [badUniverse] at member ⊢
  declaredComplete := by
    intro failure inScope
    cases failure <;> simp [badUniverse] at inScope ⊢

def badCoverageSystem :
    FailureEvidenceSystem Context Failure Failure where
  modelAt := fun _ => badUniverse
  AdmittedAt := fun _ evidence => badUniverse.inScope evidence
  CoversAt := fun _ evidence failure grade =>
    grade = .mandatory ∧ evidence = failure

def badSemantics : MetaFailureSemantics where
  Snapshot := Snapshot
  FailureModel := FailureModel
  Failure := Failure
  CoverageEvidence := Failure
  ExceptionName := ExceptionName
  snapshotDecidableEq := inferInstance
  failureModelDecidableEq := inferInstance
  failureDecidableEq := inferInstance
  coverage := badCoverageSystem
  AdmittedAt := fun _ failure => badUniverse.inScope failure
  NodeResidueAt := fun _ failure =>
    failure = .nodeFault ∨ failure = .overlap
  BridgeResidueAt := fun _ failure =>
    failure = .bridgeFault ∨ failure = .overlap
  AssumptionViolationAt := fun _ failure =>
    failure = .assumptionFault
  ScopeEscapeAt := fun _ failure =>
    failure = .scopeEscape

def badCoverageEvidence : List Failure :=
  [.nodeFault, .overlap, .outside]

def badCoverageCertificate :
    FailureCoverageCertificate
      badCoverageSystem currentContext badSeal badCoverageEvidence where
  mandatoryNonempty := ⟨.nodeFault, Or.inl rfl⟩
  everyMandatoryCovered := by
    intro failure mandatory
    refine ⟨failure, ?_, ?_⟩
    · rcases mandatory with node | overlap | outside
      · subst failure
        simp [badCoverageEvidence]
      · subst failure
        simp [badCoverageEvidence]
      · subst failure
        simp [badCoverageEvidence]
    · exact
        ⟨badUniverse.mandatoryInScope failure mandatory, rfl, rfl⟩

abbrev unknownNodeFacts :
    FailureFacts badSemantics currentContext .nodeFault where
  node := .supported (Or.inl rfl)
  bridge := .unknown
  assumption := .refuted (by simp [badSemantics])
  scopeEscape := .refuted (by simp [badSemantics])

abbrev badOverlapFacts :
    FailureFacts badSemantics currentContext .overlap where
  node := .supported (Or.inr rfl)
  bridge := .supported (Or.inr rfl)
  assumption := .refuted (by simp [badSemantics])
  scopeEscape := .refuted (by simp [badSemantics])

abbrev allRefutedOutsideFacts :
    FailureFacts badSemantics currentContext .outside where
  node := .refuted (by simp [badSemantics])
  bridge := .refuted (by simp [badSemantics])
  assumption := .refuted (by simp [badSemantics])
  scopeEscape := .refuted (by simp [badSemantics])

def badFactsAt :
    (failure : Failure) →
      Option (FailureFacts badSemantics currentContext failure)
  | .nodeFault => some unknownNodeFacts
  | .overlap => some badOverlapFacts
  | .outside => some allRefutedOutsideFacts
  | _ => none

def badWindow : AdmittedFailureWindow badSemantics currentContext where
  universeSeal := badSeal
  coverageEvidence := badCoverageEvidence
  coverageCertificate := badCoverageCertificate
  factsAt := badFactsAt
  packetSound := by
    intro failure facts found
    cases failure with
    | nodeFault =>
        simp [badFactsAt] at found
        subst facts
        simp [badSemantics, badCoverageSystem, badUniverse]
    | overlap =>
        simp [badFactsAt] at found
        subst facts
        simp [badSemantics, badCoverageSystem, badUniverse]
    | outside =>
        simp [badFactsAt] at found
        subst facts
        simp [badSemantics, badCoverageSystem, badUniverse]
    | bridgeFault => simp [badFactsAt] at found
    | assumptionFault => simp [badFactsAt] at found
    | scopeEscape => simp [badFactsAt] at found
    | omittedFifth => simp [badFactsAt] at found
  packetComplete := by
    intro failure inScope
    cases failure with
    | nodeFault => exact ⟨unknownNodeFacts, rfl⟩
    | overlap => exact ⟨badOverlapFacts, rfl⟩
    | outside => exact ⟨allRefutedOutsideFacts, rfl⟩
    | bridgeFault => simp [badSemantics, badCoverageSystem, badUniverse] at inScope
    | assumptionFault => simp [badSemantics, badCoverageSystem, badUniverse] at inScope
    | scopeEscape => simp [badSemantics, badCoverageSystem, badUniverse] at inScope
    | omittedFifth => simp [badSemantics, badCoverageSystem, badUniverse] at inScope

def badObservation (failure : Failure) : RawFailureObservation badSemantics where
  claimedSnapshot := .current
  claimedFailureModel := .v1
  failure := failure
  readout := .observed

theorem overlapping_classifiers_are_ambiguous :
    deriveEndToEndFailure badSemantics currentContext (some badWindow)
        (badObservation .overlap) =
      .refuse .ambiguousEvidence := by
  rfl

theorem unknown_evidence_is_gap :
    deriveEndToEndFailure badSemantics currentContext (some badWindow)
        (badObservation .nodeFault) =
      .refuse .evidenceGap := by
  rfl

theorem true_in_scope_all_refuted_is_evidence_gap :
    deriveEndToEndFailure badSemantics currentContext (some badWindow)
        (badObservation .outside) =
      .refuse .evidenceGap := by
  rfl

theorem ambiguous_window_cannot_be_exhaustive :
    ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
        exhaustive.admitted = badWindow :=
  refused_packet_cannot_inhabit_exhaustive_window
    badWindow .overlap (Or.inr (Or.inl rfl))
    badOverlapFacts rfl .ambiguousEvidence rfl

theorem unknown_window_cannot_be_exhaustive :
    ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
        exhaustive.admitted = badWindow :=
  refused_packet_cannot_inhabit_exhaustive_window
    badWindow .nodeFault (Or.inl rfl)
    unknownNodeFacts rfl .evidenceGap rfl

theorem all_refuted_window_cannot_be_exhaustive :
    ¬ ∃ exhaustive : ExhaustiveFailureWindow badSemantics currentContext,
        exhaustive.admitted = badWindow :=
  refused_packet_cannot_inhabit_exhaustive_window
    badWindow .outside (Or.inr (Or.inr rfl))
    allRefutedOutsideFacts rfl .evidenceGap rfl

theorem raw_exception_is_named_not_green :
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .nodeFault (.exception .scannerCrashed)) =
      .refuse (.rawException .scannerCrashed) := by
  rfl

theorem unknown_readout_is_gap_not_green :
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .nodeFault .unknown) =
      .refuse .evidenceGap := by
  rfl

/-! ## Sealed-universe countermodels -/

def omittedFifthUniverse : FailureUniverse Failure where
  inScope := fun failure =>
    mainUniverse.inScope failure ∨ failure = .omittedFifth
  mandatory := fun failure =>
    mainUniverse.mandatory failure ∨ failure = .omittedFifth
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared := mainUniverse.declared

theorem fifth_in_scope_failure_cannot_be_omitted_from_seal :
    ¬ FailureUniverseSeal omittedFifthUniverse := by
  intro universeSeal
  have declared :=
    universeSeal.declaredComplete .omittedFifth
      (Or.inr rfl)
  simp [omittedFifthUniverse, mainUniverse] at declared

def emptyUniverse : FailureUniverse Failure where
  inScope := fun failure => failure = .nodeFault
  mandatory := fun failure => failure = .nodeFault
  mandatoryInScope := by
    intro failure mandatory
    exact mandatory
  declared := []

theorem empty_universe_cannot_seal_nonempty_scope :
    ¬ FailureUniverseSeal emptyUniverse := by
  intro universeSeal
  have declared :=
    universeSeal.declaredComplete .nodeFault rfl
  simp [emptyUniverse] at declared

theorem unsealed_universe_is_refused :
    deriveEndToEndFailure semantics currentContext none
        (observation .nodeFault) =
      .refuse .universeUnsealed := by
  rfl

/-! ## Snapshot and failure-model substitution -/

abbrev staleObservation : RawFailureObservation semantics :=
  { observation .nodeFault with claimedSnapshot := .stale }

theorem wrong_snapshot_is_refused :
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        staleObservation =
      .refuse .staleSnapshot := by
  rfl

abbrev wrongModelObservation : RawFailureObservation semantics :=
  { observation .nodeFault with claimedFailureModel := .v2 }

theorem wrong_failure_model_is_refused :
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        wrongModelObservation =
      .refuse .failureModelMismatch := by
  rfl

theorem outside_failure_is_not_mislabeled_scope_escape :
    deriveEndToEndFailure semantics currentContext (some admittedWindow)
        (observation .outside) =
      .refuse .outsideSealedUniverse := by
  rfl

/-! ## Scoped exhaustion and uniqueness -/

theorem every_declared_failure_has_admitted_packet :
    ∀ failure, mainUniverse.inScope failure →
      ∃ facts,
        admittedWindow.factsAt failure = some facts ∧
          semantics.AdmittedAt currentContext failure :=
  every_in_scope_failure_has_admitted_packet admittedWindow

def scopedExhaustionWitness :=
  end_to_end_failure_classification_exhausted exhaustiveWindow

#print axioms CertifiedFailureClass.selected
#print axioms CertifiedFailureClass.excludes
#print axioms every_in_scope_failure_has_admitted_packet
#print axioms out_of_scope_failure_has_no_admitted_packet
#print axioms end_to_end_failure_classification_exhausted
#print axioms derived_failure_class_unique_tag
#print axioms node_failure_is_derived
#print axioms bridge_failure_is_derived
#print axioms assumption_failure_is_derived
#print axioms scope_escape_failure_is_derived
#print axioms overlapping_classifiers_are_ambiguous
#print axioms unknown_evidence_is_gap
#print axioms true_in_scope_all_refuted_is_evidence_gap
#print axioms ambiguous_window_cannot_be_exhaustive
#print axioms unknown_window_cannot_be_exhaustive
#print axioms all_refuted_window_cannot_be_exhaustive
#print axioms raw_exception_is_named_not_green
#print axioms unknown_readout_is_gap_not_green
#print axioms fifth_in_scope_failure_cannot_be_omitted_from_seal
#print axioms empty_universe_cannot_seal_nonempty_scope
#print axioms unsealed_universe_is_refused
#print axioms wrong_snapshot_is_refused
#print axioms wrong_failure_model_is_refused
#print axioms outside_failure_is_not_mislabeled_scope_escape
#print axioms scopedExhaustionWitness

end Residua.RCC.MetaFailureExhaustion.Tests


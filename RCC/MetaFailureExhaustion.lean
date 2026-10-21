import RCC.EffectClassification
import RCC.FailureCoverage

/-!
# RCC ME-1 End-to-end failure exhaustion

Relative to one exact snapshot, one admitted failure model, and one sealed
finite failure universe, raw failure evidence is mechanically classified as:

* a node residue;
* a bridge residue;
* an assumption violation; or
* a scope escape.

Instances provide the four proposition coordinates only.  They cannot provide
a status or classifier.  The common derivation admits exactly one supported
coordinate with the other three explicitly refuted.  Unknown evidence, empty
evidence, overlap, raw exceptions, stale contexts, and unsealed universes
produce named residues.

`scopeEscape` is itself an admitted in-scope failure kind.  A raw failure
outside the sealed universe is not silently upgraded to that class.  The
headline theorem is relative to the sealed universe and makes no claim about
all failures possible in reality.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.MetaFailureExhaustion

open Residua.RCC.EffectClassification
open Residua.RCC.FailureCoverage

universe u v w x

/-- Exact carrier for the sealed snapshot and failure-model identity. -/
structure FailureContext (Snapshot : Type u) (FailureModel : Type v) where
  snapshot : Snapshot
  failureModel : FailureModel

/-- Domain meanings for the four frozen ME-1 failure classes. -/
structure MetaFailureSemantics where
  Snapshot : Type u
  FailureModel : Type v
  Failure : Type w
  CoverageEvidence : Type x
  ExceptionName : Type x

  snapshotDecidableEq : DecidableEq Snapshot
  failureModelDecidableEq : DecidableEq FailureModel
  failureDecidableEq : DecidableEq Failure

  coverage :
    FailureEvidenceSystem
      (FailureContext Snapshot FailureModel)
      Failure CoverageEvidence

  AdmittedAt :
    FailureContext Snapshot FailureModel → Failure → Prop
  NodeResidueAt :
    FailureContext Snapshot FailureModel → Failure → Prop
  BridgeResidueAt :
    FailureContext Snapshot FailureModel → Failure → Prop
  AssumptionViolationAt :
    FailureContext Snapshot FailureModel → Failure → Prop
  ScopeEscapeAt :
    FailureContext Snapshot FailureModel → Failure → Prop

/-- Four proof coordinates for one exact context/failure pair. -/
structure FailureFacts
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (failure : K.Failure) where
  node : EvidenceState (K.NodeResidueAt context failure)
  bridge : EvidenceState (K.BridgeResidueAt context failure)
  assumption : EvidenceState (K.AssumptionViolationAt context failure)
  scopeEscape : EvidenceState (K.ScopeEscapeAt context failure)

def FailureFacts.hasUnknown
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (facts : FailureFacts K context failure) : Bool :=
  facts.node.isUnknown ||
    facts.bridge.isUnknown ||
    facts.assumption.isUnknown ||
    facts.scopeEscape.isUnknown

def FailureFacts.supportCount
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (facts : FailureFacts K context failure) : Nat :=
  (if facts.node.isSupported then 1 else 0) +
    (if facts.bridge.isSupported then 1 else 0) +
    (if facts.assumption.isSupported then 1 else 0) +
    (if facts.scopeEscape.isSupported then 1 else 0)

/-- Proof-carrying exclusive class; every alternative is explicitly refuted. -/
inductive CertifiedFailureClass
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (failure : K.Failure)
  | node
      (supported : K.NodeResidueAt context failure)
      (notBridge : ¬ K.BridgeResidueAt context failure)
      (notAssumption : ¬ K.AssumptionViolationAt context failure)
      (notScopeEscape : ¬ K.ScopeEscapeAt context failure)
  | bridge
      (notNode : ¬ K.NodeResidueAt context failure)
      (supported : K.BridgeResidueAt context failure)
      (notAssumption : ¬ K.AssumptionViolationAt context failure)
      (notScopeEscape : ¬ K.ScopeEscapeAt context failure)
  | assumption
      (notNode : ¬ K.NodeResidueAt context failure)
      (notBridge : ¬ K.BridgeResidueAt context failure)
      (supported : K.AssumptionViolationAt context failure)
      (notScopeEscape : ¬ K.ScopeEscapeAt context failure)
  | scopeEscape
      (notNode : ¬ K.NodeResidueAt context failure)
      (notBridge : ¬ K.BridgeResidueAt context failure)
      (notAssumption : ¬ K.AssumptionViolationAt context failure)
      (supported : K.ScopeEscapeAt context failure)

inductive FailureClassTag
  | nodeResidue
  | bridgeResidue
  | assumptionViolation
  | scopeEscape
  deriving DecidableEq, Repr

def CertifiedFailureClass.tag
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure} :
    CertifiedFailureClass K context failure → FailureClassTag
  | .node _ _ _ _ => .nodeResidue
  | .bridge _ _ _ _ => .bridgeResidue
  | .assumption _ _ _ _ => .assumptionViolation
  | .scopeEscape _ _ _ _ => .scopeEscape

def MetaFailureSemantics.ClassHolds
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (failure : K.Failure) : FailureClassTag → Prop
  | .nodeResidue => K.NodeResidueAt context failure
  | .bridgeResidue => K.BridgeResidueAt context failure
  | .assumptionViolation => K.AssumptionViolationAt context failure
  | .scopeEscape => K.ScopeEscapeAt context failure

theorem CertifiedFailureClass.selected
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (classification : CertifiedFailureClass K context failure) :
    K.ClassHolds context failure classification.tag := by
  cases classification with
  | node supported _ _ _ => exact supported
  | bridge _ supported _ _ => exact supported
  | assumption _ _ supported _ => exact supported
  | scopeEscape _ _ _ supported => exact supported

theorem CertifiedFailureClass.excludes
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (classification : CertifiedFailureClass K context failure)
    (other : FailureClassTag)
    (different : other ≠ classification.tag) :
    ¬ K.ClassHolds context failure other := by
  cases classification with
  | node _ notBridge notAssumption notScope =>
      cases other with
      | nodeResidue => exact (different rfl).elim
      | bridgeResidue => exact notBridge
      | assumptionViolation => exact notAssumption
      | scopeEscape => exact notScope
  | bridge notNode _ notAssumption notScope =>
      cases other with
      | nodeResidue => exact notNode
      | bridgeResidue => exact (different rfl).elim
      | assumptionViolation => exact notAssumption
      | scopeEscape => exact notScope
  | assumption notNode notBridge _ notScope =>
      cases other with
      | nodeResidue => exact notNode
      | bridgeResidue => exact notBridge
      | assumptionViolation => exact (different rfl).elim
      | scopeEscape => exact notScope
  | scopeEscape notNode notBridge notAssumption _ =>
      cases other with
      | nodeResidue => exact notNode
      | bridgeResidue => exact notBridge
      | assumptionViolation => exact notAssumption
      | scopeEscape => exact (different rfl).elim

inductive MetaFailureResidue
  | ambiguousEvidence
  | evidenceGap
  deriving DecidableEq, Repr

inductive MetaFailureResult
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (failure : K.Failure)
  | classified (classification : CertifiedFailureClass K context failure)
  | refuse (residue : MetaFailureResidue)

/-- Common four-way classifier.  There is no instance-supplied status. -/
def deriveFailureClass
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (facts : FailureFacts K context failure) :
    MetaFailureResult K context failure :=
  if 1 < facts.supportCount then
    .refuse .ambiguousEvidence
  else if facts.hasUnknown then
    .refuse .evidenceGap
  else
    match facts.node, facts.bridge, facts.assumption, facts.scopeEscape with
    | .supported node, .refuted notBridge,
        .refuted notAssumption, .refuted notScope =>
        .classified (.node node notBridge notAssumption notScope)
    | .refuted notNode, .supported bridge,
        .refuted notAssumption, .refuted notScope =>
        .classified (.bridge notNode bridge notAssumption notScope)
    | .refuted notNode, .refuted notBridge,
        .supported assumption, .refuted notScope =>
        .classified (.assumption notNode notBridge assumption notScope)
    | .refuted notNode, .refuted notBridge,
        .refuted notAssumption, .supported scope =>
        .classified (.scopeEscape notNode notBridge notAssumption scope)
    | _, _, _, _ =>
        .refuse .evidenceGap

structure DerivedFailureClassification
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    (facts : FailureFacts K context failure) where
  classification : CertifiedFailureClass K context failure
  derived : deriveFailureClass facts = .classified classification

/--
Sealed admitted window.  `factsAt` is indexed by the exact context and failure.
Soundness prevents unadmitted packets; completeness prevents an in-scope
failure from disappearing.
-/
structure AdmittedFailureWindow
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel) where
  universeSeal : FailureUniverseSeal (K.coverage.modelAt context)
  coverageEvidence : List K.CoverageEvidence
  coverageCertificate :
    FailureCoverageCertificate K.coverage context
      universeSeal coverageEvidence
  factsAt : (failure : K.Failure) → Option (FailureFacts K context failure)
  packetSound :
    ∀ failure facts,
      factsAt failure = some facts →
        (K.coverage.modelAt context).inScope failure ∧
          K.AdmittedAt context failure
  packetComplete :
    ∀ failure,
      (K.coverage.modelAt context).inScope failure →
        ∃ facts, factsAt failure = some facts

/--
Stronger ME-1 closure certificate.

An admitted window may honestly contain ambiguity or an evidence gap.  Only an
`ExhaustiveFailureWindow` proves that every in-scope packet actually derives
one of the four certified classes.
-/
structure ExhaustiveFailureWindow
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel) where
  admitted : AdmittedFailureWindow K context
  packetClassified :
    ∀ failure,
      (K.coverage.modelAt context).inScope failure →
        ∃ facts classification,
          admitted.factsAt failure = some facts ∧
            deriveFailureClass facts = .classified classification

inductive RawFailureReadout (ExceptionName : Type u)
  | observed
  | exception (name : ExceptionName)
  | unknown

structure RawFailureObservation (K : MetaFailureSemantics) where
  claimedSnapshot : K.Snapshot
  claimedFailureModel : K.FailureModel
  failure : K.Failure
  readout : RawFailureReadout K.ExceptionName

inductive EndToEndFailureResidue (ExceptionName : Type u)
  | universeUnsealed
  | staleSnapshot
  | failureModelMismatch
  | outsideSealedUniverse
  | ambiguousEvidence
  | evidenceGap
  | rawException (name : ExceptionName)
  deriving DecidableEq, Repr

inductive EndToEndFailureResult
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (failure : K.Failure)
  | classified (classification : CertifiedFailureClass K context failure)
  | refuse (residue : EndToEndFailureResidue K.ExceptionName)

/-- Total exact-context ME-1 classification. -/
def deriveEndToEndFailure
    (K : MetaFailureSemantics)
    (context : FailureContext K.Snapshot K.FailureModel)
    (window : Option (AdmittedFailureWindow K context))
    (observation : RawFailureObservation K) :
    EndToEndFailureResult K context observation.failure :=
  letI := K.snapshotDecidableEq
  letI := K.failureModelDecidableEq
  letI := K.failureDecidableEq
  if _snapshotExact : observation.claimedSnapshot = context.snapshot then
    if _modelExact :
        observation.claimedFailureModel = context.failureModel then
      match window with
      | none =>
          .refuse .universeUnsealed
      | some admitted =>
          if _declared :
              observation.failure ∈
                (K.coverage.modelAt context).declared then
            match observation.readout with
            | .exception name =>
                .refuse (.rawException name)
            | .unknown =>
                .refuse .evidenceGap
            | .observed =>
                match admitted.factsAt observation.failure with
                | none =>
                    .refuse .evidenceGap
                | some facts =>
                    match deriveFailureClass facts with
                    | .classified classification =>
                        .classified classification
                    | .refuse .ambiguousEvidence =>
                        .refuse .ambiguousEvidence
                    | .refuse .evidenceGap =>
                        .refuse .evidenceGap
          else
            .refuse .outsideSealedUniverse
    else
      .refuse .failureModelMismatch
  else
    .refuse .staleSnapshot

/-- Every in-scope failure has an exact indexed evidence packet. -/
theorem every_in_scope_failure_has_admitted_packet
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    (window : AdmittedFailureWindow K context)
    (failure : K.Failure)
    (inScope : (K.coverage.modelAt context).inScope failure) :
    ∃ facts,
      window.factsAt failure = some facts ∧ K.AdmittedAt context failure := by
  obtain ⟨facts, found⟩ := window.packetComplete failure inScope
  exact ⟨facts, found, (window.packetSound failure facts found).2⟩

/-- A packet cannot exist for a failure outside the sealed admitted scope. -/
theorem out_of_scope_failure_has_no_admitted_packet
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    (window : AdmittedFailureWindow K context)
    (failure : K.Failure)
    (outOfScope : ¬ (K.coverage.modelAt context).inScope failure) :
    window.factsAt failure = none := by
  cases found : window.factsAt failure with
  | none => rfl
  | some facts =>
      exact (outOfScope (window.packetSound failure facts found).1).elim

/--
An admitted window has a total, named disposition for every in-scope packet.
This deliberately is not called exhaustion: ambiguity and gaps remain lawful
non-green results at this weaker grade.
-/
theorem admitted_failure_packet_has_total_disposition
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    (window : AdmittedFailureWindow K context)
    (failure : K.Failure)
    (inScope : (K.coverage.modelAt context).inScope failure) :
    ∃ facts,
      window.factsAt failure = some facts ∧
        match deriveFailureClass facts with
        | .classified classification =>
            K.ClassHolds context failure classification.tag
        | .refuse .ambiguousEvidence => True
        | .refuse .evidenceGap => True := by
  obtain ⟨facts, found⟩ := window.packetComplete failure inScope
  refine ⟨facts, found, ?_⟩
  cases derived : deriveFailureClass facts with
  | classified classification =>
      exact classification.selected
  | refuse residue =>
      cases residue <;> trivial

/--
ME-1 headline theorem.  Exhaustion is scoped to the sealed admitted universe:
every in-scope failure has exact facts, a mechanically derived exclusive class,
explicit admission, and the selected semantic proposition.
-/
theorem end_to_end_failure_classification_exhausted
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    (window : ExhaustiveFailureWindow K context)
    (failure : K.Failure)
    (inScope : (K.coverage.modelAt context).inScope failure) :
    ∃ facts classification,
      window.admitted.factsAt failure = some facts ∧
        deriveFailureClass facts = .classified classification ∧
        K.AdmittedAt context failure ∧
        K.ClassHolds context failure classification.tag := by
  obtain ⟨facts, classification, found, derived⟩ :=
    window.packetClassified failure inScope
  have admitted :=
    (window.admitted.packetSound failure facts found).2
  exact
    ⟨facts, classification, found, derived,
      admitted, classification.selected⟩

/--
One refused in-scope packet is a constructive obstruction to an exhaustive
certificate over that exact admitted window.
-/
theorem refused_packet_cannot_inhabit_exhaustive_window
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    (window : AdmittedFailureWindow K context)
    (failure : K.Failure)
    (inScope : (K.coverage.modelAt context).inScope failure)
    (facts : FailureFacts K context failure)
    (found : window.factsAt failure = some facts)
    (residue : MetaFailureResidue)
    (refused : deriveFailureClass facts = .refuse residue) :
    ¬ ∃ exhaustive : ExhaustiveFailureWindow K context,
        exhaustive.admitted = window := by
  rintro ⟨exhaustive, sameWindow⟩
  obtain ⟨otherFacts, classification, otherFound, classified⟩ :=
    exhaustive.packetClassified failure inScope
  have foundAtExhaustive :
      exhaustive.admitted.factsAt failure = some facts := by
    rw [sameWindow]
    exact found
  have sameFacts : facts = otherFacts :=
    Option.some.inj (foundAtExhaustive.symm.trans otherFound)
  subst otherFacts
  have impossible :
      MetaFailureResult.refuse residue =
        MetaFailureResult.classified classification :=
    refused.symm.trans classified
  cases impossible

/-- Erased class uniqueness follows from the derivation being a function. -/
theorem derived_failure_class_unique_tag
    {K : MetaFailureSemantics}
    {context : FailureContext K.Snapshot K.FailureModel}
    {failure : K.Failure}
    {facts : FailureFacts K context failure}
    (left right : DerivedFailureClassification facts) :
    left.classification.tag = right.classification.tag := by
  have sameResult :
      MetaFailureResult.classified left.classification =
        MetaFailureResult.classified right.classification :=
    left.derived.symm.trans right.derived
  have sameClass : left.classification = right.classification :=
    MetaFailureResult.classified.inj sameResult
  exact congrArg CertifiedFailureClass.tag sameClass

end Residua.RCC.MetaFailureExhaustion

import RCC.EvidenceModalityTransport

/-!
# RCC CM-3 quantitative claim binding

CM-1 gives probabilistic and statistical claims distinct type indices.  CM-2
requires a proof-carrying bridge before evidence is retargeted.  Neither fact
alone says that a bridge retained the quantitative coordinates on which the
judgment depends.

CM-3 closes that gap in two places:

* an untrusted quantitative evidence attempt must supply every security or
  confidence coordinate and match the claim exactly before it is rebuilt as
  typed CM-1 evidence; and
* a CM-2 retargeting bridge may produce a quantitative judgment only when the
  complete judgment identity is unchanged.

The probabilistic identity contains the experiment, adversary class, security
parameter, and probability bound.  The statistical identity contains the
population, sample frame, estimator, sample size, and confidence ratio.
Missing and rewritten coordinates take named refusal branches.  A successful
transport carries an equality proof for the complete quantitative identity.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.QuantitativeClaimBinding

open Residua.RCC.ClaimModality
open Residua.RCC.EvidenceModalityTransport

/-- The two CM-1 modalities whose judgments carry quantitative coordinates. -/
inductive QuantitativeKind
  | probabilistic
  | statistical
  deriving DecidableEq, Repr

/-- Recover the existing CM-1 modality index from a quantitative kind. -/
def QuantitativeKind.modality : QuantitativeKind → Modality
  | .probabilistic => .probabilistic
  | .statistical => .statistical

/-- All coordinates on which a probabilistic claim/evidence pair depends. -/
structure ProbabilisticMetadata where
  experimentQ : String
  adversaryClassQ : String
  securityParameter : Nat
  boundNumerator : Nat
  boundDenominator : Nat
  deriving DecidableEq, Repr

/-- All coordinates on which a statistical claim/evidence pair depends. -/
structure StatisticalMetadata where
  estimatorQ : String
  sampleFrameQ : String
  sampleSize : Nat
  confidenceNumerator : Nat
  confidenceDenominator : Nat
  deriving DecidableEq, Repr

/-- The metadata family indexed by quantitative claim kind. -/
def QuantitativeMetadata : QuantitativeKind → Type
  | .probabilistic => ProbabilisticMetadata
  | .statistical => StatisticalMetadata

/-- Extract the full probabilistic coordinate tuple from a CM-1 claim. -/
def probabilisticClaimMetadata :
    Claim .probabilistic → ProbabilisticMetadata
  | .probabilistic _ experimentQ adversaryClassQ
      securityParameter boundNumerator boundDenominator =>
      { experimentQ
        adversaryClassQ
        securityParameter
        boundNumerator
        boundDenominator }

/-- Extract the full probabilistic coordinate tuple from CM-1 evidence. -/
def probabilisticEvidenceMetadata :
    Evidence .probabilistic → ProbabilisticMetadata
  | .probabilistic experimentQ adversaryClassQ _
      securityParameter boundNumerator boundDenominator =>
      { experimentQ
        adversaryClassQ
        securityParameter
        boundNumerator
        boundDenominator }

/-- Extract the complete statistical coordinate tuple from a CM-1 claim. -/
def statisticalClaimMetadata :
    Claim .statistical → StatisticalMetadata
  | .statistical _ estimatorQ _ sampleFrameQ
      sampleSize confidenceNumerator confidenceDenominator =>
      { estimatorQ
        sampleFrameQ
        sampleSize
        confidenceNumerator
        confidenceDenominator }

/-- Extract the complete statistical coordinate tuple from CM-1 evidence. -/
def statisticalEvidenceMetadata :
    Evidence .statistical → StatisticalMetadata
  | .statistical sampleFrameQ estimatorQ _
      sampleSize confidenceNumerator confidenceDenominator =>
      { estimatorQ
        sampleFrameQ
        sampleSize
        confidenceNumerator
        confidenceDenominator }

/-- Uniform claim-side metadata projection for the two quantitative kinds. -/
def quantitativeClaimMetadata :
    (kind : QuantitativeKind) →
      Claim kind.modality → QuantitativeMetadata kind
  | .probabilistic, claim => probabilisticClaimMetadata claim
  | .statistical, claim => statisticalClaimMetadata claim

/-- Uniform evidence-side metadata projection for quantitative evidence. -/
def quantitativeEvidenceMetadata :
    (kind : QuantitativeKind) →
      Evidence kind.modality → QuantitativeMetadata kind
  | .probabilistic, evidence => probabilisticEvidenceMetadata evidence
  | .statistical, evidence => statisticalEvidenceMetadata evidence

/--
Canonical probabilistic judgment coordinates.

The claim identity is included in addition to all security coordinates, so a
transport cannot retarget a distinct claim with coincidentally equal bounds.
-/
structure ProbabilisticJudgmentIdentity where
  claimQ : String
  metadata : ProbabilisticMetadata
  deriving DecidableEq, Repr

/--
Canonical statistical judgment coordinates.

`populationQ` remains claim-side in CM-1, but it is still load-bearing for
judgment identity and therefore participates in transport equality.
-/
structure StatisticalJudgmentIdentity where
  claimQ : String
  populationQ : String
  metadata : StatisticalMetadata
  deriving DecidableEq, Repr

/-- Complete judgment identity indexed by quantitative kind. -/
def QuantitativeJudgmentIdentity : QuantitativeKind → Type
  | .probabilistic => ProbabilisticJudgmentIdentity
  | .statistical => StatisticalJudgmentIdentity

/-- Equality of typed identities is decidable without erasing their kind. -/
instance quantitativeJudgmentIdentityDecidableEq
    (kind : QuantitativeKind) :
    DecidableEq (QuantitativeJudgmentIdentity kind) := by
  cases kind with
  | probabilistic =>
      change DecidableEq ProbabilisticJudgmentIdentity
      exact inferInstance
  | statistical =>
      change DecidableEq StatisticalJudgmentIdentity
      exact inferInstance

/-- Derive probabilistic judgment identity from the claim and bound metadata. -/
def probabilisticJudgmentIdentity
    (claim : Claim .probabilistic)
    (metadata : ProbabilisticMetadata) :
    ProbabilisticJudgmentIdentity :=
  match claim with
  | .probabilistic claimQ _ _ _ _ _ =>
      { claimQ, metadata }

/-- Derive statistical judgment identity from claim and bound metadata. -/
def statisticalJudgmentIdentity
    (claim : Claim .statistical)
    (metadata : StatisticalMetadata) :
    StatisticalJudgmentIdentity :=
  match claim with
  | .statistical claimQ _ populationQ _ _ _ _ =>
      { claimQ, populationQ, metadata }

/-- Uniform complete quantitative judgment identity. -/
def quantitativeJudgmentIdentity
    (kind : QuantitativeKind)
    (claim : Claim kind.modality)
    (metadata : QuantitativeMetadata kind) :
    QuantitativeJudgmentIdentity kind :=
  match kind with
  | .probabilistic =>
      probabilisticJudgmentIdentity claim metadata
  | .statistical =>
      statisticalJudgmentIdentity claim metadata

/-- Existential identity envelope used only in typed refusal payloads. -/
inductive SomeQuantitativeJudgmentIdentity
  | probabilistic (identity : ProbabilisticJudgmentIdentity)
  | statistical (identity : StatisticalJudgmentIdentity)
  deriving DecidableEq, Repr

/-- Erase a kind-indexed identity without erasing any quantitative field. -/
def eraseQuantitativeJudgmentIdentity :
    {kind : QuantitativeKind} →
      QuantitativeJudgmentIdentity kind →
      SomeQuantitativeJudgmentIdentity
  | .probabilistic, identity => .probabilistic identity
  | .statistical, identity => .statistical identity

/-- Untrusted quantitative claims at the CM-3 boundary. -/
inductive QuantitativeClaimEnvelope
  | probabilistic (claim : Claim .probabilistic)
  | statistical (claim : Claim .statistical)

/-- The type-derived quantitative kind of a claim envelope. -/
def QuantitativeClaimEnvelope.kind :
    QuantitativeClaimEnvelope → QuantitativeKind
  | .probabilistic _ => .probabilistic
  | .statistical _ => .statistical

/--
Possibly incomplete probabilistic evidence coordinates at a serialization or
agent boundary.  Absence is data and is never filled with a default.
-/
structure ProbabilisticEvidenceAttempt where
  experimentQ : Option String
  adversaryClassQ : Option String
  proofQ : String
  securityParameter : Option Nat
  boundNumerator : Option Nat
  boundDenominator : Option Nat
  deriving DecidableEq, Repr

/--
Possibly incomplete statistical evidence coordinates at an untrusted
boundary.  Sample frame and confidence are retained independently.
-/
structure StatisticalEvidenceAttempt where
  sampleFrameQ : Option String
  estimatorQ : Option String
  reportQ : String
  sampleSize : Option Nat
  confidenceNumerator : Option Nat
  confidenceDenominator : Option Nat
  deriving DecidableEq, Repr

/-- Untrusted quantitative evidence, still before CM-1 evidence rebuilding. -/
inductive QuantitativeEvidenceAttempt
  | probabilistic (attempt : ProbabilisticEvidenceAttempt)
  | statistical (attempt : StatisticalEvidenceAttempt)
  deriving DecidableEq, Repr

/-- The type-derived kind of an evidence attempt. -/
def QuantitativeEvidenceAttempt.kind :
    QuantitativeEvidenceAttempt → QuantitativeKind
  | .probabilistic _ => .probabilistic
  | .statistical _ => .statistical

/-- Every independently audited quantitative coordinate has a typed name. -/
inductive QuantitativeField
  | experiment
  | adversaryClass
  | securityParameter
  | probabilityBoundNumerator
  | probabilityBoundDenominator
  | estimator
  | sampleFrame
  | sampleSize
  | confidenceNumerator
  | confidenceDenominator
  deriving DecidableEq, Repr

/-- Values carried by a field-mismatch residue. -/
inductive QuantitativeValue
  | text (value : String)
  | natural (value : Nat)
  deriving DecidableEq, Repr

/-- All CM-3 refusal branches are named and retain their coordinates. -/
inductive QuantitativeClaimResidue
  | modalityMismatch
      (expected actual : QuantitativeKind)
  | metadataMissing
      (kind : QuantitativeKind)
      (field : QuantitativeField)
  | metadataMismatch
      (kind : QuantitativeKind)
      (field : QuantitativeField)
      (expected actual : QuantitativeValue)
  | lawfulBridgeMissing
      (kind : QuantitativeKind)
  | judgmentIdentityChanged
      (source target : SomeQuantitativeJudgmentIdentity)
  deriving DecidableEq, Repr

/-- Check one required string coordinate without supplying a default. -/
def checkTextCoordinate
    (kind : QuantitativeKind)
    (field : QuantitativeField)
    (expected : String) :
    Option String → Except QuantitativeClaimResidue Unit
  | none => .error (.metadataMissing kind field)
  | some actual =>
      if actual = expected then
        .ok ()
      else
        .error
          (.metadataMismatch kind field
            (.text expected) (.text actual))

/-- Check one required natural-number coordinate without supplying a default. -/
def checkNatCoordinate
    (kind : QuantitativeKind)
    (field : QuantitativeField)
    (expected : Nat) :
    Option Nat → Except QuantitativeClaimResidue Unit
  | none => .error (.metadataMissing kind field)
  | some actual =>
      if actual = expected then
        .ok ()
      else
        .error
          (.metadataMismatch kind field
            (.natural expected) (.natural actual))

/-- Validate every probabilistic security coordinate in a fixed order. -/
def validateProbabilisticAttempt
    (expected : ProbabilisticMetadata)
    (attempt : ProbabilisticEvidenceAttempt) :
    Except QuantitativeClaimResidue Unit := do
  checkTextCoordinate .probabilistic .experiment
    expected.experimentQ attempt.experimentQ
  checkTextCoordinate .probabilistic .adversaryClass
    expected.adversaryClassQ attempt.adversaryClassQ
  checkNatCoordinate .probabilistic .securityParameter
    expected.securityParameter attempt.securityParameter
  checkNatCoordinate .probabilistic .probabilityBoundNumerator
    expected.boundNumerator attempt.boundNumerator
  checkNatCoordinate .probabilistic .probabilityBoundDenominator
    expected.boundDenominator attempt.boundDenominator

/-- Validate every statistical sample/confidence coordinate in a fixed order. -/
def validateStatisticalAttempt
    (expected : StatisticalMetadata)
    (attempt : StatisticalEvidenceAttempt) :
    Except QuantitativeClaimResidue Unit := do
  checkTextCoordinate .statistical .sampleFrame
    expected.sampleFrameQ attempt.sampleFrameQ
  checkTextCoordinate .statistical .estimator
    expected.estimatorQ attempt.estimatorQ
  checkNatCoordinate .statistical .sampleSize
    expected.sampleSize attempt.sampleSize
  checkNatCoordinate .statistical .confidenceNumerator
    expected.confidenceNumerator attempt.confidenceNumerator
  checkNatCoordinate .statistical .confidenceDenominator
    expected.confidenceDenominator attempt.confidenceDenominator

/-- Rebuild full CM-1 probabilistic evidence only from validated metadata. -/
def probabilisticEvidenceFromMetadata
    (metadata : ProbabilisticMetadata)
    (proofQ : String) :
    Evidence .probabilistic :=
  .probabilistic
    metadata.experimentQ
    metadata.adversaryClassQ
    proofQ
    metadata.securityParameter
    metadata.boundNumerator
    metadata.boundDenominator

/-- Rebuild full CM-1 statistical evidence only from validated metadata. -/
def statisticalEvidenceFromMetadata
    (metadata : StatisticalMetadata)
    (reportQ : String) :
    Evidence .statistical :=
  .statistical
    metadata.sampleFrameQ
    metadata.estimatorQ
    reportQ
    metadata.sampleSize
    metadata.confidenceNumerator
    metadata.confidenceDenominator

/-- Rebuilt probabilistic evidence exposes exactly the supplied metadata. -/
theorem probabilistic_evidence_metadata_roundtrip
    (metadata : ProbabilisticMetadata)
    (proofQ : String) :
    probabilisticEvidenceMetadata
        (probabilisticEvidenceFromMetadata metadata proofQ) =
      metadata := by
  cases metadata
  rfl

/-- Rebuilt statistical evidence exposes exactly the supplied metadata. -/
theorem statistical_evidence_metadata_roundtrip
    (metadata : StatisticalMetadata)
    (reportQ : String) :
    statisticalEvidenceMetadata
        (statisticalEvidenceFromMetadata metadata reportQ) =
      metadata := by
  cases metadata
  rfl

/--
A quantitative claim/evidence pair whose complete metadata agreement is in
the type.  This is still pre-verification; semantic acceptance remains with a
modality-indexed verifier exactly as in CM-1.
-/
inductive BoundQuantitativePacket
  | probabilistic
      (claim : Claim .probabilistic)
      (evidence : Evidence .probabilistic)
      (metadata : ProbabilisticMetadata)
      (claimBinding :
        probabilisticClaimMetadata claim = metadata)
      (evidenceBinding :
        probabilisticEvidenceMetadata evidence = metadata)
  | statistical
      (claim : Claim .statistical)
      (evidence : Evidence .statistical)
      (metadata : StatisticalMetadata)
      (claimBinding :
        statisticalClaimMetadata claim = metadata)
      (evidenceBinding :
        statisticalEvidenceMetadata evidence = metadata)

/-- Total CM-3 evidence-binding result. -/
inductive QuantitativeBindingResult
  | bound (packet : BoundQuantitativePacket)
  | refuse (residue : QuantitativeClaimResidue)

/--
Rebuild CM-1 evidence only after all quantitative coordinates have matched.

The proof/report payload is retained, but no caller-supplied quantitative
coordinate survives by default: the rebuilt evidence uses the exact
claim-derived metadata after the checks succeed.
-/
def bindQuantitativeEvidence :
    QuantitativeClaimEnvelope →
      QuantitativeEvidenceAttempt →
      QuantitativeBindingResult
  | .probabilistic claim, .probabilistic attempt =>
      let expected := probabilisticClaimMetadata claim
      match validateProbabilisticAttempt expected attempt with
      | .error residue => .refuse residue
      | .ok () =>
          let evidence :=
            probabilisticEvidenceFromMetadata expected attempt.proofQ
          .bound
            (.probabilistic claim evidence expected rfl (by
              exact
                probabilistic_evidence_metadata_roundtrip
                  expected attempt.proofQ))
  | .statistical claim, .statistical attempt =>
      let expected := statisticalClaimMetadata claim
      match validateStatisticalAttempt expected attempt with
      | .error residue => .refuse residue
      | .ok () =>
          let evidence :=
            statisticalEvidenceFromMetadata expected attempt.reportQ
          .bound
            (.statistical claim evidence expected rfl (by
              exact
                statistical_evidence_metadata_roundtrip
                  expected attempt.reportQ))
  | claim, evidence =>
      .refuse
        (.modalityMismatch claim.kind evidence.kind)

/--
An accepted quantitative judgment with complete claim/evidence metadata
agreement.  `VerifiedClaim` supplies CM-1 semantic acceptance; the two binding
proofs supply CM-3 parameter retention.
-/
structure QuantitativeJudgment
    (verifier : ModalityVerifier)
    (kind : QuantitativeKind) where
  verified : VerifiedClaim verifier kind.modality
  metadata : QuantitativeMetadata kind
  claimBinding :
    quantitativeClaimMetadata kind verified.claim = metadata
  evidenceBinding :
    quantitativeEvidenceMetadata kind verified.evidence = metadata

/-- Construct a quantitative judgment from an accepted, metadata-equal pair. -/
def QuantitativeJudgment.ofVerified
    {verifier : ModalityVerifier}
    {kind : QuantitativeKind}
    (verified : VerifiedClaim verifier kind.modality)
    (metadataAgreement :
      quantitativeEvidenceMetadata kind verified.evidence =
        quantitativeClaimMetadata kind verified.claim) :
    QuantitativeJudgment verifier kind :=
  { verified
    metadata := quantitativeClaimMetadata kind verified.claim
    claimBinding := rfl
    evidenceBinding := metadataAgreement }

/-- Every quantitative judgment exposes its complete typed identity. -/
def QuantitativeJudgment.identity
    {verifier : ModalityVerifier}
    {kind : QuantitativeKind}
    (judgment : QuantitativeJudgment verifier kind) :
    QuantitativeJudgmentIdentity kind :=
  quantitativeJudgmentIdentity
    kind judgment.verified.claim judgment.metadata

/--
A quantitative transport either preserves the exact judgment or retargets it
through the existing CM-2 proof-carrying authorization.
-/
inductive QuantitativeTransportRequest
    (verifier : ModalityVerifier)
    (kind : QuantitativeKind)
  | preserve
      (transportQ : String)
      (source : QuantitativeJudgment verifier kind)
  | retarget
      (transportQ : String)
      (source : QuantitativeJudgment verifier kind)
      (targetClaim : Claim kind.modality)
      (targetEvidence : Evidence kind.modality)
      (targetMetadata : QuantitativeMetadata kind)
      (targetClaimBinding :
        quantitativeClaimMetadata kind targetClaim = targetMetadata)
      (targetEvidenceBinding :
        quantitativeEvidenceMetadata kind targetEvidence = targetMetadata)
      (authorization :
        RetargetAuthorization
          verifier source.verified targetClaim targetEvidence)

/--
Successful transport carries an equality proof for complete judgment identity.
The refusal branch retains either the absent bridge or both changed identities.
-/
inductive QuantitativeTransportResult
    (verifier : ModalityVerifier)
    (kind : QuantitativeKind)
  | transported
      (transportQ : String)
      (sourceIdentity : QuantitativeJudgmentIdentity kind)
      (judgment : QuantitativeJudgment verifier kind)
      (identityPreserved : judgment.identity = sourceIdentity)
  | refuse
      (residue : QuantitativeClaimResidue)

/-- Whether CM-3 produced an accepted, identity-preserving transport. -/
def QuantitativeTransportResult.isTransported :
    QuantitativeTransportResult verifier kind → Bool
  | .transported _ _ _ _ => true
  | .refuse _ => false

/--
The uniform CM-3 transport derivation.

CM-2 bridge authority is necessary for retargeting but not sufficient: the
complete quantitative identity must also be equal.  Identity comparison
happens before bridge use so a bridge can never authorize parameter rewriting.
-/
def deriveQuantitativeTransport
    (request : QuantitativeTransportRequest verifier kind) :
    QuantitativeTransportResult verifier kind :=
  match request with
  | .preserve transportQ source =>
      .transported transportQ source.identity source rfl
  | .retarget transportQ source targetClaim targetEvidence targetMetadata
      targetClaimBinding targetEvidenceBinding authorization =>
      let sourceIdentity := source.identity
      let targetIdentity :=
        quantitativeJudgmentIdentity kind targetClaim targetMetadata
      match
          quantitativeJudgmentIdentityDecidableEq
            kind targetIdentity sourceIdentity with
      | .isTrue identityEquality =>
          match authorization with
          | .absent =>
              .refuse (.lawfulBridgeMissing kind)
          | .certified certificate =>
              let targetVerified : VerifiedClaim verifier kind.modality :=
                { claim := targetClaim
                  evidence := targetEvidence
                  accepted :=
                    certificate.preservesAcceptance
                      source.verified.accepted }
              let targetJudgment : QuantitativeJudgment verifier kind :=
                { verified := targetVerified
                  metadata := targetMetadata
                  claimBinding := targetClaimBinding
                  evidenceBinding := targetEvidenceBinding }
              .transported transportQ sourceIdentity targetJudgment
                identityEquality
      | .isFalse _ =>
          .refuse
            (.judgmentIdentityChanged
              (eraseQuantitativeJudgmentIdentity sourceIdentity)
              (eraseQuantitativeJudgmentIdentity targetIdentity))

/-- Every transported result retains the complete source judgment identity. -/
theorem quantitative_transport_result_retains_identity
    (result : QuantitativeTransportResult verifier kind) :
    match result with
    | .transported _ sourceIdentity judgment _ =>
        judgment.identity = sourceIdentity
    | .refuse _ => True := by
  cases result with
  | transported _ _ _ identityPreserved =>
      exact identityPreserved
  | refuse _ =>
      exact True.intro

/-- A changed complete identity is always refused, even with a CM-2 bridge. -/
theorem changed_quantitative_identity_is_refused
    (transportQ : String)
    (source : QuantitativeJudgment verifier kind)
    (targetClaim : Claim kind.modality)
    (targetEvidence : Evidence kind.modality)
    (targetMetadata : QuantitativeMetadata kind)
    (targetClaimBinding :
      quantitativeClaimMetadata kind targetClaim = targetMetadata)
    (targetEvidenceBinding :
      quantitativeEvidenceMetadata kind targetEvidence = targetMetadata)
    (authorization :
      RetargetAuthorization
        verifier source.verified targetClaim targetEvidence)
    (changed :
      quantitativeJudgmentIdentity kind targetClaim targetMetadata ≠
        source.identity) :
    deriveQuantitativeTransport
        (.retarget transportQ source targetClaim targetEvidence
          targetMetadata targetClaimBinding targetEvidenceBinding
          authorization) =
      .refuse
        (.judgmentIdentityChanged
          (eraseQuantitativeJudgmentIdentity source.identity)
          (eraseQuantitativeJudgmentIdentity
            (quantitativeJudgmentIdentity
              kind targetClaim targetMetadata))) := by
  have identityDecision :
      quantitativeJudgmentIdentityDecidableEq kind
          (quantitativeJudgmentIdentity kind targetClaim targetMetadata)
          source.identity =
        Decidable.isFalse changed := by
    apply Subsingleton.elim
  simp only [deriveQuantitativeTransport, identityDecision]

/-- Exact quantitative coordinates still require CM-2 bridge authority. -/
theorem unbridged_quantitative_retarget_is_refused
    (transportQ : String)
    (source : QuantitativeJudgment verifier kind)
    (targetClaim : Claim kind.modality)
    (targetEvidence : Evidence kind.modality)
    (targetMetadata : QuantitativeMetadata kind)
    (targetClaimBinding :
      quantitativeClaimMetadata kind targetClaim = targetMetadata)
    (targetEvidenceBinding :
      quantitativeEvidenceMetadata kind targetEvidence = targetMetadata)
    (sameIdentity :
      quantitativeJudgmentIdentity kind targetClaim targetMetadata =
        source.identity) :
    deriveQuantitativeTransport
        (.retarget transportQ source targetClaim targetEvidence
          targetMetadata targetClaimBinding targetEvidenceBinding
          .absent) =
      .refuse (.lawfulBridgeMissing kind) := by
  have identityDecision :
      quantitativeJudgmentIdentityDecidableEq kind
          (quantitativeJudgmentIdentity kind targetClaim targetMetadata)
          source.identity =
        Decidable.isTrue sameIdentity := by
    apply Subsingleton.elim
  simp only [deriveQuantitativeTransport, identityDecision]

end Residua.RCC.QuantitativeClaimBinding

import RCC.QuantitativeClaimBinding

/-!
# RCC CM-3 quantitative claim binding tests and countermodels

The positive fixtures bind complete probabilistic and statistical metadata and
transport an exact quantitative judgment through an explicit CM-2 bridge.

The countermodels then pin both CM-3 boundaries:

* untrusted evidence cannot omit a security parameter, sample frame, or
  confidence coordinate;
* changed adversary classes are refused rather than normalized away; and
* even an accepted CM-2 bridge cannot rewrite a security parameter, adversary
  class, sample frame, or confidence ratio.

The fixture verifier is intentionally permissive inside the two quantitative
modalities.  This makes CM-3, rather than a coincidentally strict test
verifier, the load-bearing reason every mutant is refused.
-/

namespace Residua.RCC.QuantitativeClaimBinding.Tests

open Residua.RCC.ClaimModality
open Residua.RCC.EvidenceModalityTransport
open Residua.RCC.QuantitativeClaimBinding

def probabilityBoundDenominator : Nat :=
  340282366920938463463374607431768211456

def probabilisticClaim : Claim .probabilistic :=
  .probabilistic
    "claim:forgery-negligible"
    "experiment:euf-cma"
    "adversary:ppt"
    128
    1
    probabilityBoundDenominator

def probabilisticEvidence : Evidence .probabilistic :=
  .probabilistic
    "experiment:euf-cma"
    "adversary:ppt"
    "proof:reduction-v1"
    128
    1
    probabilityBoundDenominator

def probabilisticMetadata : ProbabilisticMetadata :=
  { experimentQ := "experiment:euf-cma"
    adversaryClassQ := "adversary:ppt"
    securityParameter := 128
    boundNumerator := 1
    boundDenominator := probabilityBoundDenominator }

def statisticalClaim : Claim .statistical :=
  .statistical
    "claim:failure-rate-bound"
    "estimator:clopper-pearson"
    "population:sealed-runtime"
    "sample-frame:window-42"
    10000
    95
    100

def statisticalEvidence : Evidence .statistical :=
  .statistical
    "sample-frame:window-42"
    "estimator:clopper-pearson"
    "report:failure-rate-bound"
    10000
    95
    100

def statisticalMetadata : StatisticalMetadata :=
  { estimatorQ := "estimator:clopper-pearson"
    sampleFrameQ := "sample-frame:window-42"
    sampleSize := 10000
    confidenceNumerator := 95
    confidenceDenominator := 100 }

/--
Semantic acceptance is deliberately weak here: any same-modality
probabilistic or statistical pair is accepted.  CM-3 must therefore detect
all coordinate rewriting independently of this verifier.
-/
def permissiveQuantitativeVerifier : ModalityVerifier where
  Accepts :=
    fun {modality} _ _ =>
      match modality with
      | .probabilistic => True
      | .statistical => True
      | _ => False

def verifiedProbabilistic :
    VerifiedClaim permissiveQuantitativeVerifier .probabilistic where
  claim := probabilisticClaim
  evidence := probabilisticEvidence
  accepted := True.intro

def verifiedStatistical :
    VerifiedClaim permissiveQuantitativeVerifier .statistical where
  claim := statisticalClaim
  evidence := statisticalEvidence
  accepted := True.intro

def probabilisticJudgment :
    QuantitativeJudgment
      permissiveQuantitativeVerifier .probabilistic :=
  QuantitativeJudgment.ofVerified verifiedProbabilistic (by rfl)

def statisticalJudgment :
    QuantitativeJudgment
      permissiveQuantitativeVerifier .statistical :=
  QuantitativeJudgment.ofVerified verifiedStatistical (by rfl)

/-! ## Positive evidence binding retains every quantitative coordinate. -/

def completeProbabilisticAttempt : ProbabilisticEvidenceAttempt :=
  { experimentQ := some "experiment:euf-cma"
    adversaryClassQ := some "adversary:ppt"
    proofQ := "proof:reduction-v2"
    securityParameter := some 128
    boundNumerator := some 1
    boundDenominator := some probabilityBoundDenominator }

def completeStatisticalAttempt : StatisticalEvidenceAttempt :=
  { sampleFrameQ := some "sample-frame:window-42"
    estimatorQ := some "estimator:clopper-pearson"
    reportQ := "report:failure-rate-bound-v2"
    sampleSize := some 10000
    confidenceNumerator := some 95
    confidenceDenominator := some 100 }

theorem complete_probability_metadata_is_bound :
    bindQuantitativeEvidence
        (.probabilistic probabilisticClaim)
        (.probabilistic completeProbabilisticAttempt) =
      .bound
        (.probabilistic
          probabilisticClaim
          (.probabilistic
            "experiment:euf-cma"
            "adversary:ppt"
            "proof:reduction-v2"
            128
            1
            probabilityBoundDenominator)
          probabilisticMetadata
          rfl
          rfl) := by
  rfl

theorem complete_statistical_metadata_is_bound :
    bindQuantitativeEvidence
        (.statistical statisticalClaim)
        (.statistical completeStatisticalAttempt) =
      .bound
        (.statistical
          statisticalClaim
          (.statistical
            "sample-frame:window-42"
            "estimator:clopper-pearson"
            "report:failure-rate-bound-v2"
            10000
            95
            100)
          statisticalMetadata
          rfl
          rfl) := by
  rfl

theorem probabilistic_identity_retains_security_coordinates :
    probabilisticJudgment.identity =
      ({ claimQ := "claim:forgery-negligible"
         metadata := probabilisticMetadata } :
        ProbabilisticJudgmentIdentity) := by
  rfl

theorem statistical_identity_retains_confidence_coordinates :
    statisticalJudgment.identity =
      ({ claimQ := "claim:failure-rate-bound"
         populationQ := "population:sealed-runtime"
         metadata := statisticalMetadata } :
        StatisticalJudgmentIdentity) := by
  rfl

/-! ## Omission and mismatch at the untrusted evidence boundary. -/

def missingSecurityParameterAttempt : ProbabilisticEvidenceAttempt :=
  { completeProbabilisticAttempt with
    securityParameter := none }

theorem missing_security_parameter_is_refused :
    bindQuantitativeEvidence
        (.probabilistic probabilisticClaim)
        (.probabilistic missingSecurityParameterAttempt) =
      .refuse
        (.metadataMissing .probabilistic .securityParameter) := by
  rfl

def rewrittenAdversaryAttempt : ProbabilisticEvidenceAttempt :=
  { completeProbabilisticAttempt with
    adversaryClassQ := some "adversary:unbounded" }

theorem rewritten_adversary_class_is_refused :
    bindQuantitativeEvidence
        (.probabilistic probabilisticClaim)
        (.probabilistic rewrittenAdversaryAttempt) =
      .refuse
        (.metadataMismatch
          .probabilistic
          .adversaryClass
          (.text "adversary:ppt")
          (.text "adversary:unbounded")) := by
  rfl

def rewrittenProbabilityBoundAttempt : ProbabilisticEvidenceAttempt :=
  { completeProbabilisticAttempt with
    boundNumerator := some 2 }

theorem rewritten_probability_bound_is_refused :
    bindQuantitativeEvidence
        (.probabilistic probabilisticClaim)
        (.probabilistic rewrittenProbabilityBoundAttempt) =
      .refuse
        (.metadataMismatch
          .probabilistic
          .probabilityBoundNumerator
          (.natural 1)
          (.natural 2)) := by
  rfl

def missingSampleFrameAttempt : StatisticalEvidenceAttempt :=
  { completeStatisticalAttempt with
    sampleFrameQ := none }

theorem missing_sample_frame_is_refused :
    bindQuantitativeEvidence
        (.statistical statisticalClaim)
        (.statistical missingSampleFrameAttempt) =
      .refuse
        (.metadataMissing .statistical .sampleFrame) := by
  rfl

def missingConfidenceAttempt : StatisticalEvidenceAttempt :=
  { completeStatisticalAttempt with
    confidenceNumerator := none }

theorem missing_confidence_metadata_is_refused :
    bindQuantitativeEvidence
        (.statistical statisticalClaim)
        (.statistical missingConfidenceAttempt) =
      .refuse
        (.metadataMissing .statistical .confidenceNumerator) := by
  rfl

/-! ## Exact CM-2 retargeting remains possible when identity is unchanged. -/

def updatedProbabilisticEvidence : Evidence .probabilistic :=
  .probabilistic
    "experiment:euf-cma"
    "adversary:ppt"
    "proof:reduction-v2"
    128
    1
    probabilityBoundDenominator

def exactProbabilisticBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedProbabilistic
      probabilisticClaim
      updatedProbabilisticEvidence where
  bridgeQ := "bridge:probability-proof-refresh"
  preservesAcceptance := by
    intro _
    exact True.intro

def exactProbabilisticTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .probabilistic :=
  .retarget
    "transport:probability-proof-refresh"
    probabilisticJudgment
    probabilisticClaim
    updatedProbabilisticEvidence
    probabilisticMetadata
    rfl
    rfl
    (.certified exactProbabilisticBridge)

theorem exact_quantitative_identity_can_be_transported :
    (deriveQuantitativeTransport
      exactProbabilisticTransport).isTransported = true := by
  rfl

/-!
## Transport mutants

Every target is accepted by the permissive verifier and carries a real CM-2
bridge.  The only reason it is refused is CM-3 complete-identity inequality.
-/

def changedSecurityClaim : Claim .probabilistic :=
  .probabilistic
    "claim:forgery-negligible"
    "experiment:euf-cma"
    "adversary:ppt"
    64
    1
    probabilityBoundDenominator

def changedSecurityEvidence : Evidence .probabilistic :=
  .probabilistic
    "experiment:euf-cma"
    "adversary:ppt"
    "proof:reduction-weak"
    64
    1
    probabilityBoundDenominator

def changedSecurityMetadata : ProbabilisticMetadata :=
  { probabilisticMetadata with securityParameter := 64 }

def changedSecurityBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedProbabilistic
      changedSecurityClaim
      changedSecurityEvidence where
  bridgeQ := "bridge:forged-security-rewrite"
  preservesAcceptance := by
    intro _
    exact True.intro

def changedSecurityTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .probabilistic :=
  .retarget
    "transport:forged-security-rewrite"
    probabilisticJudgment
    changedSecurityClaim
    changedSecurityEvidence
    changedSecurityMetadata
    rfl
    rfl
    (.certified changedSecurityBridge)

theorem security_parameter_rewrite_is_refused_despite_bridge :
    deriveQuantitativeTransport changedSecurityTransport =
      .refuse
        (.judgmentIdentityChanged
          (.probabilistic probabilisticJudgment.identity)
          (.probabilistic
            (probabilisticJudgmentIdentity
              changedSecurityClaim changedSecurityMetadata))) := by
  rfl

def changedAdversaryClaim : Claim .probabilistic :=
  .probabilistic
    "claim:forgery-negligible"
    "experiment:euf-cma"
    "adversary:unbounded"
    128
    1
    probabilityBoundDenominator

def changedAdversaryEvidence : Evidence .probabilistic :=
  .probabilistic
    "experiment:euf-cma"
    "adversary:unbounded"
    "proof:invalid-adversary-upgrade"
    128
    1
    probabilityBoundDenominator

def changedAdversaryMetadata : ProbabilisticMetadata :=
  { probabilisticMetadata with
    adversaryClassQ := "adversary:unbounded" }

def changedAdversaryBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedProbabilistic
      changedAdversaryClaim
      changedAdversaryEvidence where
  bridgeQ := "bridge:forged-adversary-rewrite"
  preservesAcceptance := by
    intro _
    exact True.intro

def changedAdversaryTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .probabilistic :=
  .retarget
    "transport:forged-adversary-rewrite"
    probabilisticJudgment
    changedAdversaryClaim
    changedAdversaryEvidence
    changedAdversaryMetadata
    rfl
    rfl
    (.certified changedAdversaryBridge)

theorem adversary_class_rewrite_is_refused_despite_bridge :
    deriveQuantitativeTransport changedAdversaryTransport =
      .refuse
        (.judgmentIdentityChanged
          (.probabilistic probabilisticJudgment.identity)
          (.probabilistic
            (probabilisticJudgmentIdentity
              changedAdversaryClaim changedAdversaryMetadata))) := by
  rfl

def changedProbabilityBoundClaim : Claim .probabilistic :=
  .probabilistic
    "claim:forgery-negligible"
    "experiment:euf-cma"
    "adversary:ppt"
    128
    2
    probabilityBoundDenominator

def changedProbabilityBoundEvidence : Evidence .probabilistic :=
  .probabilistic
    "experiment:euf-cma"
    "adversary:ppt"
    "proof:weaker-probability-bound"
    128
    2
    probabilityBoundDenominator

def changedProbabilityBoundMetadata : ProbabilisticMetadata :=
  { probabilisticMetadata with
    boundNumerator := 2 }

def changedProbabilityBoundBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedProbabilistic
      changedProbabilityBoundClaim
      changedProbabilityBoundEvidence where
  bridgeQ := "bridge:forged-probability-bound-rewrite"
  preservesAcceptance := by
    intro _
    exact True.intro

def changedProbabilityBoundTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .probabilistic :=
  .retarget
    "transport:forged-probability-bound-rewrite"
    probabilisticJudgment
    changedProbabilityBoundClaim
    changedProbabilityBoundEvidence
    changedProbabilityBoundMetadata
    rfl
    rfl
    (.certified changedProbabilityBoundBridge)

theorem probability_bound_rewrite_is_refused_despite_bridge :
    deriveQuantitativeTransport changedProbabilityBoundTransport =
      .refuse
        (.judgmentIdentityChanged
          (.probabilistic probabilisticJudgment.identity)
          (.probabilistic
            (probabilisticJudgmentIdentity
              changedProbabilityBoundClaim
              changedProbabilityBoundMetadata))) := by
  rfl

def changedSampleFrameClaim : Claim .statistical :=
  .statistical
    "claim:failure-rate-bound"
    "estimator:clopper-pearson"
    "population:sealed-runtime"
    "sample-frame:biased-window"
    10000
    95
    100

def changedSampleFrameEvidence : Evidence .statistical :=
  .statistical
    "sample-frame:biased-window"
    "estimator:clopper-pearson"
    "report:biased-frame"
    10000
    95
    100

def changedSampleFrameMetadata : StatisticalMetadata :=
  { statisticalMetadata with
    sampleFrameQ := "sample-frame:biased-window" }

def changedSampleFrameBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedStatistical
      changedSampleFrameClaim
      changedSampleFrameEvidence where
  bridgeQ := "bridge:forged-frame-rewrite"
  preservesAcceptance := by
    intro _
    exact True.intro

def changedSampleFrameTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .statistical :=
  .retarget
    "transport:forged-frame-rewrite"
    statisticalJudgment
    changedSampleFrameClaim
    changedSampleFrameEvidence
    changedSampleFrameMetadata
    rfl
    rfl
    (.certified changedSampleFrameBridge)

theorem sample_frame_rewrite_is_refused_despite_bridge :
    deriveQuantitativeTransport changedSampleFrameTransport =
      .refuse
        (.judgmentIdentityChanged
          (.statistical statisticalJudgment.identity)
          (.statistical
            (statisticalJudgmentIdentity
              changedSampleFrameClaim changedSampleFrameMetadata))) := by
  rfl

def changedConfidenceClaim : Claim .statistical :=
  .statistical
    "claim:failure-rate-bound"
    "estimator:clopper-pearson"
    "population:sealed-runtime"
    "sample-frame:window-42"
    10000
    90
    100

def changedConfidenceEvidence : Evidence .statistical :=
  .statistical
    "sample-frame:window-42"
    "estimator:clopper-pearson"
    "report:weaker-confidence"
    10000
    90
    100

def changedConfidenceMetadata : StatisticalMetadata :=
  { statisticalMetadata with
    confidenceNumerator := 90 }

def changedConfidenceBridge :
    LawfulEvidenceBridge
      permissiveQuantitativeVerifier
      verifiedStatistical
      changedConfidenceClaim
      changedConfidenceEvidence where
  bridgeQ := "bridge:forged-confidence-rewrite"
  preservesAcceptance := by
    intro _
    exact True.intro

def changedConfidenceTransport :
    QuantitativeTransportRequest
      permissiveQuantitativeVerifier .statistical :=
  .retarget
    "transport:forged-confidence-rewrite"
    statisticalJudgment
    changedConfidenceClaim
    changedConfidenceEvidence
    changedConfidenceMetadata
    rfl
    rfl
    (.certified changedConfidenceBridge)

theorem confidence_rewrite_is_refused_despite_bridge :
    deriveQuantitativeTransport changedConfidenceTransport =
      .refuse
        (.judgmentIdentityChanged
          (.statistical statisticalJudgment.identity)
          (.statistical
            (statisticalJudgmentIdentity
              changedConfidenceClaim changedConfidenceMetadata))) := by
  rfl

/-! The generic theorem also proves parameter mutation is never bridgeable. -/

theorem changed_security_uses_general_identity_law :
    deriveQuantitativeTransport changedSecurityTransport =
      .refuse
        (.judgmentIdentityChanged
          (.probabilistic probabilisticJudgment.identity)
          (.probabilistic
            (probabilisticJudgmentIdentity
              changedSecurityClaim changedSecurityMetadata))) := by
  apply changed_quantitative_identity_is_refused
  decide

#print axioms complete_probability_metadata_is_bound
#print axioms complete_statistical_metadata_is_bound
#print axioms missing_security_parameter_is_refused
#print axioms rewritten_adversary_class_is_refused
#print axioms rewritten_probability_bound_is_refused
#print axioms missing_sample_frame_is_refused
#print axioms missing_confidence_metadata_is_refused
#print axioms exact_quantitative_identity_can_be_transported
#print axioms security_parameter_rewrite_is_refused_despite_bridge
#print axioms adversary_class_rewrite_is_refused_despite_bridge
#print axioms probability_bound_rewrite_is_refused_despite_bridge
#print axioms sample_frame_rewrite_is_refused_despite_bridge
#print axioms confidence_rewrite_is_refused_despite_bridge
#print axioms changed_security_uses_general_identity_law
#print axioms quantitative_transport_result_retains_identity
#print axioms changed_quantitative_identity_is_refused
#print axioms unbridged_quantitative_retarget_is_refused

end Residua.RCC.QuantitativeClaimBinding.Tests

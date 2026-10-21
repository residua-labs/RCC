import RCCTests.QuantitativeClaimBinding

/-! RCC-89 candidate: quantitative claim identity and transport binding. -/

namespace Residua.RCC.RCC89Target

open Residua.RCC.QuantitativeClaimBinding.Tests
open Residua.RCC.QuantitativeClaimBinding

def probabilityMetadataBound := complete_probability_metadata_is_bound
def statisticalMetadataBound := complete_statistical_metadata_is_bound
def probabilisticIdentityRetainsCoordinates := probabilistic_identity_retains_security_coordinates
def statisticalIdentityRetainsCoordinates := statistical_identity_retains_confidence_coordinates
def missingSecurityRefused := missing_security_parameter_is_refused
def rewrittenAdversaryRefused := rewritten_adversary_class_is_refused
def rewrittenProbabilityRefused := rewritten_probability_bound_is_refused
def missingSampleFrameRefused := missing_sample_frame_is_refused
def missingConfidenceRefused := missing_confidence_metadata_is_refused
def exactIdentityTransported := exact_quantitative_identity_can_be_transported
def securityRewriteRefused := security_parameter_rewrite_is_refused_despite_bridge
def adversaryRewriteRefused := adversary_class_rewrite_is_refused_despite_bridge
def probabilityRewriteRefused := probability_bound_rewrite_is_refused_despite_bridge
def sampleFrameRewriteRefused := sample_frame_rewrite_is_refused_despite_bridge
def confidenceRewriteRefused := confidence_rewrite_is_refused_despite_bridge
def generalIdentityLaw := changed_security_uses_general_identity_law

abbrev ProbabilityMetadataBound : Prop :=
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
        rfl)

abbrev StatisticalMetadataBound : Prop :=
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
        rfl)

abbrev ProbabilisticIdentityRetainsCoordinates : Prop :=
  probabilisticJudgment.identity =
    ({ claimQ := "claim:forgery-negligible"
       metadata := probabilisticMetadata } :
      ProbabilisticJudgmentIdentity)

abbrev StatisticalIdentityRetainsCoordinates : Prop :=
  statisticalJudgment.identity =
    ({ claimQ := "claim:failure-rate-bound"
       populationQ := "population:sealed-runtime"
       metadata := statisticalMetadata } :
      StatisticalJudgmentIdentity)

abbrev MissingSecurityRefused : Prop :=
  bindQuantitativeEvidence
      (.probabilistic probabilisticClaim)
      (.probabilistic missingSecurityParameterAttempt) =
    .refuse (.metadataMissing .probabilistic .securityParameter)

abbrev RewrittenAdversaryRefused : Prop :=
  bindQuantitativeEvidence
      (.probabilistic probabilisticClaim)
      (.probabilistic rewrittenAdversaryAttempt) =
    .refuse
      (.metadataMismatch
        .probabilistic
        .adversaryClass
        (.text "adversary:ppt")
        (.text "adversary:unbounded"))

abbrev RewrittenProbabilityRefused : Prop :=
  bindQuantitativeEvidence
      (.probabilistic probabilisticClaim)
      (.probabilistic rewrittenProbabilityBoundAttempt) =
    .refuse
      (.metadataMismatch
        .probabilistic
        .probabilityBoundNumerator
        (.natural 1)
        (.natural 2))

abbrev MissingSampleFrameRefused : Prop :=
  bindQuantitativeEvidence
      (.statistical statisticalClaim)
      (.statistical missingSampleFrameAttempt) =
    .refuse (.metadataMissing .statistical .sampleFrame)

abbrev MissingConfidenceRefused : Prop :=
  bindQuantitativeEvidence
      (.statistical statisticalClaim)
      (.statistical missingConfidenceAttempt) =
    .refuse (.metadataMissing .statistical .confidenceNumerator)

abbrev ExactIdentityTransported : Prop :=
  (deriveQuantitativeTransport exactProbabilisticTransport).isTransported = true

abbrev SecurityRewriteRefused : Prop :=
  deriveQuantitativeTransport changedSecurityTransport =
    .refuse
      (.judgmentIdentityChanged
        (.probabilistic probabilisticJudgment.identity)
        (.probabilistic
          (probabilisticJudgmentIdentity
            changedSecurityClaim changedSecurityMetadata)))

abbrev AdversaryRewriteRefused : Prop :=
  deriveQuantitativeTransport changedAdversaryTransport =
    .refuse
      (.judgmentIdentityChanged
        (.probabilistic probabilisticJudgment.identity)
        (.probabilistic
          (probabilisticJudgmentIdentity
            changedAdversaryClaim changedAdversaryMetadata)))

abbrev ProbabilityRewriteRefused : Prop :=
  deriveQuantitativeTransport changedProbabilityBoundTransport =
    .refuse
      (.judgmentIdentityChanged
        (.probabilistic probabilisticJudgment.identity)
        (.probabilistic
          (probabilisticJudgmentIdentity
            changedProbabilityBoundClaim changedProbabilityBoundMetadata)))

abbrev SampleFrameRewriteRefused : Prop :=
  deriveQuantitativeTransport changedSampleFrameTransport =
    .refuse
      (.judgmentIdentityChanged
        (.statistical statisticalJudgment.identity)
        (.statistical
          (statisticalJudgmentIdentity
            changedSampleFrameClaim changedSampleFrameMetadata)))

abbrev ConfidenceRewriteRefused : Prop :=
  deriveQuantitativeTransport changedConfidenceTransport =
    .refuse
      (.judgmentIdentityChanged
        (.statistical statisticalJudgment.identity)
        (.statistical
          (statisticalJudgmentIdentity
            changedConfidenceClaim changedConfidenceMetadata)))

abbrev GeneralIdentityLaw : Prop :=
  deriveQuantitativeTransport changedSecurityTransport =
    .refuse
      (.judgmentIdentityChanged
        (.probabilistic probabilisticJudgment.identity)
        (.probabilistic
          (probabilisticJudgmentIdentity
            changedSecurityClaim changedSecurityMetadata)))

structure Certificate where
  probabilityMetadataBound : ProbabilityMetadataBound
  statisticalMetadataBound : StatisticalMetadataBound
  probabilisticIdentityRetainsCoordinates : ProbabilisticIdentityRetainsCoordinates
  statisticalIdentityRetainsCoordinates : StatisticalIdentityRetainsCoordinates
  missingSecurityRefused : MissingSecurityRefused
  rewrittenAdversaryRefused : RewrittenAdversaryRefused
  rewrittenProbabilityRefused : RewrittenProbabilityRefused
  missingSampleFrameRefused : MissingSampleFrameRefused
  missingConfidenceRefused : MissingConfidenceRefused
  exactIdentityTransported : ExactIdentityTransported
  securityRewriteRefused : SecurityRewriteRefused
  adversaryRewriteRefused : AdversaryRewriteRefused
  probabilityRewriteRefused : ProbabilityRewriteRefused
  sampleFrameRewriteRefused : SampleFrameRewriteRefused
  confidenceRewriteRefused : ConfidenceRewriteRefused
  generalIdentityLaw : GeneralIdentityLaw

def certificate : Certificate where
  probabilityMetadataBound := complete_probability_metadata_is_bound
  statisticalMetadataBound := complete_statistical_metadata_is_bound
  probabilisticIdentityRetainsCoordinates :=
    probabilistic_identity_retains_security_coordinates
  statisticalIdentityRetainsCoordinates :=
    statistical_identity_retains_confidence_coordinates
  missingSecurityRefused := missing_security_parameter_is_refused
  rewrittenAdversaryRefused := rewritten_adversary_class_is_refused
  rewrittenProbabilityRefused := rewritten_probability_bound_is_refused
  missingSampleFrameRefused := missing_sample_frame_is_refused
  missingConfidenceRefused := missing_confidence_metadata_is_refused
  exactIdentityTransported := exact_quantitative_identity_can_be_transported
  securityRewriteRefused :=
    security_parameter_rewrite_is_refused_despite_bridge
  adversaryRewriteRefused :=
    adversary_class_rewrite_is_refused_despite_bridge
  probabilityRewriteRefused :=
    probability_bound_rewrite_is_refused_despite_bridge
  sampleFrameRewriteRefused :=
    sample_frame_rewrite_is_refused_despite_bridge
  confidenceRewriteRefused :=
    confidence_rewrite_is_refused_despite_bridge
  generalIdentityLaw := changed_security_uses_general_identity_law

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC89Target

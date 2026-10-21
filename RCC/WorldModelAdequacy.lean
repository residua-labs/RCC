import RCC.ObservationAbstraction

/-!
# RCC WI-4 world-model adequacy from model property to external intent

WI-4 pins exactly one bridge: a WI-3 admitted internal `ModelClaim` may
establish an external intent only through an explicit, snapshot-bound adequacy
verifier and its soundness theorem.

The common derivation does not accept a caller-supplied `closed` flag or an
arbitrary proposition.  It first checks that the request names the exact
snapshot, context, observation set, model, and claim carried by the admitted
WI-3 packet.  It then runs the domain adequacy verifier on those packet fields.
Only `verifySound`, applied to the packet's observation and model proofs, can
produce `IntentSatisfied`.

This file does not claim WI-5 actuation soundness.  Its terminal proposition is
an external intent judgment at one sealed observation snapshot.

Prelude-only Lean 4.14; no Mathlib, no custom axioms, no proof placeholders,
and only computable adequacy admission.
-/

namespace Residua.RCC.WorldModelAdequacy

open Residua.RCC.ObservationSoundness
open Residua.RCC.ObservationAbstraction

universe u v

/-- Domain-specific external intent and the explicit WI-3 → WI-4 bridge. -/
structure ExternalIntentSystem
    (S : ObservationSystem)
    (A : AbstractionSystem S) where
  Intent : Type u
  AdequacyCertificate : Type v

  /-- The external proposition, evaluated at the exact sealed snapshot. -/
  IntentSatisfied :
    SealedWorldSnapshot S → Intent → Prop

  /--
  Executable verification for the complete model-property tuple.

  The snapshot identity, context, observations, model, and claim are all
  explicit inputs.  The common derivation supplies these values from the WI-3
  packet rather than trusting caller copies.
  -/
  verify :
    S.SnapshotQ →
      A.ModelContext →
      List S.Observation →
      A.Model →
      A.Claim →
      Intent →
      AdequacyCertificate →
      Bool

  /--
  An accepted certificate bridges the exact admitted model property to the
  external intent.  Observation soundness is retained because a model claim
  may otherwise be internally true while describing the wrong world.
  -/
  verifySound :
    ∀ {snapshot context observations model claim intent certificate},
      A.ContextMatches snapshot.snapshotQ context →
        (∀ observation, observation ∈ observations →
          S.ObservationTrue snapshot.world observation) →
        A.ModelClaim context observations model claim →
        verify snapshot.snapshotQ context observations model claim
          intent certificate = true →
        IntentSatisfied snapshot intent

/--
Untrusted request to apply one adequacy certificate.

All five claimed model coordinates are checked against the admitted WI-3
packet before the domain verifier runs.
-/
structure AdequacyAttempt
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (I : ExternalIntentSystem S A)
    (snapshot : SealedWorldSnapshot S) where
  claimedSnapshotQ : S.SnapshotQ
  claimedContext : A.ModelContext
  claimedObservations : List S.Observation
  claimedModel : A.Model
  claimedClaim : A.Claim
  intent : I.Intent
  certificate : I.AdequacyCertificate

/-- A proof-carrying external intent judgment derived from one WI-3 packet. -/
structure AdmittedExternalIntent
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (I : ExternalIntentSystem S A)
    (snapshot : SealedWorldSnapshot S) where
  packet : AdmittedModelClaim S A snapshot
  intent : I.Intent
  certificate : I.AdequacyCertificate
  verifierAccepted :
    I.verify snapshot.snapshotQ
      packet.context packet.observations packet.model packet.claim
      intent certificate = true

/-- Every constructible WI-4 judgment establishes its external intent. -/
theorem AdmittedExternalIntent.sound
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    (admitted : AdmittedExternalIntent S A I snapshot) :
    I.IntentSatisfied snapshot admitted.intent :=
  I.verifySound
    admitted.packet.contextBound
    admitted.packet.observationsSound
    admitted.packet.sound
    admitted.verifierAccepted

/-- Exhaustive WI-4 refusal vocabulary. -/
inductive AdequacyResidue
  | staleObservationSnapshot
  | modelContextMismatch
  | observationSetMismatch
  | modelMismatch
  | modelClaimMismatch
  | adequacyCertificateRefused
  deriving DecidableEq, Repr

/-- Total proof-carrying WI-4 result. -/
inductive AdequacyResult
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (I : ExternalIntentSystem S A)
    (snapshot : SealedWorldSnapshot S)
  | admitted (judgment : AdmittedExternalIntent S A I snapshot)
  | refuse (residue : AdequacyResidue)

/--
Mechanical WI-4 derivation.

The instance supplies intent evidence and a sound verifier; it cannot directly
return an admitted judgment.  Equality checks pin every caller copy to the
exact admitted WI-3 packet, and verification then uses the packet fields.
-/
def deriveExternalIntent
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    [DecidableEq A.ModelContext]
    [DecidableEq S.Observation]
    [DecidableEq A.Model]
    [DecidableEq A.Claim]
    (packet : AdmittedModelClaim S A snapshot)
    (attempt : AdequacyAttempt S A I snapshot) :
    AdequacyResult S A I snapshot :=
  letI := S.snapshotQDecidableEq
  if _snapshot :
      attempt.claimedSnapshotQ = snapshot.snapshotQ then
    if _context :
        attempt.claimedContext = packet.context then
      if _observations :
          attempt.claimedObservations = packet.observations then
        if _model :
            attempt.claimedModel = packet.model then
          if _claim :
              attempt.claimedClaim = packet.claim then
            if accepted :
                I.verify snapshot.snapshotQ
                  packet.context packet.observations
                  packet.model packet.claim
                  attempt.intent attempt.certificate = true then
              .admitted
                { packet := packet
                  intent := attempt.intent
                  certificate := attempt.certificate
                  verifierAccepted := accepted }
            else
              .refuse .adequacyCertificateRefused
          else
            .refuse .modelClaimMismatch
        else
          .refuse .modelMismatch
      else
        .refuse .observationSetMismatch
    else
      .refuse .modelContextMismatch
  else
    .refuse .staleObservationSnapshot

/-- Every successful WI-4 derivation establishes the external intent. -/
theorem admitted_external_intent_is_sound
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    [DecidableEq A.ModelContext]
    [DecidableEq S.Observation]
    [DecidableEq A.Model]
    [DecidableEq A.Claim]
    {packet : AdmittedModelClaim S A snapshot}
    {attempt : AdequacyAttempt S A I snapshot}
    {judgment : AdmittedExternalIntent S A I snapshot}
    (_result :
      deriveExternalIntent packet attempt =
        .admitted judgment) :
    I.IntentSatisfied snapshot judgment.intent :=
  judgment.sound

/-- A stale snapshot cannot transport model adequacy into the current world. -/
theorem stale_adequacy_snapshot_is_refused
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    [DecidableEq A.ModelContext]
    [DecidableEq S.Observation]
    [DecidableEq A.Model]
    [DecidableEq A.Claim]
    (packet : AdmittedModelClaim S A snapshot)
    (attempt : AdequacyAttempt S A I snapshot)
    (stale : attempt.claimedSnapshotQ ≠ snapshot.snapshotQ) :
    deriveExternalIntent packet attempt =
      .refuse .staleObservationSnapshot := by
  letI := S.snapshotQDecidableEq
  simp [deriveExternalIntent, stale]

/-- A caller-named context different from the packet context is refused. -/
theorem wrong_adequacy_context_is_refused
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    [DecidableEq A.ModelContext]
    [DecidableEq S.Observation]
    [DecidableEq A.Model]
    [DecidableEq A.Claim]
    (packet : AdmittedModelClaim S A snapshot)
    (attempt : AdequacyAttempt S A I snapshot)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ)
    (wrongContext : attempt.claimedContext ≠ packet.context) :
    deriveExternalIntent packet attempt =
      .refuse .modelContextMismatch := by
  letI := S.snapshotQDecidableEq
  simp [deriveExternalIntent, fresh, wrongContext]

/-- A refused or missing adequacy certificate cannot establish intent. -/
theorem refused_adequacy_certificate_is_not_admitted
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {I : ExternalIntentSystem S A}
    {snapshot : SealedWorldSnapshot S}
    [DecidableEq A.ModelContext]
    [DecidableEq S.Observation]
    [DecidableEq A.Model]
    [DecidableEq A.Claim]
    (packet : AdmittedModelClaim S A snapshot)
    (attempt : AdequacyAttempt S A I snapshot)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ)
    (sameContext : attempt.claimedContext = packet.context)
    (sameObservations :
      attempt.claimedObservations = packet.observations)
    (sameModel : attempt.claimedModel = packet.model)
    (sameClaim : attempt.claimedClaim = packet.claim)
    (refused :
      I.verify snapshot.snapshotQ
        packet.context packet.observations packet.model packet.claim
        attempt.intent attempt.certificate ≠ true) :
    deriveExternalIntent packet attempt =
      .refuse .adequacyCertificateRefused := by
  letI := S.snapshotQDecidableEq
  simp [deriveExternalIntent, fresh, sameContext, sameObservations,
    sameModel, sameClaim, refused]

end Residua.RCC.WorldModelAdequacy

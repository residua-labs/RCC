import Init

/-!
# RCC WI-1 observation soundness

WI-1 pins exactly one world-interface obligation: an admitted observation is
true of the sealed external-world snapshot to which its source capture and
certificate are bound.

An instance supplies the raw correspondence relation and a certificate
verifier, but it cannot directly declare an observation admitted.  The common
admission function checks the serialized snapshot identity, requires a proof
that the exact source/raw pair represents the sealed world, and accepts only a
certificate whose verifier returns `true`.  The verifier's soundness law then
establishes the observation proposition.

This file does not claim WI-2 observation completeness.  A sound verifier may
reject a true observation, and a sealed source scope may omit a real event.

Prelude-only Lean 4.14; no Mathlib, no custom axioms, no proof placeholders,
and only computable admission.
-/

namespace Residua.RCC.ObservationSoundness

universe u v w x y z

/-- Domain facts needed to validate one external observation. -/
structure ObservationSystem where
  World : Type u
  SnapshotQ : Type v
  Source : Type w
  Raw : Type x
  Observation : Type y
  Certificate : Type z

  snapshotQDecidableEq : DecidableEq SnapshotQ

  /-- The exact source/raw capture corresponds to this external world. -/
  RawRepresents : World → Source → Raw → Prop

  /-- The admitted semantic observation is true of this external world. -/
  ObservationTrue : World → Observation → Prop

  /-- Executable certificate verification at the raw/semantic boundary. -/
  verify : Source → Raw → Observation → Certificate → Bool

  /-- Every accepted certificate is sound relative to an authentic capture. -/
  verifySound :
    ∀ {world source raw observation certificate},
      RawRepresents world source raw →
        verify source raw observation certificate = true →
        ObservationTrue world observation

/--
One fixed external world and its declared snapshot identity.

WI-1 uses this identity as an exact freshness guard.  Faithful realization of
the identity itself belongs to AddressKernel/runtime binding; external-world
authenticity here is carried by `RawRepresents`.
-/
structure SealedWorldSnapshot (S : ObservationSystem) where
  snapshotQ : S.SnapshotQ
  world : S.World

/-- Untrusted serialized proposal to admit an observation. -/
structure ObservationAttempt
    (S : ObservationSystem)
    (snapshot : SealedWorldSnapshot S) where
  claimedSnapshotQ : S.SnapshotQ
  source : S.Source
  raw : S.Raw
  observation : S.Observation
  certificate : S.Certificate

/--
Capture authorization is either absent or proves that this exact attempt's
source/raw pair represents the exact sealed world.
-/
inductive CaptureAuthorization
    (S : ObservationSystem)
    (snapshot : SealedWorldSnapshot S)
    (attempt : ObservationAttempt S snapshot)
  | absent
  | certified
      (authentic :
        S.RawRepresents snapshot.world attempt.source attempt.raw)

/-- Proof-carrying admitted observation at one exact sealed snapshot. -/
structure AdmittedObservation
    (S : ObservationSystem)
    (snapshot : SealedWorldSnapshot S) where
  source : S.Source
  raw : S.Raw
  observation : S.Observation
  certificate : S.Certificate
  sourceAuthentic : S.RawRepresents snapshot.world source raw
  verifierAccepted : S.verify source raw observation certificate = true

/-- Every constructible admitted packet is semantically sound. -/
theorem AdmittedObservation.sound
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (admitted : AdmittedObservation S snapshot) :
    S.ObservationTrue snapshot.world admitted.observation :=
  S.verifySound admitted.sourceAuthentic admitted.verifierAccepted

/-- The exhaustive WI-1 refusal vocabulary. -/
inductive ObservationAdmissionResidue
  | staleSnapshot
  | sourceCaptureUnverified
  | certificateRefused
  deriving DecidableEq, Repr

/-- Total observation-admission result. -/
inductive ObservationAdmissionResult
    (S : ObservationSystem)
    (snapshot : SealedWorldSnapshot S)
  | admitted (packet : AdmittedObservation S snapshot)
  | refuse (residue : ObservationAdmissionResidue)

/--
The common admission decision tree.

Snapshot mismatch is checked before capture authority, and capture authority
before certificate verification.  No caller-supplied status enters the result.
-/
def admitObservation
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (attempt : ObservationAttempt S snapshot)
    (authorization : CaptureAuthorization S snapshot attempt) :
    ObservationAdmissionResult S snapshot :=
  letI := S.snapshotQDecidableEq
  if _hsnapshot : attempt.claimedSnapshotQ = snapshot.snapshotQ then
    match authorization with
    | .absent =>
        .refuse .sourceCaptureUnverified
    | .certified authentic =>
        if haccepted :
            S.verify attempt.source attempt.raw
              attempt.observation attempt.certificate = true then
          .admitted
            { source := attempt.source
              raw := attempt.raw
              observation := attempt.observation
              certificate := attempt.certificate
              sourceAuthentic := authentic
              verifierAccepted := haccepted }
        else
          .refuse .certificateRefused
  else
    .refuse .staleSnapshot

/-- Every successful executable admission yields a true observation. -/
theorem admitted_result_is_sound
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    {attempt : ObservationAttempt S snapshot}
    {authorization : CaptureAuthorization S snapshot attempt}
    {packet : AdmittedObservation S snapshot}
    (_result :
      admitObservation attempt authorization = .admitted packet) :
    S.ObservationTrue snapshot.world packet.observation :=
  packet.sound

/-- A stale serialized snapshot identity cannot produce an admitted packet. -/
theorem stale_snapshot_is_refused
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (attempt : ObservationAttempt S snapshot)
    (authorization : CaptureAuthorization S snapshot attempt)
    (stale : attempt.claimedSnapshotQ ≠ snapshot.snapshotQ) :
    admitObservation attempt authorization =
      .refuse .staleSnapshot := by
  letI := S.snapshotQDecidableEq
  simp [admitObservation, stale]

/-- Missing capture authority is refused before certificate authority matters. -/
theorem absent_capture_authority_is_refused
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (attempt : ObservationAttempt S snapshot)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ) :
    admitObservation attempt (.absent) =
      .refuse .sourceCaptureUnverified := by
  letI := S.snapshotQDecidableEq
  simp [admitObservation, fresh]

/-- An authentic capture with a refused certificate is still not admitted. -/
theorem refused_certificate_is_not_admitted
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (attempt : ObservationAttempt S snapshot)
    (authentic :
      S.RawRepresents snapshot.world attempt.source attempt.raw)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ)
    (refused :
      S.verify attempt.source attempt.raw
        attempt.observation attempt.certificate ≠ true) :
    admitObservation attempt (.certified authentic) =
      .refuse .certificateRefused := by
  letI := S.snapshotQDecidableEq
  simp [admitObservation, fresh, refused]

/-! ## Logical-world projection -/

/-- A logical world contains only packets indexed by one sealed snapshot. -/
structure LogicalWorld
    (S : ObservationSystem)
    (snapshot : SealedWorldSnapshot S) where
  observations : List (AdmittedObservation S snapshot)

/-- Membership in a logical world cannot introduce an unsupported observation. -/
theorem logical_world_member_is_sound
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot)
    (packet : AdmittedObservation S snapshot)
    (_member : packet ∈ logicalWorld.observations) :
    S.ObservationTrue snapshot.world packet.observation :=
  packet.sound

end Residua.RCC.ObservationSoundness

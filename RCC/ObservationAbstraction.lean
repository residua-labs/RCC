import RCC.ObservationSoundness

/-!
# RCC WI-3 abstraction soundness from observations to model

WI-3 pins exactly one bridge: a proof-carrying abstraction from WI-1 admitted
observations at one sealed snapshot to a context-bound model claim.

The domain instance supplies an executable `abstract` function, but that
function has no authority by itself.  The common derivation requires:

* a WI-1 `LogicalWorld`, whose observations are all sound;
* exact snapshot freshness;
* proof that the model context is bound to that snapshot;
* the exact model computed by `abstract`; and
* an accepted abstraction certificate backed by `verifySound`.

This file does not claim WI-4 world-model adequacy.  Its terminal proposition
is `ModelClaim context observations model claim`, not an external intent.

Prelude-only Lean 4.14; no Mathlib, no custom axioms, no proof placeholders,
and only computable abstraction admission.
-/

namespace Residua.RCC.ObservationAbstraction

open Residua.RCC.ObservationSoundness

universe u v w x

/-- Domain-specific abstraction and its proof boundary. -/
structure AbstractionSystem (S : ObservationSystem) where
  ModelContext : Type u
  Model : Type v
  Claim : Type w
  Certificate : Type x

  /-- The context is valid for this exact sealed snapshot identity. -/
  ContextMatches : S.SnapshotQ → ModelContext → Prop

  /-- Executable model construction.  This function alone proves nothing. -/
  abstract : ModelContext → List S.Observation → Model

  /-- The exact proposition established inside the model layer. -/
  ModelClaim :
    ModelContext → List S.Observation → Model → Claim → Prop

  /-- Executable certificate verification for the exact abstraction tuple. -/
  verify :
    ModelContext → List S.Observation → Model → Claim → Certificate → Bool

  /--
  An accepted abstraction is sound only with a snapshot-bound context, sound
  source observations, and the exact output of `abstract`.
  -/
  verifySound :
    ∀ {world snapshotQ context observations model claim certificate},
      ContextMatches snapshotQ context →
        (∀ observation, observation ∈ observations →
          S.ObservationTrue world observation) →
        model = abstract context observations →
        verify context observations model claim certificate = true →
        ModelClaim context observations model claim

/-- Extract the semantic values from one exact WI-1 logical world. -/
def observationValues
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot) :
    List S.Observation :=
  logicalWorld.observations.map (fun packet => packet.observation)

/-- Every extracted value retains the WI-1 observation-soundness theorem. -/
theorem observationValuesSound
    {S : ObservationSystem}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot) :
    ∀ observation,
      observation ∈ observationValues logicalWorld →
        S.ObservationTrue snapshot.world observation := by
  intro observation member
  rcases List.mem_map.mp member with
    ⟨packet, packetMember, packetObservation⟩
  subst observation
  exact logical_world_member_is_sound
    logicalWorld packet packetMember

/-- Untrusted request for one model claim. -/
structure AbstractionAttempt
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (snapshot : SealedWorldSnapshot S) where
  claimedSnapshotQ : S.SnapshotQ
  context : A.ModelContext
  claim : A.Claim
  certificate : A.Certificate

/-- Context authority is proof-carrying or absent. -/
inductive ModelContextAuthorization
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (snapshot : SealedWorldSnapshot S)
    (attempt : AbstractionAttempt S A snapshot)
  | absent
  | certified
      (bound :
        A.ContextMatches snapshot.snapshotQ attempt.context)

/-- A model claim admitted from one exact logical world. -/
structure AdmittedModelClaim
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (snapshot : SealedWorldSnapshot S) where
  context : A.ModelContext
  observations : List S.Observation
  model : A.Model
  claim : A.Claim
  certificate : A.Certificate

  contextBound : A.ContextMatches snapshot.snapshotQ context
  observationsSound :
    ∀ observation, observation ∈ observations →
      S.ObservationTrue snapshot.world observation
  computed : model = A.abstract context observations
  verifierAccepted :
    A.verify context observations model claim certificate = true

/-- Every constructible model packet satisfies its exact internal model claim. -/
theorem AdmittedModelClaim.sound
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    (admitted : AdmittedModelClaim S A snapshot) :
    A.ModelClaim admitted.context admitted.observations
      admitted.model admitted.claim :=
  A.verifySound
    admitted.contextBound
    admitted.observationsSound
    admitted.computed
    admitted.verifierAccepted

/-- Exhaustive WI-3 refusal vocabulary. -/
inductive AbstractionResidue
  | staleObservationSnapshot
  | modelContextUnbound
  | abstractionCertificateRefused
  deriving DecidableEq, Repr

/-- Total proof-carrying abstraction result. -/
inductive AbstractionResult
    (S : ObservationSystem)
    (A : AbstractionSystem S)
    (snapshot : SealedWorldSnapshot S)
  | admitted (packet : AdmittedModelClaim S A snapshot)
  | refuse (residue : AbstractionResidue)

/--
Mechanical WI-3 derivation.

The instance cannot return `admitted`; it provides only the executable
abstraction, verifier, and verifier-soundness theorem.
-/
def abstractLogicalWorld
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot)
    (attempt : AbstractionAttempt S A snapshot)
    (authorization : ModelContextAuthorization S A snapshot attempt) :
    AbstractionResult S A snapshot :=
  letI := S.snapshotQDecidableEq
  if _fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ then
    match authorization with
    | .absent =>
        .refuse .modelContextUnbound
    | .certified bound =>
        let observations := observationValues logicalWorld
        let model := A.abstract attempt.context observations
        if accepted :
            A.verify attempt.context observations model
              attempt.claim attempt.certificate = true then
          .admitted
            { context := attempt.context
              observations := observations
              model := model
              claim := attempt.claim
              certificate := attempt.certificate
              contextBound := bound
              observationsSound :=
                observationValuesSound logicalWorld
              computed := rfl
              verifierAccepted := accepted }
        else
          .refuse .abstractionCertificateRefused
  else
    .refuse .staleObservationSnapshot

/-- Every successful executable abstraction yields its exact model claim. -/
theorem admitted_abstraction_is_sound
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    {logicalWorld : LogicalWorld S snapshot}
    {attempt : AbstractionAttempt S A snapshot}
    {authorization : ModelContextAuthorization S A snapshot attempt}
    {packet : AdmittedModelClaim S A snapshot}
    (_result :
      abstractLogicalWorld logicalWorld attempt authorization =
        .admitted packet) :
    A.ModelClaim packet.context packet.observations
      packet.model packet.claim :=
  packet.sound

/-- A stale observation snapshot cannot be abstracted into the current model. -/
theorem stale_abstraction_snapshot_is_refused
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot)
    (attempt : AbstractionAttempt S A snapshot)
    (authorization : ModelContextAuthorization S A snapshot attempt)
    (stale : attempt.claimedSnapshotQ ≠ snapshot.snapshotQ) :
    abstractLogicalWorld logicalWorld attempt authorization =
      .refuse .staleObservationSnapshot := by
  letI := S.snapshotQDecidableEq
  simp [abstractLogicalWorld, stale]

/-- An unbound model context is refused before abstraction verification. -/
theorem absent_model_context_is_refused
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot)
    (attempt : AbstractionAttempt S A snapshot)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ) :
    abstractLogicalWorld logicalWorld attempt (.absent) =
      .refuse .modelContextUnbound := by
  letI := S.snapshotQDecidableEq
  simp [abstractLogicalWorld, fresh]

/-- A rejected abstraction certificate cannot create model truth. -/
theorem refused_abstraction_certificate_is_not_admitted
    {S : ObservationSystem}
    {A : AbstractionSystem S}
    {snapshot : SealedWorldSnapshot S}
    (logicalWorld : LogicalWorld S snapshot)
    (attempt : AbstractionAttempt S A snapshot)
    (bound :
      A.ContextMatches snapshot.snapshotQ attempt.context)
    (fresh : attempt.claimedSnapshotQ = snapshot.snapshotQ)
    (refused :
      A.verify attempt.context (observationValues logicalWorld)
        (A.abstract attempt.context (observationValues logicalWorld))
        attempt.claim attempt.certificate ≠ true) :
    abstractLogicalWorld logicalWorld attempt (.certified bound) =
      .refuse .abstractionCertificateRefused := by
  letI := S.snapshotQDecidableEq
  simp [abstractLogicalWorld, fresh, refused]

end Residua.RCC.ObservationAbstraction

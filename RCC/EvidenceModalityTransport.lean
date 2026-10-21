import RCC.ClaimModality

/-!
# RCC CM-2 evidence-modality transport

CM-1 prevents evidence of one modality from being presented directly as
evidence of another modality.  CM-2 closes the remaining transport gap:

* preserving an already verified claim returns that exact verified object at
  the same modality;
* changing the claim or evidence target, even at the same modality, requires
  an explicit proof-carrying bridge;
* an absent bridge produces a typed refusal rather than an upgraded claim.

The modalities are deliberately not arranged in a caller-chosen total order.
Computational, probabilistic, statistical, empirical-window, and
assumption-relative evidence have different meanings.  The load-bearing rule
is therefore stronger and simpler: only exact preservation is implicit; every
retargeting must consume a `LawfulEvidenceBridge`.

In particular, a bridge name is not authority.  The certificate contains an
actual Lean function transporting semantic acceptance from the exact source
claim/evidence pair to the exact target pair.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.EvidenceModalityTransport

open Residua.RCC.ClaimModality

/--
An explicit proof that one verified evidence judgment lawfully entails a
specific target judgment.

Both endpoint pairs occur in the type of `preservesAcceptance`; a certificate
for one source, target, or verifier cannot be silently reused for another.
-/
structure LawfulEvidenceBridge
    (verifier : ModalityVerifier)
    {source target : Modality}
    (sourceVerified : VerifiedClaim verifier source)
    (targetClaim : Claim target)
    (targetEvidence : Evidence target) where
  bridgeQ : String
  preservesAcceptance :
    verifier.Accepts sourceVerified.claim sourceVerified.evidence →
      verifier.Accepts targetClaim targetEvidence

/--
Retargeting authority is exhaustive: either no bridge was supplied or a
proof-carrying bridge for these exact endpoints was supplied.
-/
inductive RetargetAuthorization
    (verifier : ModalityVerifier)
    {source target : Modality}
    (sourceVerified : VerifiedClaim verifier source)
    (targetClaim : Claim target)
    (targetEvidence : Evidence target)
  | absent
  | certified
      (certificate :
        LawfulEvidenceBridge
          verifier sourceVerified targetClaim targetEvidence)

/--
Transport requests distinguish identity-preserving movement from semantic
retargeting.  Merely retaining the same modality index does not make a changed
claim/evidence pair safe, so all retargeting goes through an authorization.
-/
inductive EvidenceTransportRequest
    (verifier : ModalityVerifier)
  | preserve
      {modality : Modality}
      (transportQ : String)
      (sourceVerified : VerifiedClaim verifier modality)
  | retarget
      {source target : Modality}
      (transportQ : String)
      (sourceVerified : VerifiedClaim verifier source)
      (targetClaim : Claim target)
      (targetEvidence : Evidence target)
      (authorization :
        RetargetAuthorization
          verifier sourceVerified targetClaim targetEvidence)

/-- Existential packaging of a verified claim after lawful transport. -/
inductive SomeVerifiedClaim
    (verifier : ModalityVerifier)
  | pack
      (modality : Modality)
      (verified : VerifiedClaim verifier modality)

/-- The modality remains derived from the dependent result type. -/
def SomeVerifiedClaim.modality :
    SomeVerifiedClaim verifier → Modality
  | .pack modality _ => modality

/-- The sole CM-2 refusal: a retargeting attempt omitted its lawful bridge. -/
inductive EvidenceTransportResidue
  | lawfulBridgeMissing (source target : Modality)
  deriving DecidableEq, Repr

/-- Total, proof-carrying evidence-transport result. -/
inductive EvidenceTransportResult
    (verifier : ModalityVerifier)
  | transported
      (transportQ : String)
      (verified : SomeVerifiedClaim verifier)
  | refuse
      (residue : EvidenceTransportResidue)

/-- Whether the result contains an actually verified target judgment. -/
def EvidenceTransportResult.isTransported :
    EvidenceTransportResult verifier → Bool
  | .transported _ _ => true
  | .refuse _ => false

/-- Report the target modality only for a successful transport. -/
def EvidenceTransportResult.transportedModality :
    EvidenceTransportResult verifier → Option Modality
  | .transported _ verified => some verified.modality
  | .refuse _ => none

/--
The uniform CM-2 derivation.

The `preserve` branch returns the exact source proof.  The certified branch
constructs target acceptance only by applying the supplied bridge theorem to
the source acceptance proof.  No other branch can construct a target claim.
-/
def deriveEvidenceTransport
    (request : EvidenceTransportRequest verifier) :
    EvidenceTransportResult verifier :=
  match request with
  | .preserve (modality := modality) transportQ sourceVerified =>
      .transported transportQ
        (.pack modality sourceVerified)
  | .retarget (source := source) (target := target)
      _ _ _ _ .absent =>
      .refuse
        (.lawfulBridgeMissing source target)
  | .retarget (target := target)
      transportQ sourceVerified targetClaim targetEvidence
      (.certified certificate) =>
      .transported transportQ
        (.pack target
          { claim := targetClaim
            evidence := targetEvidence
            accepted :=
              certificate.preservesAcceptance sourceVerified.accepted })

/-- Exact preservation never changes the evidence modality. -/
theorem preservation_transport_retains_modality
    {verifier : ModalityVerifier}
    {modality : Modality}
    (transportQ : String)
    (sourceVerified : VerifiedClaim verifier modality) :
    (deriveEvidenceTransport
      (.preserve transportQ sourceVerified)).transportedModality =
        some modality := by
  rfl

/--
Any retargeting request without a bridge is refused, including every
non-deductive-to-deductive upgrade.
-/
theorem unbridged_retargeting_is_refused
    {verifier : ModalityVerifier}
    {source target : Modality}
    (transportQ : String)
    (sourceVerified : VerifiedClaim verifier source)
    (targetClaim : Claim target)
    (targetEvidence : Evidence target) :
    deriveEvidenceTransport
        (.retarget transportQ sourceVerified targetClaim targetEvidence
          .absent) =
      .refuse (.lawfulBridgeMissing source target) := by
  rfl

/-- A certified bridge reports exactly its target modality. -/
theorem certified_retargeting_reports_target_modality
    {verifier : ModalityVerifier}
    {source target : Modality}
    (transportQ : String)
    (sourceVerified : VerifiedClaim verifier source)
    (targetClaim : Claim target)
    (targetEvidence : Evidence target)
    (certificate :
      LawfulEvidenceBridge
        verifier sourceVerified targetClaim targetEvidence) :
    (deriveEvidenceTransport
      (.retarget transportQ sourceVerified targetClaim targetEvidence
        (.certified certificate))).transportedModality =
      some target := by
  rfl

/--
A successful retargeting authorization cannot be the absent constructor.
This is the proof-level form of “no silent evidence upgrade”.
-/
theorem transported_retargeting_requires_bridge
    {verifier : ModalityVerifier}
    {source target : Modality}
    (transportQ : String)
    (sourceVerified : VerifiedClaim verifier source)
    (targetClaim : Claim target)
    (targetEvidence : Evidence target)
    (authorization :
      RetargetAuthorization
        verifier sourceVerified targetClaim targetEvidence)
    (transported :
      (deriveEvidenceTransport
        (.retarget transportQ sourceVerified targetClaim targetEvidence
          authorization)).isTransported = true) :
    ∃ certificate,
      authorization = RetargetAuthorization.certified certificate := by
  cases authorization with
  | absent =>
      simp [deriveEvidenceTransport,
        EvidenceTransportResult.isTransported] at transported
  | certified certificate =>
      exact ⟨certificate, rfl⟩

end Residua.RCC.EvidenceModalityTransport

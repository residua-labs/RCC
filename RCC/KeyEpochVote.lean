import RCC.AuthorityReconfiguration
import RCC.DurableVoteLock

/-!
# RCC-52 Key-Epoch Vote Admissibility

An admissible vote is derived from an actual RCC-41 durable signature release
and an actual RCC-44 lawful authority-transition coordinate.  The signed vote
binds signer key epoch, active configuration epoch, slot, parent head, round,
policy, prior-vote continuity, and canonical judgment.  A physical runtime key
is additionally bound to that signed signer/key epoch by a single-valued
registry.

Active and retired key evidence is not an arbitrary deployment predicate.  It
is derived from the `added` and `removed` membership lists of the exact RCC-44
transition authorized at the exact activation coordinate.  This kernel models
one key-epoch rotation per transition; proving that the transition membership
delta is a complete projection of the deployment remains the RCC-44 runtime
adapter obligation.

Prelude-only Lean 4.14; no Mathlib, axioms, or proof placeholders.
-/

namespace Residua.RCC.KeyEpochVote

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock

universe u

/-- The configuration epoch selected by an RCC-44 authority phase. -/
def phaseConfig
    {Config Slot Head Authority Member : Type u}
    (transition :
      AuthorityTransition Config Slot Head Authority Member) :
    AuthorityPhase → Config
  | .old => transition.oldConfig
  | .new => transition.newConfig

/--
The key-epoch coordinates carried by the actual RCC-44 membership delta.
`noAddedRemovedOverlap` makes retirement and activation disjoint, while
`configEpochChanges` prevents an old configuration epoch from being replayed
after the boundary under an unchanged configuration identity.
-/
structure LawfulKeyEpochTransition
    {Q : Type u}
    (transition : AuthorityTransition Q Q Q Q Q) where
  oldKeyEpochQ : Q
  newKeyEpochQ : Q
  oldEpochRemoved :
    oldKeyEpochQ ∈ transition.membershipDelta.removed
  newEpochAdded :
    newKeyEpochQ ∈ transition.membershipDelta.added
  noAddedRemovedOverlap :
    ∀ {keyEpochQ},
      keyEpochQ ∈ transition.membershipDelta.added →
      keyEpochQ ∈ transition.membershipDelta.removed →
      False
  configEpochChanges : transition.oldConfig ≠ transition.newConfig

/-- The signer key epoch selected by the lawful RCC-44 authority phase. -/
def phaseKeyEpoch
    {Q : Type u}
    {transition : AuthorityTransition Q Q Q Q Q}
    (lawful : LawfulKeyEpochTransition transition) :
    AuthorityPhase → Q
  | .old => lawful.oldKeyEpochQ
  | .new => lawful.newKeyEpochQ

/-- The old and new key epochs of a lawful transition are distinct. -/
theorem LawfulKeyEpochTransition.keyEpochsDistinct
    {Q : Type u}
    {transition : AuthorityTransition Q Q Q Q Q}
    (lawful : LawfulKeyEpochTransition transition) :
    lawful.oldKeyEpochQ ≠ lawful.newKeyEpochQ := by
  intro sameEpoch
  exact lawful.noAddedRemovedOverlap
    lawful.newEpochAdded
    (sameEpoch ▸ lawful.oldEpochRemoved)

/--
The complete RCC-52 payload derived from one actual released signature.
`runtimeKeyQ` belongs to the release envelope; every other semantic coordinate
is covered by the signed RCC-41 `Vote`.
-/
structure KeyEpochVotePayload (Q : Type u) where
  signerQ : Q
  signerKeyEpochQ : Q
  runtimeKeyQ : Q
  activeConfigEpochQ : Q
  slotQ : Q
  parentHeadQ : Q
  round : Nat
  judgment : CanonicalJudgment Q
  policyQ : Q
  priorVoteQ : Option Q
  deriving DecidableEq, Repr

/-- Mechanically project the complete payload from an RCC-41 release. -/
def releasedKeyEpochPayload
    {Q : Type u}
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) :
    KeyEpochVotePayload Q where
  signerQ := (releasedVote release).signerQ
  signerKeyEpochQ := (releasedVote release).epochQ
  runtimeKeyQ := release.runtime.keyQ
  activeConfigEpochQ := (releasedVote release).configQ
  slotQ := (releasedVote release).slotQ
  parentHeadQ := (releasedVote release).parentHeadQ
  round := (releasedVote release).round
  judgment := canonicalJudgment (releasedVote release)
  policyQ := (releasedVote release).policyQ
  priorVoteQ := (releasedVote release).priorVoteQ

/--
A complete deployment registry binds one physical runtime key to at most one
signer key epoch for a logical signer.  Absence is not evidence of retirement;
the positive relation is consumed only by an admissible certificate.
-/
structure RuntimeKeyEpochRegistry (Q : Type u) where
  Binds : Q → Q → Q → Prop
  runtimeKeyBindsOneEpoch :
    ∀ {signerQ runtimeKeyQ firstEpochQ secondEpochQ},
      Binds signerQ runtimeKeyQ firstEpochQ →
      Binds signerQ runtimeKeyQ secondEpochQ →
      firstEpochQ = secondEpochQ

/--
An admissible key-epoch vote consumes:

* the actual authorized RCC-44 activation;
* a lawful key rotation derived from that transition's membership delta;
* the actual RCC-41 durable signature release; and
* the single-valued runtime-key registry binding.

No caller-supplied payload or active-key predicate appears in this type.
-/
structure KeyEpochVoteCertificate
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat} {phase : AuthorityPhase}
    (activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round phase)
    (lawful : LawfulKeyEpochTransition transition)
    (registry : RuntimeKeyEpochRegistry Q)
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) : Type u where
  activeConfigEpochBound :
    (releasedKeyEpochPayload release).activeConfigEpochQ =
      phaseConfig transition phase
  signerKeyEpochBound :
    (releasedKeyEpochPayload release).signerKeyEpochQ =
      phaseKeyEpoch lawful phase
  slotBound : (releasedKeyEpochPayload release).slotQ = slot
  parentHeadBound :
    (releasedKeyEpochPayload release).parentHeadQ = head
  roundBound : (releasedKeyEpochPayload release).round = round
  runtimeKeyEpochBound :
    registry.Binds
      (releasedKeyEpochPayload release).signerQ
      (releasedKeyEpochPayload release).runtimeKeyQ
      (releasedKeyEpochPayload release).signerKeyEpochQ

/--
A retired-key certificate is available only in the actual new phase and only
for the old epoch named in the actual transition's `removed` membership list.
-/
structure RetiredKeyEpochCertificate
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat}
    (activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round .new)
    (lawful : LawfulKeyEpochTransition transition)
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) : Type u where
  retiredEpochBound :
    (releasedKeyEpochPayload release).signerKeyEpochQ =
      lawful.oldKeyEpochQ

/-- The active new epoch is in the actual RCC-44 `added` membership list. -/
theorem new_phase_active_epoch_is_transition_added
    {Q : Type u}
    {transition : AuthorityTransition Q Q Q Q Q}
    (lawful : LawfulKeyEpochTransition transition) :
    phaseKeyEpoch lawful .new ∈ transition.membershipDelta.added :=
  lawful.newEpochAdded

/-- The retired epoch is in the actual RCC-44 `removed` membership list. -/
theorem retired_epoch_is_transition_removed
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round .new}
    {lawful : LawfulKeyEpochTransition transition}
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    (_retired :
      RetiredKeyEpochCertificate activation lawful release) :
    lawful.oldKeyEpochQ ∈ transition.membershipDelta.removed :=
  lawful.oldEpochRemoved

/--
One runtime key cannot be reused for both epochs of a lawful transition.
This is the load-bearing registry countermodel, not a comparison of key bytes.
-/
theorem runtime_key_reuse_across_transition_epochs_impossible
    {Q : Type u}
    {transition : AuthorityTransition Q Q Q Q Q}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {signerQ runtimeKeyQ : Q}
    (oldBinding :
      registry.Binds signerQ runtimeKeyQ lawful.oldKeyEpochQ)
    (newBinding :
      registry.Binds signerQ runtimeKeyQ lawful.newKeyEpochQ) :
    False :=
  lawful.keyEpochsDistinct
    (registry.runtimeKeyBindsOneEpoch oldBinding newBinding)

/--
The same actual release cannot be both admissible and retired in the new
phase.  The contradiction is discharged by the RCC-44 membership delta.
-/
theorem active_and_retired_new_epoch_conflict
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round .new}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    (active :
      KeyEpochVoteCertificate activation lawful registry release)
    (retired :
      RetiredKeyEpochCertificate activation lawful release) :
    False := by
  apply lawful.keyEpochsDistinct
  exact retired.retiredEpochBound.symm.trans active.signerKeyEpochBound

/--
Every certificate exposes the full signed/activation binding, including the
canonical judgment.  Judgment equality is definitional because the payload is
mechanically projected from the exact RCC-41 released vote.
-/
theorem certificate_binds_complete_vote_payload
    {Q : Type u}
    {AuthorityEvidence : Proposal Q Q Q → Type u}
    [DecidableEq Q]
    {jointProtocol :
      JointQuorumProtocol Q Q Q Q Q Q Q}
    {spec : FencedWriterSpec Q Q}
    {equivalence : JudgmentEquivalence Q}
    {adapter :
      ReconfigurationJudgmentAdapter Q Q Q Q Q Q equivalence}
    {state : FencedWriterState Q Q Q Q}
    {transition : AuthorityTransition Q Q Q Q Q}
    {envelope :
      AuthorizedTransitionEnvelope
        AuthorityEvidence jointProtocol spec equivalence adapter state}
    {slot head : Q} {round : Nat} {phase : AuthorityPhase}
    {activation :
      AuthorizedActivationEvidence
        AuthorityEvidence jointProtocol spec equivalence adapter state
          transition envelope slot head round phase}
    {lawful : LawfulKeyEpochTransition transition}
    {registry : RuntimeKeyEpochRegistry Q}
    {scheme : SignatureScheme Q}
    {release : ReleasedSignature Q scheme}
    (certificate :
      KeyEpochVoteCertificate activation lawful registry release) :
    ActiveAt transition slot head round phase ∧
      (releasedKeyEpochPayload release).signerQ =
        (releasedVote release).signerQ ∧
      (releasedKeyEpochPayload release).signerKeyEpochQ =
        phaseKeyEpoch lawful phase ∧
      (releasedKeyEpochPayload release).runtimeKeyQ =
        release.runtime.keyQ ∧
      (releasedKeyEpochPayload release).activeConfigEpochQ =
        phaseConfig transition phase ∧
      (releasedKeyEpochPayload release).slotQ = slot ∧
      (releasedKeyEpochPayload release).parentHeadQ = head ∧
      (releasedKeyEpochPayload release).round = round ∧
      (releasedKeyEpochPayload release).judgment =
        canonicalJudgment (releasedVote release) ∧
      registry.Binds
        (releasedVote release).signerQ
        release.runtime.keyQ
        (releasedVote release).epochQ := by
  exact
    ⟨activation.active, rfl, certificate.signerKeyEpochBound, rfl,
      certificate.activeConfigEpochBound, certificate.slotBound,
      certificate.parentHeadBound, certificate.roundBound, rfl,
      certificate.runtimeKeyEpochBound⟩

/-- RCC-52 result polarity: missing evidence awaits; retirement refuses. -/
inductive KeyEpochVoteAssessment
    (Admissible Retired : Type u)
  | admissible :
      Admissible → KeyEpochVoteAssessment Admissible Retired
  | await :
      KeyEpochVoteAssessment Admissible Retired
  | refuse :
      Retired → KeyEpochVoteAssessment Admissible Retired

/-- Mechanical RCC-52 evidence gate over the proof-carrying certificates. -/
def assessKeyEpochVote
    {Admissible Retired : Type u}
    (admissible? : Option Admissible)
    (retired? : Option Retired) :
    KeyEpochVoteAssessment Admissible Retired :=
  match admissible?, retired? with
  | some certificate, none => .admissible certificate
  | _, some certificate => .refuse certificate
  | none, none => .await

end Residua.RCC.KeyEpochVote

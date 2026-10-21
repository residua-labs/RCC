import Init

/-!
# RCC-41 Durable Signer Non-Equivocation

A vote binds config, epoch, slot, parent head, round, proposal class, policy,
verdict, signer, and prior vote.  A released signature additionally carries
proof that one signature scheme accepted the canonical full-vote message and
binds that vote to a durable lock commit preceding signature release.

Crash recovery, process multiplicity, and key rotation do not create a fresh
logical signer.  Their non-faulty path is exact lock restoration/transport, or
a certified higher-round unlock carrying prior-lock continuity.  The main
theorem proves that such a signer cannot release conflicting judgments.

This logical kernel does not prove that a storage device really persisted the
commit before external signature bytes escaped.  That implementation/effect
binding remains an explicit RCC runtime assumption and adversarial test target.

Prelude-only Lean 4.14; no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.DurableVoteLock

universe u

/-- The complete canonical context covered by one vote signature. -/
structure Vote (Q : Type u) where
  configQ : Q
  epochQ : Q
  slotQ : Q
  parentHeadQ : Q
  round : Nat
  proposalClassQ : Q
  policyQ : Q
  verdict : Q
  signerQ : Q
  priorVoteQ : Option Q

/-- A durable lock names both the exact vote and its stable lock identity. -/
structure VoteLock (Q : Type u) where
  vote : Vote Q
  lockQ : Q

/-- Proof object that the lock reached durable storage at this sequence. -/
structure DurableLockCommit (Q : Type u) where
  lock : VoteLock Q
  committedAt : Nat

/--
A signature scheme supplies a canonical full-vote message and proof that both
canonicalization and accepted signatures bind uniquely.  Cryptographic
soundness remains an implementation assumption represented by `Accepts`.
-/
structure SignatureScheme (Q : Type u) where
  Signature : Type u
  Message : Type u
  canonicalVoteMessage : Vote Q → Message
  canonicalVoteMessage_injective :
    ∀ {first second},
      canonicalVoteMessage first = canonicalVoteMessage second →
      first = second
  Accepts : Signature → Message → Prop
  acceptanceBindsMessage :
    ∀ {signature first second},
      Accepts signature first →
      Accepts signature second →
      first = second

/-- Signature bytes paired with the complete structured vote they claim. -/
structure SignatureEnvelope (Q : Type u) (scheme : SignatureScheme Q) where
  signedVote : Vote Q
  signatureQ : scheme.Signature

/-- Proof that an envelope's signature accepts its canonical full-vote message. -/
structure SignatureBinding {Q : Type u} (scheme : SignatureScheme Q)
    (envelope : SignatureEnvelope Q scheme) : Prop where
  accepted :
    scheme.Accepts envelope.signatureQ
      (scheme.canonicalVoteMessage envelope.signedVote)

/-- One accepted signature cannot bind two distinct canonical votes. -/
theorem same_signature_acceptance_unique_vote
    {Q : Type u} {scheme : SignatureScheme Q}
    {signature : scheme.Signature} {first second : Vote Q}
    (firstAccepted :
      scheme.Accepts signature (scheme.canonicalVoteMessage first))
    (secondAccepted :
      scheme.Accepts signature (scheme.canonicalVoteMessage second)) :
    first = second := by
  apply scheme.canonicalVoteMessage_injective
  exact scheme.acceptanceBindsMessage firstAccepted secondAccepted

/--
Physical key and process identities may change while the logical signer
identity remains stable.
-/
structure SignerRuntime (Q : Type u) where
  signerQ : Q
  keyQ : Q
  processQ : Q

/--
A lawful release can be constructed only after a matching durable lock commit.
The strict sequence proof is the formal write-before-release ordering.
-/
structure ReleasedSignature (Q : Type u) (scheme : SignatureScheme Q) where
  commit : DurableLockCommit Q
  envelope : SignatureEnvelope Q scheme
  validSignature : SignatureBinding scheme envelope
  signatureBindsLock : envelope.signedVote = commit.lock.vote
  runtime : SignerRuntime Q
  runtimeSigner : runtime.signerQ = envelope.signedVote.signerQ
  releasedAt : Nat
  lockBeforeRelease : commit.committedAt < releasedAt

/-- The exact vote whose complete canonical bytes were signed. -/
def releasedVote {Q : Type u} {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) : Vote Q :=
  release.envelope.signedVote

/-- The judgment coordinates whose conflict requires lock continuity. -/
structure CanonicalJudgment (Q : Type u) where
  proposalClassQ : Q
  verdict : Q
  deriving DecidableEq, Repr

/-- Project one complete vote to its canonical judgment. -/
def canonicalJudgment {Q : Type u} (vote : Vote Q) : CanonicalJudgment Q :=
  ⟨vote.proposalClassQ, vote.verdict⟩

/--
Decision context equality excludes round and canonical judgment, which may
advance only through a lawful higher-round unlock.
-/
def SameDecisionContext {Q : Type u} (first second : Vote Q) : Prop :=
  first.configQ = second.configQ ∧
    first.epochQ = second.epochQ ∧
    first.slotQ = second.slotQ ∧
    first.parentHeadQ = second.parentHeadQ ∧
    first.policyQ = second.policyQ

/-- Durable identity and commit sequence of an unlock certificate. -/
structure UnlockCertificate (Q : Type u) where
  certificateQ : Q
  committedAt : Nat

/--
A proposal change is lawful only at a strictly higher round, with a certificate
committed before the replacement lock and an explicit prior-lock reference.
-/
structure LawfulHigherRoundUnlock {Q : Type u}
    (oldCommit newCommit : DurableLockCommit Q)
    (certificate : UnlockCertificate Q) : Prop where
  sameDecisionContext :
    SameDecisionContext oldCommit.lock.vote newCommit.lock.vote
  sameSigner :
    oldCommit.lock.vote.signerQ = newCommit.lock.vote.signerQ
  higherRound :
    oldCommit.lock.vote.round < newCommit.lock.vote.round
  priorVoteContinuity :
    newCommit.lock.vote.priorVoteQ = some oldCommit.lock.lockQ
  certificateBeforeNewLock : certificate.committedAt < newCommit.committedAt

/-- Existential package used by conflict detection. -/
def HasLawfulHigherRoundUnlock {Q : Type u}
    (oldCommit newCommit : DurableLockCommit Q) : Prop :=
  ∃ certificate, LawfulHigherRoundUnlock oldCommit newCommit certificate

/--
The durable lock lineage either restores/transports the exact same lock or
advances through a lawful higher-round unlock certificate.
-/
inductive LockContinuity {Q : Type u}
    (oldCommit newCommit : DurableLockCommit Q) : Prop
  | restore : oldCommit.lock = newCommit.lock →
      LockContinuity oldCommit newCommit
  | unlock : (certificate : UnlockCertificate Q) →
      LawfulHigherRoundUnlock oldCommit newCommit certificate →
      LockContinuity oldCommit newCommit

/-- Pair orientation is irrelevant when comparing two historical releases. -/
inductive OrientedLockContinuity {Q : Type u} {scheme : SignatureScheme Q}
    (first second : ReleasedSignature Q scheme) : Prop
  | forward : LockContinuity first.commit second.commit →
      OrientedLockContinuity first second
  | backward : LockContinuity second.commit first.commit →
      OrientedLockContinuity first second

/--
Two same-signer releases conflict exactly when they share one decision context,
carry unequal canonical judgments, and no lawful unlock orders them.
-/
def ConflictingJudgments {Q : Type u} {scheme : SignatureScheme Q}
    (first second : ReleasedSignature Q scheme) : Prop :=
  SameDecisionContext (releasedVote first) (releasedVote second) ∧
    (releasedVote first).signerQ = (releasedVote second).signerQ ∧
    canonicalJudgment (releasedVote first) ≠
      canonicalJudgment (releasedVote second) ∧
    ¬ HasLawfulHigherRoundUnlock first.commit second.commit ∧
    ¬ HasLawfulHigherRoundUnlock second.commit first.commit

/--
Non-faulty signer continuity is proof-carrying, never a Bool tag.  Runtime
processes and physical keys may differ, but the logical signer and lock lineage
must remain connected.
-/
structure NonFaultySignerContinuity {Q : Type u}
    {scheme : SignatureScheme Q}
    (first second : ReleasedSignature Q scheme) : Prop where
  sameSigner :
    (releasedVote first).signerQ = (releasedVote second).signerQ
  lockContinuity : OrientedLockContinuity first second

/--
At one round, non-faulty lock continuity collapses to exact lock restoration,
so the canonical judgment is equal.  A lawful unlock cannot inhabit this case
because it requires a strictly higher round.
-/
theorem same_round_continuity_canonical_judgment_equal
    {Q : Type u} {scheme : SignatureScheme Q}
    {first second : ReleasedSignature Q scheme}
    (nonfaulty : NonFaultySignerContinuity first second)
    (sameRound :
      (releasedVote first).round = (releasedVote second).round) :
    canonicalJudgment (releasedVote first) =
      canonicalJudgment (releasedVote second) := by
  have sameCommitRound :
      first.commit.lock.vote.round = second.commit.lock.vote.round := by
    calc
      first.commit.lock.vote.round = (releasedVote first).round :=
        congrArg Vote.round first.signatureBindsLock.symm
      _ = (releasedVote second).round := sameRound
      _ = second.commit.lock.vote.round :=
        congrArg Vote.round second.signatureBindsLock
  cases nonfaulty.lockContinuity with
  | forward continuity =>
      cases continuity with
      | restore sameLock =>
          have sameVote : releasedVote first = releasedVote second := by
            calc
              releasedVote first = first.commit.lock.vote :=
                first.signatureBindsLock
              _ = second.commit.lock.vote :=
                congrArg VoteLock.vote sameLock
              _ = releasedVote second :=
                second.signatureBindsLock.symm
          exact congrArg canonicalJudgment sameVote
      | unlock certificate lawful =>
          exact False.elim
            ((Nat.ne_of_lt lawful.higherRound) sameCommitRound)
  | backward continuity =>
      cases continuity with
      | restore sameLock =>
          have sameVote : releasedVote second = releasedVote first := by
            calc
              releasedVote second = second.commit.lock.vote :=
                second.signatureBindsLock
              _ = first.commit.lock.vote :=
                congrArg VoteLock.vote sameLock
              _ = releasedVote first :=
                first.signatureBindsLock.symm
          exact (congrArg canonicalJudgment sameVote).symm
      | unlock certificate lawful =>
          exact False.elim
            ((Nat.ne_of_lt lawful.higherRound) sameCommitRound.symm)

/--
RCC-41 Durable Signer Non-Equivocation: two releases connected by the
non-faulty durable-lock protocol cannot be conflicting judgments.
-/
theorem durable_signer_non_equivocation
    {Q : Type u} {scheme : SignatureScheme Q}
    {first second : ReleasedSignature Q scheme}
    (nonfaulty : NonFaultySignerContinuity first second) :
    ¬ ConflictingJudgments first second := by
  intro conflict
  cases nonfaulty.lockContinuity with
  | forward continuity =>
      cases continuity with
      | restore sameLock =>
          have sameVote : releasedVote first = releasedVote second := by
            calc
              releasedVote first = first.commit.lock.vote :=
                first.signatureBindsLock
              _ = second.commit.lock.vote :=
                congrArg VoteLock.vote sameLock
              _ = releasedVote second :=
                second.signatureBindsLock.symm
          exact conflict.2.2.1
            (congrArg canonicalJudgment sameVote)
      | unlock certificate lawful =>
          exact conflict.2.2.2.1 ⟨certificate, lawful⟩
  | backward continuity =>
      cases continuity with
      | restore sameLock =>
          have sameVote : releasedVote second = releasedVote first := by
            calc
              releasedVote second = second.commit.lock.vote :=
                second.signatureBindsLock
              _ = first.commit.lock.vote :=
                congrArg VoteLock.vote sameLock
              _ = releasedVote first :=
                first.signatureBindsLock.symm
          exact conflict.2.2.1
            (congrArg canonicalJudgment sameVote).symm
      | unlock certificate lawful =>
          exact conflict.2.2.2.2 ⟨certificate, lawful⟩

/--
The intentionally unsafe contrast: signing only a proposal class permits the
same bytes to replay across config, epoch, slot, head, round, policy, verdict,
signer, and prior-lock coordinates.
-/
structure BareProposalSignature (Q : Type u) where
  proposalClassQ : Q
  signatureQ : Q

def BareSignatureAccepts {Q : Type u}
    (signature : BareProposalSignature Q) (vote : Vote Q) : Prop :=
  signature.proposalClassQ = vote.proposalClassQ

end Residua.RCC.DurableVoteLock

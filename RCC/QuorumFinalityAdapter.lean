import RCC.AuthorizationFinality
import RCC.EffectiveAuthorityQuorum
import RCC.QuorumIntersectionSafety
import RCC.DurableVoteLock

/-!
# RCC-34 / RCC-40 / RCC-41 → RCC-39 Quorum Finality Adapter

This adapter realizes RCC-40 locked votes from RCC-41 released signatures.
Honest non-equivocation is derived from proof-carrying durable signer
continuity; callers cannot insert an opaque `HonestNonEquivocation` premise.

Authorization is realized separately from finality.  A proposal-indexed
`EffectiveQuorumAuthorityEvidence` contains both an RCC-34
`LawfulAuthorityAct` and the exact RCC-40 quorum certificate, with explicit
bindings for the act, signer set, config, policy, and authority-context epoch.
RCC-39 finality additionally consumes an independent canonical-linearizer
receipt at an externally supplied canonical head.  A bare QC therefore cannot
manufacture finality, and a proposal cannot select its own parent as canonical.

The completeness of `allowedFaultSets` is caller-supplied.  Cryptographic
signature soundness, runtime write-before-release fidelity, and physical
storage durability remain explicit implementation assumptions/nonclaims.

Prelude-only Lean 4.14; no Mathlib, axioms, detector, registry, workflow, or
aggregator changes.
-/

namespace Residua.RCC.QuorumFinalityAdapter

open Residua.RCC.AuthorizationFinality
open Residua.RCC.DurableVoteLock
open Residua.RCC.EffectiveAuthorityQuorum
open Residua.RCC.QuorumIntersectionSafety

universe u v w x

/-- Every coordinate that fixes one quorum decision slot. -/
structure DecisionSlot (Q : Type u) where
  configQ : Q
  epochQ : Q
  slotQ : Q
  parentHeadQ : Q
  round : Nat
  policyQ : Q
  deriving DecidableEq, Repr

/-- Project a complete RCC-41 vote to its RCC-40 decision slot. -/
def decisionSlot {Q : Type u} (vote : Vote Q) : DecisionSlot Q where
  configQ := vote.configQ
  epochQ := vote.epochQ
  slotQ := vote.slotQ
  parentHeadQ := vote.parentHeadQ
  round := vote.round
  policyQ := vote.policyQ

/-- Finite quorum configuration reused by the RCC-40 safety kernel. -/
structure QuorumConfiguration (Q : Type u) where
  members : List Q
  quorums : List (List Q)
  allowedFaultSets : List (List Q)

/--
The explicit realization bridge from RCC-34 authority objects to the
coordinates signed by RCC-41 votes.

The signer projection is injective: two distinct RCC-34 signers cannot collapse
to one quorum member address.  The remaining functions are normative
projections of the *actual* quorum configuration, policy, and sealed authority
context supplied to the certificate.  They are not unindexed Q constants
selected by one certificate.
-/
structure EffectiveAuthorityBinding
    (Q : Type u) (system : AuthoritySystem) where
  signerQ : system.Signer → Q
  signerQInjective :
    ∀ {first second}, signerQ first = signerQ second → first = second
  actFor :
    Proposal (DecisionSlot Q) Q (CanonicalJudgment Q) → system.ActQ
  configQ : QuorumConfiguration Q → Q
  policyQ : AuthorityPolicy system → Q
  contextEpochQ : system.Context → Q

/--
The RCC-40 realization uses exact equality of RCC-41 canonical
`(proposal, verdict)` judgments.
-/
def quorumSystem {Q : Type u}
    (config : QuorumConfiguration Q) : FiniteQuorumSystem where
  Member := Q
  Slot := DecisionSlot Q
  Judgment := CanonicalJudgment Q
  equivalent := Eq
  members := config.members
  quorums := config.quorums
  allowedFaultSets := config.allowedFaultSets

/-- One released RCC-41 vote realized as an RCC-40 locked vote. -/
def releaseLockedVote {Q : Type u}
    (config : QuorumConfiguration Q)
    {scheme : SignatureScheme Q}
    (release : ReleasedSignature Q scheme) :
    LockedVote (quorumSystem config) where
  signer := (releasedVote release).signerQ
  slot := decisionSlot (releasedVote release)
  judgment := canonicalJudgment (releasedVote release)

/-- The complete finite released-signature snapshot as RCC-40 lock state. -/
def releaseLocks {Q : Type u}
    (config : QuorumConfiguration Q)
    {scheme : SignatureScheme Q}
    (releases : List (ReleasedSignature Q scheme)) :
    VoteLockState (quorumSystem config) where
  lockedVotes := releases.map (releaseLockedVote config)

/--
Every pair of releases attributed to one honest configured signer at one
complete slot carries RCC-41 durable continuity.
-/
structure HonestSignerContinuity {Q : Type u}
    (config : QuorumConfiguration Q)
    (scheme : SignatureScheme Q)
    (releases : List (ReleasedSignature Q scheme))
    (faultSet : List Q) : Prop where
  pairwise :
    ∀ first,
      first ∈ releases →
        ∀ second,
          second ∈ releases →
            (releasedVote first).signerQ =
                (releasedVote second).signerQ →
              (releasedVote first).signerQ ∈ config.members →
                (releasedVote first).signerQ ∉ faultSet →
                  decisionSlot (releasedVote first) =
                      decisionSlot (releasedVote second) →
                    NonFaultySignerContinuity first second

/--
The complete quorum-safety adapter.  Its non-equivocation law is not a field:
it is derived below from RCC-41 continuity.
-/
structure QuorumFinalityAdapter {Q : Type u}
    (config : QuorumConfiguration Q)
    (scheme : SignatureScheme Q)
    (releases : List (ReleasedSignature Q scheme))
    (faultSet : List Q) : Prop where
  intersectionSafe : QuorumIntersectionSafe (quorumSystem config)
  faultAllowed : AllowedFaultSet (quorumSystem config) faultSet
  continuity : HonestSignerContinuity config scheme releases faultSet

/-- Recover the RCC-41 release underlying an RCC-40 lock membership proof. -/
theorem release_origin_of_locked_vote
    {Q : Type u}
    (config : QuorumConfiguration Q)
    {scheme : SignatureScheme Q}
    (releases : List (ReleasedSignature Q scheme))
    {signer : Q}
    {slot : DecisionSlot Q}
    {judgment : CanonicalJudgment Q}
    (locked :
      HasLockedVote
        (releaseLocks config releases) signer slot judgment) :
    ∃ release,
      release ∈ releases ∧
        (releasedVote release).signerQ = signer ∧
        decisionSlot (releasedVote release) = slot ∧
        canonicalJudgment (releasedVote release) = judgment := by
  obtain ⟨entry, entryIn, signerBound, slotBound, judgmentBound⟩ := locked
  change entry ∈ releases.map (releaseLockedVote config) at entryIn
  obtain ⟨release, releaseIn, releaseBound⟩ := List.mem_map.mp entryIn
  subst entry
  exact ⟨release, releaseIn, signerBound, slotBound, judgmentBound⟩

/--
RCC-41 pairwise continuity discharges RCC-40 honest non-equivocation for the
realized lock snapshot.
-/
theorem honest_signer_continuity_implies_non_equivocation
    {Q : Type u}
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    (adapter :
      QuorumFinalityAdapter config scheme releases faultSet) :
    HonestNonEquivocation
      (quorumSystem config) (releaseLocks config releases) faultSet := by
  intro signer signerMember signerHonest slot firstJudgment secondJudgment
    firstLocked secondLocked
  obtain ⟨first, firstIn, firstSigner, firstSlot, firstJudgmentBound⟩ :=
    release_origin_of_locked_vote config releases firstLocked
  obtain ⟨second, secondIn, secondSigner, secondSlot, secondJudgmentBound⟩ :=
    release_origin_of_locked_vote config releases secondLocked
  have sameSigner :
      (releasedVote first).signerQ =
        (releasedVote second).signerQ :=
    firstSigner.trans secondSigner.symm
  have sameSlot :
      decisionSlot (releasedVote first) =
        decisionSlot (releasedVote second) :=
    firstSlot.trans secondSlot.symm
  have continuity :=
    adapter.continuity.pairwise
      first firstIn second secondIn sameSigner
      (by
        simpa [quorumSystem, firstSigner] using signerMember)
      (fun firstFaulty => signerHonest (firstSigner ▸ firstFaulty))
      sameSlot
  have sameRound :
      (releasedVote first).round = (releasedVote second).round :=
    congrArg DecisionSlot.round sameSlot
  have sameJudgment :
      canonicalJudgment (releasedVote first) =
        canonicalJudgment (releasedVote second) :=
    same_round_continuity_canonical_judgment_equal continuity sameRound
  exact firstJudgmentBound.symm.trans
    (sameJudgment.trans secondJudgmentBound)

/--
Proposal-indexed authority evidence jointly carries the RCC-34 lawful act and
the exact RCC-40 QC used by this proposal.

All load-bearing coordinates are related to the sealed RCC-34 topology
context.  In particular, a QC is not authority by itself: it must be paired
with a lawful act whose signer set and pre-state config/epoch/policy
projections agree with the signed decision slot.
-/
structure EffectiveQuorumAuthorityEvidence
    {Q : Type u}
    (system : AuthoritySystem)
    (policy : AuthorityPolicy system)
    (topology : FiniteControlTopology system)
    (binding : EffectiveAuthorityBinding Q system)
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    (adapter :
      QuorumFinalityAdapter config scheme releases faultSet)
    (proposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)) where
  lawfulAct : LawfulAuthorityAct system policy topology
  qc :
    ValidQC
      (quorumSystem config) (releaseLocks config releases)
      proposal.slot proposal.judgment
  actBound : lawfulAct.act = binding.actFor proposal
  signerSetBound :
    ∀ signerQ,
      signerQ ∈ lawfulAct.signers.map binding.signerQ ↔
        signerQ ∈ qc.quorum
  configBound :
    proposal.slot.configQ = binding.configQ config
  epochBound :
    proposal.slot.epochQ = binding.contextEpochQ topology.context
  policyBound :
    proposal.slot.policyQ = binding.policyQ policy

/--
An independent canonical-linearizer snapshot.

The canonical head is fixed by this object, rather than selected from the
proposal.  `Receipt` is indexed by the exact proposal; its implementation is
owned by the RCC-42 realization.
-/
structure CanonicalLinearizer
    (Slot : Type u) (Head : Type v) (Judgment : Type w) where
  canonicalHead : Head
  Receipt : Proposal Slot Head Judgment → Head → Type x

/--
RCC-39 linearization evidence binds an independent receipt to both the exact
proposal and the externally fixed canonical head.
-/
structure CanonicalLinearizerEvidence
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    (linearizer : CanonicalLinearizer Slot Head Judgment)
    (proposal : Proposal Slot Head Judgment)
    (canonicalHead : Head) where
  receipt : linearizer.Receipt proposal canonicalHead
  canonicalHeadBound : canonicalHead = linearizer.canonicalHead

/--
A quorum finality certificate contains the complete RCC-34/RCC-40 authority
evidence and an independent canonical-linearizer receipt.  The canonical head
is the one fixed by `linearizer`, never `proposal.expectedParent` by
definition.
-/
structure QuorumFinalityCert
    {Q : Type u}
    (system : AuthoritySystem)
    (policy : AuthorityPolicy system)
    (topology : FiniteControlTopology system)
    (binding : EffectiveAuthorityBinding Q system)
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    (adapter :
      QuorumFinalityAdapter config scheme releases faultSet)
    (linearizer :
      CanonicalLinearizer
        (DecisionSlot Q) Q (CanonicalJudgment Q))
    (proposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)) where
  finality :
    FinalityCert
      (DecisionSlot Q) Q (CanonicalJudgment Q)
      (EffectiveQuorumAuthorityEvidence
        system policy topology binding adapter)
      (CanonicalLinearizerEvidence linearizer)
      linearizer.canonicalHead
  proposalBound : finality.authorization.proposal = proposal

/--
Construct finality only from complete effective-quorum authority evidence, an
independent canonical-linearizer receipt, and a proof that the proposal
expected the externally fixed canonical head.
-/
def certifyAuthorizedQC
    {Q : Type u}
    {system : AuthoritySystem}
    {policy : AuthorityPolicy system}
    {topology : FiniteControlTopology system}
    {binding : EffectiveAuthorityBinding Q system}
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    {adapter :
      QuorumFinalityAdapter config scheme releases faultSet}
    {linearizer :
      CanonicalLinearizer
        (DecisionSlot Q) Q (CanonicalJudgment Q)}
    {proposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)}
    (authority :
      EffectiveQuorumAuthorityEvidence
        system policy topology binding adapter proposal)
    (linearization :
      linearizer.Receipt proposal linearizer.canonicalHead)
    (parentBound :
      proposal.expectedParent = linearizer.canonicalHead) :
    QuorumFinalityCert
      system policy topology binding adapter linearizer proposal where
  finality := {
    authorization := {
      proposal := proposal
      authorityEvidence := authority
    }
    linearizationEvidence := {
      receipt := linearization
      canonicalHeadBound := rfl
    }
    parentBound := parentBound
  }
  proposalBound := rfl

/-- Project the RCC-39 existential finality judgment from the concrete cert. -/
def quorum_finalized_with_receipts
    {Q : Type u}
    {system : AuthoritySystem}
    {policy : AuthorityPolicy system}
    {topology : FiniteControlTopology system}
    {binding : EffectiveAuthorityBinding Q system}
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    {adapter :
      QuorumFinalityAdapter config scheme releases faultSet}
    {linearizer :
      CanonicalLinearizer
        (DecisionSlot Q) Q (CanonicalJudgment Q)}
    {proposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)}
    (certificate :
      QuorumFinalityCert
        system policy topology binding adapter linearizer proposal) :
    FinalizedWithReceipts
      (DecisionSlot Q) Q (CanonicalJudgment Q)
      (EffectiveQuorumAuthorityEvidence
        system policy topology binding adapter)
      (CanonicalLinearizerEvidence linearizer)
      proposal linearizer.canonicalHead :=
  ⟨certificate.finality, certificate.proposalBound⟩

/-- RCC-39 finality retains the exact effective-quorum authorization. -/
theorem quorum_finality_implies_authorized
    {Q : Type u}
    {system : AuthoritySystem}
    {policy : AuthorityPolicy system}
    {topology : FiniteControlTopology system}
    {binding : EffectiveAuthorityBinding Q system}
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    {adapter :
      QuorumFinalityAdapter config scheme releases faultSet}
    {linearizer :
      CanonicalLinearizer
        (DecisionSlot Q) Q (CanonicalJudgment Q)}
    {proposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)}
    (certificate :
      QuorumFinalityCert
        system policy topology binding adapter linearizer proposal) :
    AuthorizedWithReceipt
      (DecisionSlot Q) Q (CanonicalJudgment Q)
      (EffectiveQuorumAuthorityEvidence
        system policy topology binding adapter)
      proposal :=
  finalized_implies_authorized
    (quorum_finalized_with_receipts certificate)

/--
Two same-slot quorum finalities have equal canonical `(proposal, verdict)`
judgments.  The proof consumes both RCC-40 quorum/fault laws and the RCC-41
continuity-derived non-equivocation bridge.
-/
theorem same_slot_quorum_finalities_judgment_equivalent
    {Q : Type u}
    {system : AuthoritySystem}
    {policy : AuthorityPolicy system}
    {topology : FiniteControlTopology system}
    {binding : EffectiveAuthorityBinding Q system}
    {config : QuorumConfiguration Q}
    {scheme : SignatureScheme Q}
    {releases : List (ReleasedSignature Q scheme)}
    {faultSet : List Q}
    {adapter :
      QuorumFinalityAdapter config scheme releases faultSet}
    {linearizer :
      CanonicalLinearizer
        (DecisionSlot Q) Q (CanonicalJudgment Q)}
    {firstProposal secondProposal :
      Proposal (DecisionSlot Q) Q (CanonicalJudgment Q)}
    (first :
      QuorumFinalityCert
        system policy topology binding adapter linearizer firstProposal)
    (second :
      QuorumFinalityCert
        system policy topology binding adapter linearizer secondProposal)
    (sameSlot : firstProposal.slot = secondProposal.slot) :
    firstProposal.judgment = secondProposal.judgment := by
  have firstQC :
      ValidQC
        (quorumSystem config) (releaseLocks config releases)
        firstProposal.slot firstProposal.judgment := by
    rw [← first.proposalBound]
    exact first.finality.authorization.authorityEvidence.qc
  have originalSecondQC :
      ValidQC
        (quorumSystem config) (releaseLocks config releases)
        secondProposal.slot secondProposal.judgment := by
    rw [← second.proposalBound]
    exact second.finality.authorization.authorityEvidence.qc
  have secondQC :
      ValidQC
        (quorumSystem config) (releaseLocks config releases)
        firstProposal.slot secondProposal.judgment := by
    rw [sameSlot]
    exact originalSecondQC
  exact
    valid_qcs_same_slot_equivalent
      (quorumSystem config)
      (releaseLocks config releases)
      adapter.intersectionSafe
      faultSet
      adapter.faultAllowed
      (honest_signer_continuity_implies_non_equivocation adapter)
      firstQC
      secondQC

end Residua.RCC.QuorumFinalityAdapter

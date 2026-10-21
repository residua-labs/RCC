import RCC.LongRangeSafety
import RCCTests.KeyEpochVote
import RCCTests.HistoricalInclusion

/-!
# RCC-54 Long-Range Safety Countermodels

The positive witness combines the actual RCC-52 key/config-epoch certificate
with the actual RCC-53 finalized-checkpoint inclusion.  Mutants cover:

* valid retired-key bytes claiming an incompatible item;
* a stale checkpoint/fork head;
* reuse of the retired runtime key as the active runtime key; and
* missing positive evidence, which can only Await.
-/

namespace Residua.RCC.LongRangeSafety.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.AuthorityReconfiguration
open Residua.RCC.DurableVoteLock
open Residua.RCC.DurableVoteLock.Tests
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.FinalizedHeadWindow.Tests
open Residua.RCC.HistoricalInclusion
open Residua.RCC.KeyEpochVote
open Residua.RCC.LongRangeSafety

/-- Explicit bridge from the RCC-53 domains to the signed RCC-52 payload. -/
def authorityAdapter :
    HistoricalAuthorityAdapter
      Token Token Slot Head Config Token Token where
  slotQ
    | .deploy => .slotA
  headQ
    | .genesis => .headA
    | .headA => .headA
    | .headB => .headB
  configQ
    | .v1 => .configA
    | .v2 => .configB
  coordinateKeyEpochQ := fun coordinate => coordinate
  itemJudgment := fun item =>
    if item = .proposalP then
      ⟨.proposalP, .verdictAccept⟩
    else
      ⟨item, .verdictReject⟩

def canonicalClaim :
    PresentedHistoricalClaim Token Slot Head Config Token Token where
  checkpointQ := .lockP
  slot := .deploy
  head := .headA
  config := .v1
  coordinate := .epochA
  item := .proposalP

def canonicalFacts :
    HistoricalAuthorityFacts
      Token Token Slot Head Config Token Token where
  activePayload :=
    releasedKeyEpochPayload
      Residua.RCC.DurableVoteLock.Tests.releaseP
  checkpointQ :=
    Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint.checkpointQ
  slot :=
    Residua.RCC.HistoricalInclusion.Tests.finalizedClosure.snapshot.slot
  head :=
    Residua.RCC.HistoricalInclusion.Tests.finalizedClosure.snapshot.head
  config :=
    Residua.RCC.HistoricalInclusion.Tests.finalizedClosure.snapshot.config
  coordinate := .epochA
  item := .proposalP

def canonicalBinding :
    ExactHistoricalAuthorityBinding
      authorityAdapter canonicalFacts canonicalClaim where
  checkpointBound := rfl
  slotBound := rfl
  headBound := rfl
  configBound := rfl
  coordinateBound := rfl
  itemBound := rfl
  activeSlotBound := rfl
  activeHeadBound := rfl
  activeConfigBound := rfl
  activeKeyEpochBound := rfl
  judgmentBound := rfl

theorem canonical_binding_is_mechanically_accepted :
    (match
        verifyHistoricalAuthorityBinding
          authorityAdapter canonicalFacts canonicalClaim with
      | .authority _ => true
      | .refuse _ => false) = true := by
  rfl

/-- The exact type of the proof-carrying positive authority fixture. -/
abbrev HistoricalAuthorityCertificate : Type :=
    ActualHistoricalAuthority
      (TransitionAuthorityEvidence :=
        Residua.RCC.KeyEpochVote.Tests.KeyAuthorityEvidence)
      (HistoryAuthorityEvidence :=
        Residua.RCC.FinalizedHeadWindow.Tests.AuthorityEvidence)
      (jointProtocol :=
        Residua.RCC.KeyEpochVote.Tests.keyJointProtocol)
      (spec := Residua.RCC.KeyEpochVote.Tests.keyWriterSpec)
      (equivalence :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentEquivalence)
      (transitionAdapter :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentAdapter)
      (state := Residua.RCC.KeyEpochVote.Tests.keyWriterState)
      (transition := Residua.RCC.KeyEpochVote.Tests.keyTransition)
      (envelope := Residua.RCC.KeyEpochVote.Tests.keyEnvelope)
      (activation := Residua.RCC.KeyEpochVote.Tests.newKeyActivation)
      (lawful := Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition)
      (registry := Residua.RCC.KeyEpochVote.Tests.keyRegistry)
      (scheme := exactVoteSignatureScheme)
      (activeRelease := Residua.RCC.DurableVoteLock.Tests.releaseP)
      (history := Residua.RCC.FinalizedHeadWindow.Tests.finalizedHistory)
      (environment :=
        Residua.RCC.FinalizedHeadWindow.Tests.admissionEnvironment)
      (ConfigLawful :=
        Residua.RCC.FinalizedHeadWindow.Tests.configLawful)
      (sourceProtocol :=
        Residua.RCC.FinalizedHeadWindow.Tests.sourceProtocol)
      (ConfigStable :=
        Residua.RCC.FinalizedHeadWindow.Tests.configStable)
      (closure :=
        Residua.RCC.HistoricalInclusion.Tests.finalizedClosure)
      Residua.RCC.HistoricalInclusion.Tests.checkpointProtocol
      Residua.RCC.HistoricalInclusion.Tests.HistoricalVoteEvidence
      Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint
      .epochA .proposalP authorityAdapter

/-- The positive object retains actual RCC-52 and RCC-53 certificates. -/
def historicalAuthority : HistoricalAuthorityCertificate where
  active := Residua.RCC.KeyEpochVote.Tests.releasePActive
  inclusion :=
    Residua.RCC.HistoricalInclusion.Tests.releasePInclusion
  claim := canonicalClaim
  binding := canonicalBinding

theorem accepted_history_consumes_actual_rcc52_and_rcc53 :
    Nonempty
        (KeyEpochVoteCertificate
          Residua.RCC.KeyEpochVote.Tests.newKeyActivation
          Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition
          Residua.RCC.KeyEpochVote.Tests.keyRegistry
          Residua.RCC.DurableVoteLock.Tests.releaseP) ∧
      Nonempty
          (FinalizedHistoricalInclusion
            Residua.RCC.HistoricalInclusion.Tests.checkpointProtocol
            Residua.RCC.HistoricalInclusion.Tests.HistoricalVoteEvidence
            Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint
            Token.epochA Token.proposalP) ∧
        Residua.RCC.HistoricalInclusion.Tests.checkpointProtocol.InCheckpoint
          Residua.RCC.HistoricalInclusion.Tests.sealedCheckpoint.checkpointQ
          .epochA .proposalP :=
  historical_authority_consumes_rcc52_and_rcc53 historicalAuthority

/-! ## Logical compromise window and actual retirement transition -/

inductive Window
  | sealed
  deriving DecidableEq, Repr

def retiredObserved
    (receipt oldConfig newConfig oldEpoch : Token)
    (time : Nat) : Prop :=
  receipt = .lockQ ∧
    oldConfig = .configB ∧
    newConfig = .configA ∧
    oldEpoch = .epochB ∧
    time = 10

def compromisedObserved
    (receipt : Token) (signature : Vote Token)
    (runtimeKey oldEpoch : Token) (time : Nat) (window : Window) : Prop :=
  receipt = .unlockCert ∧
    signature = Residua.RCC.KeyEpochVote.Tests.crossEpochVote ∧
    (runtimeKey = .keyOld ∨ runtimeKey = .keyNew) ∧
    oldEpoch = .epochB ∧
    time = 20 ∧
    window = .sealed

def compromiseProtocol :
    CompromiseWindowProtocol
      Token exactVoteSignatureScheme Nat Window where
  RetirementReceipt := Token
  CompromiseReceipt := Token
  RetiredAt := retiredObserved
  CompromisedAt := compromisedObserved
  Before := Nat.lt
  WithinWindow := fun time window =>
    time = 20 ∧ window = .sealed

/--
The retired release uses a physical key distinct from the active release, so
the item/fork mutants reach the intended later checks.
-/
def distinctRetiredRuntime : SignerRuntime Token where
  signerQ := .signerA
  keyQ := .keyNew
  processQ := .processTwo

def distinctRetiredRelease :
    ReleasedSignature Token exactVoteSignatureScheme where
  commit := Residua.RCC.KeyEpochVote.Tests.crossEpochCommit
  envelope := {
    signedVote := Residua.RCC.KeyEpochVote.Tests.crossEpochVote
    signatureQ := Residua.RCC.KeyEpochVote.Tests.crossEpochVote
  }
  validSignature := ⟨rfl⟩
  signatureBindsLock := rfl
  runtime := distinctRetiredRuntime
  runtimeSigner := rfl
  releasedAt := 1
  lockBeforeRelease := by decide

def distinctRetiredCertificate :
    RetiredKeyEpochCertificate
      Residua.RCC.KeyEpochVote.Tests.newKeyActivation
      Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition
      distinctRetiredRelease where
  retiredEpochBound := rfl

def incompatibleClaim :
    PresentedHistoricalClaim Token Slot Head Config Token Token :=
  { canonicalClaim with item := .proposalQ }

def staleForkClaim :
    PresentedHistoricalClaim Token Slot Head Config Token Token :=
  { canonicalClaim with head := .headB }

def exactRetiredClaim :
    PresentedHistoricalClaim Token Slot Head Config Token Token :=
  canonicalClaim

def distinctIncompatibleAttempt :
    LaterRetiredKeyCompromise
      (TransitionAuthorityEvidence :=
        Residua.RCC.KeyEpochVote.Tests.KeyAuthorityEvidence)
      (jointProtocol :=
        Residua.RCC.KeyEpochVote.Tests.keyJointProtocol)
      (spec := Residua.RCC.KeyEpochVote.Tests.keyWriterSpec)
      (equivalence :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentEquivalence)
      (transitionAdapter :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentAdapter)
      (state := Residua.RCC.KeyEpochVote.Tests.keyWriterState)
      (transition := Residua.RCC.KeyEpochVote.Tests.keyTransition)
      (envelope := Residua.RCC.KeyEpochVote.Tests.keyEnvelope)
      (activation := Residua.RCC.KeyEpochVote.Tests.newKeyActivation)
      (lawful := Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition)
      (scheme := exactVoteSignatureScheme)
      (retiredRelease := distinctRetiredRelease)
      compromiseProtocol incompatibleClaim where
  retired := distinctRetiredCertificate
  retirementTime := 10
  compromiseTime := 20
  observationWindow := .sealed
  retirementReceipt := .lockQ
  retiredObserved := ⟨rfl, rfl, rfl, rfl, rfl⟩
  compromiseReceipt := .unlockCert
  compromisedObserved :=
    ⟨rfl, rfl, Or.inr rfl, rfl, rfl, rfl⟩
  laterThanRetirement := by
    change 10 < 20
    decide
  compromiseInWindow := ⟨rfl, rfl⟩

def distinctStaleAttempt :
    LaterRetiredKeyCompromise
      (TransitionAuthorityEvidence :=
        Residua.RCC.KeyEpochVote.Tests.KeyAuthorityEvidence)
      (jointProtocol :=
        Residua.RCC.KeyEpochVote.Tests.keyJointProtocol)
      (spec := Residua.RCC.KeyEpochVote.Tests.keyWriterSpec)
      (equivalence :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentEquivalence)
      (transitionAdapter :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentAdapter)
      (state := Residua.RCC.KeyEpochVote.Tests.keyWriterState)
      (transition := Residua.RCC.KeyEpochVote.Tests.keyTransition)
      (envelope := Residua.RCC.KeyEpochVote.Tests.keyEnvelope)
      (activation := Residua.RCC.KeyEpochVote.Tests.newKeyActivation)
      (lawful := Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition)
      (scheme := exactVoteSignatureScheme)
      (retiredRelease := distinctRetiredRelease)
      compromiseProtocol staleForkClaim where
  retired := distinctRetiredCertificate
  retirementTime := 10
  compromiseTime := 20
  observationWindow := .sealed
  retirementReceipt := .lockQ
  retiredObserved := ⟨rfl, rfl, rfl, rfl, rfl⟩
  compromiseReceipt := .unlockCert
  compromisedObserved :=
    ⟨rfl, rfl, Or.inr rfl, rfl, rfl, rfl⟩
  laterThanRetirement := by
    change 10 < 20
    decide
  compromiseInWindow := ⟨rfl, rfl⟩

def distinctExactAttempt :
    LaterRetiredKeyCompromise
      (TransitionAuthorityEvidence :=
        Residua.RCC.KeyEpochVote.Tests.KeyAuthorityEvidence)
      (jointProtocol :=
        Residua.RCC.KeyEpochVote.Tests.keyJointProtocol)
      (spec := Residua.RCC.KeyEpochVote.Tests.keyWriterSpec)
      (equivalence :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentEquivalence)
      (transitionAdapter :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentAdapter)
      (state := Residua.RCC.KeyEpochVote.Tests.keyWriterState)
      (transition := Residua.RCC.KeyEpochVote.Tests.keyTransition)
      (envelope := Residua.RCC.KeyEpochVote.Tests.keyEnvelope)
      (activation := Residua.RCC.KeyEpochVote.Tests.newKeyActivation)
      (lawful := Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition)
      (scheme := exactVoteSignatureScheme)
      (retiredRelease := distinctRetiredRelease)
      compromiseProtocol exactRetiredClaim where
  retired := distinctRetiredCertificate
  retirementTime := 10
  compromiseTime := 20
  observationWindow := .sealed
  retirementReceipt := .lockQ
  retiredObserved := ⟨rfl, rfl, rfl, rfl, rfl⟩
  compromiseReceipt := .unlockCert
  compromisedObserved :=
    ⟨rfl, rfl, Or.inr rfl, rfl, rfl, rfl⟩
  laterThanRetirement := by
    change 10 < 20
    decide
  compromiseInWindow := ⟨rfl, rfl⟩

def reusedKeyAttempt :
    LaterRetiredKeyCompromise
      (TransitionAuthorityEvidence :=
        Residua.RCC.KeyEpochVote.Tests.KeyAuthorityEvidence)
      (jointProtocol :=
        Residua.RCC.KeyEpochVote.Tests.keyJointProtocol)
      (spec := Residua.RCC.KeyEpochVote.Tests.keyWriterSpec)
      (equivalence :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentEquivalence)
      (transitionAdapter :=
        Residua.RCC.KeyEpochVote.Tests.keyJudgmentAdapter)
      (state := Residua.RCC.KeyEpochVote.Tests.keyWriterState)
      (transition := Residua.RCC.KeyEpochVote.Tests.keyTransition)
      (envelope := Residua.RCC.KeyEpochVote.Tests.keyEnvelope)
      (activation := Residua.RCC.KeyEpochVote.Tests.newKeyActivation)
      (lawful := Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition)
      (scheme := exactVoteSignatureScheme)
      (retiredRelease :=
        Residua.RCC.KeyEpochVote.Tests.crossEpochRelease)
      compromiseProtocol exactRetiredClaim where
  retired := Residua.RCC.KeyEpochVote.Tests.crossEpochRetired
  retirementTime := 10
  compromiseTime := 20
  observationWindow := .sealed
  retirementReceipt := .lockQ
  retiredObserved := ⟨rfl, rfl, rfl, rfl, rfl⟩
  compromiseReceipt := .unlockCert
  compromisedObserved :=
    ⟨rfl, rfl, Or.inl rfl, rfl, rfl, rfl⟩
  laterThanRetirement := by
    change 10 < 20
    decide
  compromiseInWindow := ⟨rfl, rfl⟩

/-! ## Load-bearing mutants -/

theorem valid_old_key_bytes_on_incompatible_item_are_refused :
    exactVoteSignatureScheme.Accepts
        distinctRetiredRelease.envelope.signatureQ
        (exactVoteSignatureScheme.canonicalVoteMessage
          distinctRetiredRelease.envelope.signedVote) ∧
      assessRetiredClaim authorityAdapter
        Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
        distinctRetiredRelease.runtime.keyQ
        canonicalClaim incompatibleClaim
        (releasedKeyEpochPayload distinctRetiredRelease).judgment
        distinctIncompatibleAttempt =
          RetiredClaimAssessment.refuse
            distinctIncompatibleAttempt .checkpointItemMismatch := by
  exact ⟨distinctRetiredRelease.validSignature.accepted, rfl⟩

theorem stale_checkpoint_or_fork_is_refused :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      distinctRetiredRelease.runtime.keyQ
      canonicalClaim staleForkClaim
      (releasedKeyEpochPayload distinctRetiredRelease).judgment
      distinctStaleAttempt =
        RetiredClaimAssessment.refuse
          distinctStaleAttempt .staleCheckpointOrFork := by
  rfl

theorem retired_key_reused_as_active_is_refused :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      Residua.RCC.KeyEpochVote.Tests.crossEpochRelease.runtime.keyQ
      canonicalClaim exactRetiredClaim
      (releasedKeyEpochPayload
        Residua.RCC.KeyEpochVote.Tests.crossEpochRelease).judgment
      reusedKeyAttempt =
        RetiredClaimAssessment.refuse
          reusedKeyAttempt .retiredKeyReusedAsActive := by
  rfl

theorem missing_historical_authority_only_awaits :
    assessLongRangeAuthority
      (none : Option HistoricalAuthorityCertificate) =
        (LongRangeAuthorityAssessment.await
          .activeAuthorityEvidencePending :
          LongRangeAuthorityAssessment HistoricalAuthorityCertificate) := by
  rfl

theorem actual_authority_remains_canonical :
    assessLongRangeAuthority (some historicalAuthority) =
      LongRangeAuthorityAssessment.authority historicalAuthority := by
  rfl

theorem later_compromise_bytes_remain_cryptographically_valid :
    exactVoteSignatureScheme.Accepts
      distinctRetiredRelease.envelope.signatureQ
      (exactVoteSignatureScheme.canonicalVoteMessage
        distinctRetiredRelease.envelope.signedVote) :=
  later_compromise_signature_remains_cryptographically_valid
    distinctIncompatibleAttempt

/--
Even a perfectly matching retired claim is still only a refused retired
signature; the actual RCC-53 inclusion remains the sole authority object.
-/
theorem retired_bytes_never_gain_canonical_history_authority :
    assessRetiredClaim authorityAdapter
      Residua.RCC.DurableVoteLock.Tests.releaseP.runtime.keyQ
      distinctRetiredRelease.runtime.keyQ
      canonicalClaim canonicalClaim
      (releasedKeyEpochPayload distinctRetiredRelease).judgment
      distinctExactAttempt =
        RetiredClaimAssessment.refuse
          distinctExactAttempt
          .retiredSignatureHasNoHistoryAuthority := by
  rfl

theorem retired_release_cannot_become_active
    (active :
      KeyEpochVoteCertificate
        Residua.RCC.KeyEpochVote.Tests.newKeyActivation
        Residua.RCC.KeyEpochVote.Tests.lawfulKeyTransition
        Residua.RCC.KeyEpochVote.Tests.keyRegistry
        distinctRetiredRelease) :
    False :=
  retired_release_cannot_gain_active_history_authority
    distinctIncompatibleAttempt active

#print axioms historical_authority_consumes_rcc52_and_rcc53
#print axioms later_compromise_signature_remains_cryptographically_valid
#print axioms retired_release_cannot_gain_active_history_authority
#print axioms valid_old_key_bytes_on_incompatible_item_are_refused
#print axioms stale_checkpoint_or_fork_is_refused
#print axioms retired_key_reused_as_active_is_refused
#print axioms missing_historical_authority_only_awaits
#print axioms retired_bytes_never_gain_canonical_history_authority

end Residua.RCC.LongRangeSafety.Tests

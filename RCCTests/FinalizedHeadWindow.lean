import RCC.FinalizedHeadWindow

/-!
# RCC-45 Finalized Head and Window Countermodels

Only a concrete RCC-42/RCC-31/durable-history admission plus an
authority-sealed complete window can make a closure candidate eligible.
Partition-local consistency is never global closure authority.
-/

namespace Residua.RCC.FinalizedHeadWindow.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.EffectSettlement
open Residua.RCC.FinalizedHeadWindow

inductive Slot
  | deploy
  deriving DecidableEq

inductive Head
  | genesis
  | headA
  | headB
  deriving DecidableEq

inductive Judgment
  | commitA
  | commitB
  deriving DecidableEq

inductive Config
  | v1
  | v2
  deriving DecidableEq

inductive Generation
  | current
  deriving DecidableEq

inductive Epoch
  | current
  deriving DecidableEq

inductive EffectSlot
  | store
  deriving DecidableEq

inductive Occurrence
  | deployment
  deriving DecidableEq

inductive FailureName
  | receiverRejected
  deriving DecidableEq

inductive EventQ
  | activationRecorded
  deriving DecidableEq

inductive SourceAuthority
  | origin
  deriving DecidableEq

inductive Watermark
  | ten
  | eleven
  deriving DecidableEq

inductive Partition
  | zero
  | one
  deriving DecidableEq

inductive WatermarkReceipt
  | full
  deriving DecidableEq

def proposalA : Proposal Slot Head Judgment :=
  ⟨.deploy, .genesis, .commitA⟩

/--
Only the exact proposal admitted by this fixture has authority evidence.
There is no context-free token that can be spliced into another proposal.
-/
inductive AuthorityEvidence : Proposal Slot Head Judgment → Type
  | quorumA : AuthorityEvidence proposalA

def authorizationA :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence :=
  ⟨proposalA, .quorumA⟩

def writerSpec : FencedWriterSpec Slot Head where
  slotParent := fun _ => .genesis

def judgmentEq : JudgmentEquivalence Judgment where
  Equivalent := Eq
  refl := by intro _; rfl
  symm := by intro _ _ equality; exact equality.symm
  trans := by intro _ _ _ first second; exact first.trans second
  decide := fun first second => inferInstanceAs (Decidable (first = second))

def writerState :
    FencedWriterState Slot Head Judgment Generation where
  generation := .current
  canonicalHead := .genesis
  decisions := fun _ => some .commitA

def finalizeRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation :=
  ⟨authorizationA, .current⟩

def finalizeOutput :
    FencedFinalizeOutput writerSpec judgmentEq writerState finalizeRequest where
  finality := {
    authorization := authorizationA
    linearizationEvidence := {
      generation := .current
      slot := .deploy
      parentHead := .genesis
      slotBound := rfl
      parentHeadBound := rfl
    }
    parentBound := rfl
  }
  authorizationBound := rfl
  generationBound := rfl
  finalized := ⟨rfl, rfl, .commitA, rfl, rfl⟩

def finalizeSuccess :
    SuccessfulFinalize writerSpec judgmentEq writerState finalizeRequest where
  output := finalizeOutput
  accepted := by rfl

def deploymentEffect : ExternalEffect Occurrence Head EffectSlot where
  occurrence := .deployment
  expectedParent := .genesis
  effectSlot := .store

def deploymentReceipt :
    EffectReceipt
      Epoch Head EffectSlot Generation Occurrence FailureName where
  occurrence := .deployment
  fence := {
    epoch := .current
    head := .genesis
    effectSlot := .store
    generation := .current
  }
  phase := .recorded

def settledObservation :
    EffectObservation
      Epoch Head EffectSlot Generation Occurrence FailureName where
  worldApplied := true
  historyRecorded := true
  compensationApplied := false
  receipt := some deploymentReceipt

def effectSnapshot :
    EffectSnapshot
      Epoch Head EffectSlot Generation Occurrence FailureName where
  epoch := .current
  head := .genesis
  currentGeneration := fun _ => .current
  policyTerminalFailure := fun _ => False
  externalEffects := [deploymentEffect]
  observe := fun _ => some settledObservation

def historyEventView :
    HistoryEventView EventQ Slot Head Judgment Occurrence where
  preHead := fun _ => .genesis
  slot := fun _ => .deploy
  judgment := fun _ => .commitA
  occurrence := fun _ => .deployment

def canonicalHistory : CanonicalHistorySnapshot EventQ Head where
  canonicalHead := .genesis
  contains := fun _ => true
  durableContains := fun _ => True
  containsSound := by intro _ _; trivial

def admissionEnvironment :
    AdmissionEnvironment
      Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot Occurrence
        FailureName EventQ where
  writerSpec := writerSpec
  equivalence := judgmentEq
  writerState := writerState
  effectSnapshot := effectSnapshot
  historyView := historyEventView
  historySnapshot := canonicalHistory
  occurrenceOf := fun _ => .deployment
  effectSlotOf := fun _ => .store
  effectHeadBound := rfl
  historyHeadBound := rfl
  generationCoherent := by intro _; rfl

def admissionA : SettledAdmission admissionEnvironment proposalA where
  finalizeRequest := finalizeRequest
  proposalBound := rfl
  finalizeSuccess := finalizeSuccess
  effect := deploymentEffect
  effectDeclared := by simp [admissionEnvironment, effectSnapshot]
  effectOccurrenceBound := rfl
  effectParentBound := rfl
  effectSlotBound := rfl
  effectObservation := settledObservation
  effectReceipt := deploymentReceipt
  settled := {
    observed := rfl
    receiptPresent := rfl
    epochBound := rfl
    expectedParentBound := rfl
    canonicalHeadBound := rfl
    slotBound := rfl
    generationBound := rfl
    occurrenceBound := rfl
    coherent := by
      simp [SettlementCoherent, settledObservation, deploymentReceipt]
  }
  history := {
    event := .activationRecorded
    recorded := rfl
    durablyRecorded := True.intro
    canonicalHeadBound := rfl
    preHeadBound := rfl
    slotBound := rfl
    judgmentBound := rfl
    occurrenceBound := rfl
  }

def finalizedHistory : FinalizedHistoryView EventQ Slot Head Config where
  slot := fun _ => .deploy
  successorHead := fun _ => .headA
  config := fun _ => .v1
  finalized := fun _ => True
  sameSlotUnique := by
    intro first second _ _ _
    cases first
    cases second
    exact ⟨rfl, rfl⟩

def configLawful (config : Config) : Prop :=
  config = .v1

def headCertificate :
    FinalizedHeadCert
      admissionEnvironment finalizedHistory configLawful .v1 .genesis
        proposalA where
  admission := admissionA
  head := .headA
  configLawful := rfl
  parentBound := rfl
  historyFinalized := True.intro
  historySlotBound := rfl
  historyHeadBound := rfl
  historyConfigBound := rfl

def headEnvelope :
    FinalizedHeadEnvelope
      admissionEnvironment finalizedHistory configLawful where
  config := .v1
  parent := .genesis
  proposal := proposalA
  certificate := headCertificate

def sourceProtocol :
    SourceWindowProtocol
      SourceAuthority Watermark Partition Head Config where
  InUniverse := fun partition =>
    partition = .zero ∨ partition = .one
  Confirmation := WatermarkReceipt
  confirms receipt authority head config watermark partitions :=
    receipt = .full ∧
      authority = .origin ∧
      head = .headA ∧
      config = .v1 ∧
      watermark = .ten ∧
      partitions = [.zero, .one]

def fullCoverage :
    CoverageCertificate sourceProtocol.InUniverse [.zero, .one] where
  sound := by
    intro partition _
    cases partition <;> simp [sourceProtocol]
  complete := by
    intro partition _
    cases partition <;> simp

def configStable (config : Config) : Prop :=
  config = .v1

def fullSeal :
    FinalizedWindowSeal sourceProtocol configStable .v1 .headA
      [.zero, .one] where
  watermark := .ten
  sourceAuthority := .origin
  confirmation := .full
  authorityConfirmed := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  coverage := fullCoverage
  includedPartitions := [.zero, .one]
  allPriorPartitionsIncluded := rfl
  configStable := rfl

def fullSealEnvelope :
    FinalizedWindowEnvelope sourceProtocol configStable where
  config := .v1
  head := .headA
  watermark := .ten
  sourceAuthority := .origin
  priorPartitions := [.zero, .one]
  windowSeal := fullSeal
  watermarkBound := rfl
  sourceAuthorityBound := rfl

/-- The transition identity exported by the future RCC-44 adapter. -/
inductive ConfigTransition
  | upgradeToV2
  deriving DecidableEq

/--
The current admitted transition view contains the declared upgrade coordinate,
but it is not pending at the finalized v1/headA snapshot.
-/
def stableTransitionView :
    ConfigTransitionView Slot Head Config where
  Transition := ConfigTransition
  InUniverse := fun transition => transition = .upgradeToV2
  pendingAt := fun _ _ _ _ => False

def stableTransitionCoverage :
    CoverageCertificate
      stableTransitionView.InUniverse [.upgradeToV2] where
  sound := by
    intro transition _
    cases transition
    rfl
  complete := by
    intro transition _
    cases transition
    simp

def stableConfigEvidenceAt
    (slot : Slot) (head : Head) (config : Config) :
    StableConfigEvidence
      stableTransitionView slot head config where
  transitions := [.upgradeToV2]
  coverage := stableTransitionCoverage
  noPending := by
    intro _ _ pending
    exact pending

def stableConfigEvidence :
    StableConfigEvidence
      stableTransitionView .deploy .headA .v1 :=
  stableConfigEvidenceAt .deploy .headA .v1

def currentSnapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition where
  slot := .deploy
  parent := .genesis
  head := .headA
  config := .v1
  sourceAuthority := .origin
  watermark := .ten
  priorPartitions := [.zero, .one]
  transitionView := stableTransitionView

abbrev TestHeadEnvelope :=
  FinalizedHeadEnvelope admissionEnvironment finalizedHistory configLawful

abbrev FullWindowEnvelope :=
  FinalizedWindowEnvelope sourceProtocol configStable

def assessFull
    (snapshot :
      ClosureSnapshot
        Slot Config Head SourceAuthority Watermark Partition)
    (head? : Option TestHeadEnvelope)
    (window? : Option FullWindowEnvelope)
    (stable? :
      Option
        (StableConfigEvidence
          snapshot.transitionView snapshot.slot snapshot.head
            snapshot.config)) :=
  assessFinalizedClosure snapshot head? window? stable?

theorem finalized_head_consumes_rcc42_history :
    headCertificate.admission = admissionA := by
  rfl

theorem finalized_head_and_window_are_eligible :
    (match assessFull currentSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .eligible _ => true
      | .await _ => false) = true := by
  rfl

structure LocalPartitionView where
  partition : Partition
  localHead : Head
  localGreen : Bool

def localA : LocalPartitionView :=
  ⟨.zero, .headA, true⟩

def localB : LocalPartitionView :=
  ⟨.one, .headB, true⟩

/--
Two partitions can each be locally consistent while disagreeing globally.
Without a concrete finalized-history certificate, both local GREENs await.
-/
theorem two_local_greens_global_fork_awaits :
    localA.localGreen = true ∧ localB.localGreen = true ∧
      localA.localHead ≠ localB.localHead ∧
      (match assessFull currentSnapshot none none none with
        | .await .sourceWindowNotFinalized => true
        | _ => false) = true := by
  exact ⟨rfl, rfl, Head.noConfusion, rfl⟩

def omittedPartitionSnapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition :=
  { currentSnapshot with priorPartitions := [.zero] }

theorem window_omitting_partition_awaits :
    (match assessFull omittedPartitionSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true := by
  rfl

/--
CM-RCC45-05: even when both a caller snapshot and an included list omit the
same partition, a complete enumeration of the authority-declared universe
cannot be forged.
-/
theorem same_omitted_partition_has_no_coverage :
    ¬ Nonempty
      (CoverageCertificate sourceProtocol.InUniverse [.zero]) := by
  rintro ⟨coverage⟩
  have oneCovered :=
    coverage.complete .one (Or.inr rfl)
  simp at oneCovered

def staleHeadSnapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition :=
  { currentSnapshot with head := .headB }

theorem window_bound_to_stale_head_awaits :
    (match assessFull staleHeadSnapshot (some headEnvelope)
        (some fullSealEnvelope)
        (some (stableConfigEvidenceAt .deploy .headB .v1)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true := by
  rfl

def staleWatermarkSnapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition :=
  { currentSnapshot with watermark := .eleven }

theorem stale_watermark_awaits :
    (match assessFull staleWatermarkSnapshot (some headEnvelope)
        (some fullSealEnvelope) (some stableConfigEvidence) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true := by
  rfl

/--
CM-RCC45-CONFIG-PENDING: the authoritative transition universe contains an
actual pending transition at the exact finalized coordinate.
-/
def pendingTransitionView :
    ConfigTransitionView Slot Head Config where
  Transition := ConfigTransition
  InUniverse := fun transition => transition = .upgradeToV2
  pendingAt := fun transition slot head config =>
    transition = .upgradeToV2 ∧
      slot = .deploy ∧ head = .headA ∧ config = .v1

theorem actual_pending_transition_excludes_stable_evidence :
    ¬ Nonempty
      (StableConfigEvidence
        pendingTransitionView .deploy .headA .v1) :=
  pendingTransition_excludesStability
    (view := pendingTransitionView)
    .upgradeToV2 rfl ⟨rfl, rfl, rfl, rfl⟩

def pendingTransitionSnapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition :=
  { currentSnapshot with transitionView := pendingTransitionView }

theorem actual_pending_transition_cannot_be_hidden :
    (match assessFinalizedClosure
        pendingTransitionSnapshot (some headEnvelope) (some fullSealEnvelope)
        (none :
          Option
            (StableConfigEvidence
              pendingTransitionSnapshot.transitionView
                pendingTransitionSnapshot.slot pendingTransitionSnapshot.head
                pendingTransitionSnapshot.config)) with
      | .await .sourceWindowNotFinalized => true
      | _ => false) = true := by
  rfl

theorem lawful_finalized_heads_do_not_conflict
    (other :
      FinalizedHeadCert
        admissionEnvironment finalizedHistory configLawful .v1 .genesis
          proposalA) :
    headCertificate.head = other.head ∧
      Config.v1 = Config.v1 ∧
      admissionEnvironment.equivalence.Equivalent
        proposalA.judgment proposalA.judgment :=
  finalizedHead_unique headCertificate other rfl

/--
CM-RCC45-CONFIG-FORK: two finalized certificates in one durable history and
slot cannot certify the same successor under distinct authority configs.
-/
theorem same_finalized_slot_distinct_configs_cannot_both_certify
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {leftProposal rightProposal : Proposal Slot Head Judgment}
    (left :
      FinalizedHeadCert
        admissionEnvironment history (fun _ => True) .v1 .genesis leftProposal)
    (right :
      FinalizedHeadCert
        admissionEnvironment history (fun _ => True) .v2 .genesis rightProposal)
    (sameSlot : leftProposal.slot = rightProposal.slot) :
    False := by
  have configUnique :
      Config.v1 = Config.v2 :=
    (finalizedHead_unique left right sameSlot).2.1
  exact Config.noConfusion configUnique

#print axioms finalized_head_consumes_rcc42_history
#print axioms finalized_head_and_window_are_eligible
#print axioms two_local_greens_global_fork_awaits
#print axioms window_omitting_partition_awaits
#print axioms same_omitted_partition_has_no_coverage
#print axioms window_bound_to_stale_head_awaits
#print axioms stale_watermark_awaits
#print axioms actual_pending_transition_excludes_stable_evidence
#print axioms actual_pending_transition_cannot_be_hidden
#print axioms lawful_finalized_heads_do_not_conflict
#print axioms same_finalized_slot_distinct_configs_cannot_both_certify

end Residua.RCC.FinalizedHeadWindow.Tests

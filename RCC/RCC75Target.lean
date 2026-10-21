import RCCTests.AdmissionLinearizer

/-! RCC-75 candidate: admission linearization and settled-history finality. -/

namespace Residua.RCC.RCC75Target

universe uSlot uHead uJudgment uAuthority uGeneration uVersion uSettlement

open Residua.RCC.AdmissionLinearizer.Tests
open Residua.RCC.AdmissionLinearizer.RealizationTests
open Residua.RCC.AdmissionLinearizer.SettlementBridgeTests
open Residua.RCC.AdmissionLinearizer
open Residua.RCC.AuthorizationFinality
open Residua.RCC.EffectSettlement

abbrev SingletonLogClaim : Prop :=
  ∀ {j₁ j₂ : Residua.RCC.AdmissionLinearizer.Tests.Judgment}
    (first : FinalizedByLog singletonLog .deploy j₁)
    (second : FinalizedByLog singletonLog .deploy j₂),
    j₁ = j₂

def singletonLogUnique : SingletonLogClaim :=
  @singleton_log_finality_is_single_valued
def conflictingLogRefused := conflicting_log_is_not_consistent
def emptyWriterAwaits := empty_writer_waits
def committedWriterFinalizes := committed_writer_finalizes
def conflictingJudgmentRefused := conflicting_judgment_is_refused
def staleParentRefused := stale_parent_is_refused
def staleGenerationRefused := stale_generation_is_refused
def localForkCountermodel := conflicting_independent_snapshots_both_finalize_locally
def globalInterfaceFinalizes := global_interface_finalizes
def distinctSnapshotsSingleValued := distinct_canonical_snapshots_are_single_valued
def atMostOneFinalized := admission_linearizer_at_most_one_finalized
def globalConflictRefused := @conflicting_local_successes_cannot_both_be_globally_certified
def canonicalGenerationSingleValued := @canonical_snapshot_generation_is_single_valued
abbrev CompleteAdmissionSingleValuedClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ : Type uSettlement}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type uSettlement}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {first second : Proposal Slot Head Judgment}
    (firstAdmitted : SettledAdmission environment first)
    (secondAdmitted : SettledAdmission environment second)
    (sameSlot : first.slot = second.slot),
    environment.equivalence.Equivalent first.judgment second.judgment

def completeAdmissionSingleValued : CompleteAdmissionSingleValuedClaim := by
  intro Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
    AuthorityEvidence instHead instGeneration environment first second
    firstAdmitted secondAdmitted sameSlot
  exact settled_admissions_same_slot_equivalent
    firstAdmitted secondAdmitted sameSlot
def unauthorizedRefused := @authorized_only_cannot_admit
def unsettledRefused := @finalized_unsettled_cannot_admit
def settledUnrecordedRefused := @settled_unrecorded_cannot_admit

abbrev SettledAdmissionTerminalClaim : Prop :=
  ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {proposal : Proposal Slot Head Judgment}
    (admission : SettledAdmission environment proposal),
      EffectPhase.IsTerminal
        environment.effectSnapshot.policyTerminalFailure
        admission.effectReceipt.phase ∧
      environment.historySnapshot.contains
        admission.history.event = true

def settledAdmissionTerminal : SettledAdmissionTerminalClaim := by
  intro Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
    AuthorityEvidence instHead instGeneration environment proposal admission
  exact settled_admission_is_terminal_and_recorded admission

abbrev SingletonLogUniqueClaim : Prop :=
  ∀ {j₁ j₂ : Residua.RCC.AdmissionLinearizer.Tests.Judgment}
    (first : FinalizedByLog singletonLog .deploy j₁)
    (second : FinalizedByLog singletonLog .deploy j₂),
    j₁ = j₂

abbrev DistinctSnapshotsSingleValuedClaim : Prop :=
  ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type uAuthority}
    {Generation : Type uGeneration} {Version : Type uVersion}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer Slot Head Judgment Generation Version
        writerSpec equivalence)
    {firstVersion secondVersion : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest Slot Head Judgment AuthorityEvidence Generation}
    (first : GloballySuccessfulFinalize
      linearizer firstVersion firstState firstRequest)
    (second : GloballySuccessfulFinalize
      linearizer secondVersion secondState secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot)
    (sameParent :
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent),
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment

abbrev AtMostOneFinalizedClaim : Prop :=
  ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type uAuthority}
    {Generation : Type uGeneration} {Version : Type uVersion}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer Slot Head Judgment Generation Version
        writerSpec equivalence)
    {firstVersion secondVersion : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest Slot Head Judgment AuthorityEvidence Generation}
    (first : GloballySuccessfulFinalize
      linearizer firstVersion firstState firstRequest)
    (second : GloballySuccessfulFinalize
      linearizer secondVersion secondState secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot)
    (sameGeneration : firstState.generation = secondState.generation)
    (sameParent :
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent),
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment

abbrev CanonicalGenerationClaim : Prop :=
  ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
    {Generation : Type uGeneration} {Version : Type uVersion}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      AdmissionLinearizer Slot Head Judgment Generation Version
        writerSpec equivalence}
    {version : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    (first : CanonicalWriterSnapshot linearizer version firstState)
    (second : CanonicalWriterSnapshot linearizer version secondState)
    (sameHead : firstState.canonicalHead = secondState.canonicalHead),
    firstState.generation = secondState.generation

structure Certificate where
  singletonLogUnique : SingletonLogUniqueClaim
  conflictingLogRefused : ¬ ConsistentLog conflictingLog
  conflictingJudgmentRefused :
    fencedFinalize writerSpec judgmentEq
        Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState
        ⟨rollbackAuthorization, .current⟩ =
      .Refuse .conflictingJudgment
  staleParentRefused :
    fencedFinalize writerSpec judgmentEq
        Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState
        ⟨staleAuthorization, .current⟩ =
      .Refuse .staleParent
  staleGenerationRefused :
    fencedFinalize writerSpec judgmentEq currentGenerationState
        ⟨activateAuthorization, .stale⟩ =
      .Refuse .staleGeneration
  completeAdmissionSingleValued :
    ∀ {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ : Type uSettlement}
      {AuthorityEvidence : Proposal Slot Head Judgment → Type uSettlement}
      [DecidableEq Head] [DecidableEq Generation]
      {environment :
        AdmissionEnvironment
          Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
            Occurrence FailureName EventQ}
      {first second : Proposal Slot Head Judgment}
      (firstAdmitted : SettledAdmission environment first)
      (secondAdmitted : SettledAdmission environment second)
      (sameSlot : first.slot = second.slot),
      environment.equivalence.Equivalent first.judgment second.judgment
  unauthorizedRefused :
    ¬ Nonempty
      (SettledAdmission authorizedOnlyEnvironment activateProposal)
  unsettledRefused :
    ¬ Nonempty
      (SettledAdmission unsettledEnvironment activateProposal)
  emptyWriterAwaits :
    fencedFinalize writerSpec judgmentEq emptyState
        activateRequest =
      .Await .decisionCommitPending
  committedWriterFinalizes :
    ∃ output,
      fencedFinalize writerSpec judgmentEq
          Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState
          activateRequest =
        .Ok output
  localForkCountermodel :
    fencedFinalize writerSpec judgmentEq
        Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState
        activateRequest =
        .Ok activateFinalizeOutput ∧
      fencedFinalize writerSpec judgmentEq rollbackState rollbackRequest =
        .Ok rollbackFinalizeOutput
  globalInterfaceFinalizes :
    globalLinearizer.finalize
        0 Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState
          (activatedCanonicalSnapshot 0) activateRequest =
      .Ok (globallyActivated 0)
  distinctSnapshotsSingleValued :
    ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
      {AuthorityEvidence : Proposal Slot Head Judgment → Type uAuthority}
      {Generation : Type uGeneration} {Version : Type uVersion}
      {writerSpec : FencedWriterSpec Slot Head}
      {equivalence : JudgmentEquivalence Judgment}
      [DecidableEq Head] [DecidableEq Generation]
      (linearizer :
        AdmissionLinearizer Slot Head Judgment Generation Version
          writerSpec equivalence)
      {firstVersion secondVersion : Version}
      {firstState secondState :
        FencedWriterState Slot Head Judgment Generation}
      {firstRequest secondRequest :
        FencedFinalizeRequest Slot Head Judgment AuthorityEvidence Generation}
      (first : GloballySuccessfulFinalize
        linearizer firstVersion firstState firstRequest)
      (second : GloballySuccessfulFinalize
        linearizer secondVersion secondState secondRequest)
      (sameSlot :
        firstRequest.authorization.proposal.slot =
          secondRequest.authorization.proposal.slot)
      (sameParent :
        firstRequest.authorization.proposal.expectedParent =
          secondRequest.authorization.proposal.expectedParent),
      equivalence.Equivalent
        firstRequest.authorization.proposal.judgment
        secondRequest.authorization.proposal.judgment
  atMostOneFinalized :
    ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
      {AuthorityEvidence : Proposal Slot Head Judgment → Type uAuthority}
      {Generation : Type uGeneration} {Version : Type uVersion}
      {writerSpec : FencedWriterSpec Slot Head}
      {equivalence : JudgmentEquivalence Judgment}
      [DecidableEq Head] [DecidableEq Generation]
      (linearizer :
        AdmissionLinearizer Slot Head Judgment Generation Version
          writerSpec equivalence)
      {firstVersion secondVersion : Version}
      {firstState secondState :
        FencedWriterState Slot Head Judgment Generation}
      {firstRequest secondRequest :
        FencedFinalizeRequest Slot Head Judgment AuthorityEvidence Generation}
      (first : GloballySuccessfulFinalize
        linearizer firstVersion firstState firstRequest)
      (second : GloballySuccessfulFinalize
        linearizer secondVersion secondState secondRequest)
      (sameSlot :
        firstRequest.authorization.proposal.slot =
          secondRequest.authorization.proposal.slot)
      (sameGeneration : firstState.generation = secondState.generation)
      (sameParent :
        firstRequest.authorization.proposal.expectedParent =
          secondRequest.authorization.proposal.expectedParent),
      equivalence.Equivalent
        firstRequest.authorization.proposal.judgment
        secondRequest.authorization.proposal.judgment
  globalConflictRefused :
    ∀ (linearizer :
      AdmissionLinearizer
        Residua.RCC.AdmissionLinearizer.RealizationTests.Slot
        Residua.RCC.AdmissionLinearizer.RealizationTests.Head
        Residua.RCC.AdmissionLinearizer.RealizationTests.Judgment
        Residua.RCC.AdmissionLinearizer.RealizationTests.Generation
        Nat
        Residua.RCC.AdmissionLinearizer.RealizationTests.writerSpec
        Residua.RCC.AdmissionLinearizer.RealizationTests.judgmentEq)
      (firstVersion secondVersion : Nat)
      (activateCanonical :
        CanonicalWriterSnapshot linearizer firstVersion
          Residua.RCC.AdmissionLinearizer.RealizationTests.activatedState)
      (rollbackCanonical :
        CanonicalWriterSnapshot linearizer secondVersion
          Residua.RCC.AdmissionLinearizer.RealizationTests.rollbackState),
      False
  canonicalGenerationSingleValued :
    ∀ {Slot : Type uSlot} {Head : Type uHead} {Judgment : Type uJudgment}
      {Generation : Type uGeneration} {Version : Type uVersion}
      {writerSpec : FencedWriterSpec Slot Head}
      {equivalence : JudgmentEquivalence Judgment}
      {linearizer :
        AdmissionLinearizer Slot Head Judgment Generation Version
          writerSpec equivalence}
      {version : Version}
      {firstState secondState :
        FencedWriterState Slot Head Judgment Generation}
      (first : CanonicalWriterSnapshot linearizer version firstState)
      (second : CanonicalWriterSnapshot linearizer version secondState)
      (sameHead : firstState.canonicalHead = secondState.canonicalHead),
      firstState.generation = secondState.generation
  settledUnrecordedRefused :
    ¬ Nonempty
      (SettledAdmission unrecordedEnvironment activateProposal)
  settledAdmissionTerminal : SettledAdmissionTerminalClaim

def certificate : Certificate where
  singletonLogUnique := singleton_log_finality_is_single_valued
  conflictingLogRefused := conflicting_log_is_not_consistent
  conflictingJudgmentRefused := conflicting_judgment_is_refused
  staleParentRefused := stale_parent_is_refused
  staleGenerationRefused := stale_generation_is_refused
  completeAdmissionSingleValued := by
    intro Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      AuthorityEvidence instHead instGeneration environment first second
      firstAdmitted secondAdmitted sameSlot
    exact settled_admissions_same_slot_equivalent
      firstAdmitted secondAdmitted sameSlot
  unauthorizedRefused := authorized_only_cannot_admit
  unsettledRefused := finalized_unsettled_cannot_admit
  emptyWriterAwaits := emptyWriterAwaits
  committedWriterFinalizes := committedWriterFinalizes
  localForkCountermodel := localForkCountermodel
  globalInterfaceFinalizes := globalInterfaceFinalizes
  distinctSnapshotsSingleValued := global_finalizes_same_slot_parent_equivalent
  atMostOneFinalized := AdmissionLinearizer.atMostOneFinalized
  globalConflictRefused := globalConflictRefused
  canonicalGenerationSingleValued := canonical_snapshots_no_generation_overlap
  settledUnrecordedRefused := settledUnrecordedRefused
  settledAdmissionTerminal := settledAdmissionTerminal

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC75Target

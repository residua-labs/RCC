import RCC.AdmissionLinearizer

/-!
# RCC-45 Finalized Head and Window

Global closure eligibility consumes an actual RCC-42 successful finalizer
computation, its RCC-31 settled effect, durable canonical-history membership,
and an authority-confirmed complete source-window seal.  Partition-local heads
and local GREEN observations carry no closure authority.

This is a safety kernel.  It does not realize the host CAS/storage adapter and
does not prove delivery, quorum, or window-sealing liveness (RCC-46).

Prelude-only Lean 4.14; no Mathlib and no proof placeholders.
-/

namespace Residua.RCC.FinalizedHeadWindow

open Residua.RCC.AuthorizationFinality
open Residua.RCC.AdmissionLinearizer

universe u

/--
The durable finalized-history projection consumed by RCC-45.  It extends the
RCC-43 event carrier with the successor head and authority configuration.  The
single-valued law is about the durable finalized history, not partition-local
views.
-/
structure FinalizedHistoryView
    (EventQ Slot Head Config : Type u) where
  slot : EventQ → Slot
  successorHead : EventQ → Head
  config : EventQ → Config
  finalized : EventQ → Prop
  sameSlotUnique :
    ∀ first second,
      finalized first →
      finalized second →
      slot first = slot second →
      successorHead first = successorHead second ∧
        config first = config second

/--
A finalized canonical head consumes the concrete RCC-43 product.  Consequently
its admission contains the actual `fencedFinalize = .Ok ...` computation, the
pre-state authorization, RCC-31 settlement, and durable history membership.
The finalized-history view binds that same durable event to its successor head
and authority configuration.
-/
structure FinalizedHeadCert
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop)
    (config : Config) (parent : Head)
    (proposal : Proposal Slot Head Judgment) where
  admission : SettledAdmission environment proposal
  head : Head
  configLawful : ConfigLawful config
  parentBound : proposal.expectedParent = parent
  historyFinalized : history.finalized admission.history.event
  historySlotBound : history.slot admission.history.event = proposal.slot
  historyHeadBound : history.successorHead admission.history.event = head
  historyConfigBound : history.config admission.history.event = config

/-- Existential packaging used by the executable gate. -/
structure FinalizedHeadEnvelope
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ)
    (history : FinalizedHistoryView EventQ Slot Head Config)
    (ConfigLawful : Config → Prop) where
  config : Config
  parent : Head
  proposal : Proposal Slot Head Judgment
  certificate :
    FinalizedHeadCert
      environment history ConfigLawful config parent proposal

/--
Two concrete RCC-43 admissions in one durable finalized-history snapshot and
decision slot cannot name conflicting successors or canonical judgments.
-/
theorem finalizedHead_unique
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {leftConfig rightConfig : Config} {parent : Head}
    {leftProposal rightProposal : Proposal Slot Head Judgment}
    (left : FinalizedHeadCert
      environment history ConfigLawful leftConfig parent leftProposal)
    (right : FinalizedHeadCert
      environment history ConfigLawful rightConfig parent rightProposal)
    (sameSlot :
      leftProposal.slot = rightProposal.slot) :
    left.head = right.head ∧
      leftConfig = rightConfig ∧
      environment.equivalence.Equivalent
        leftProposal.judgment rightProposal.judgment := by
  have eventSlots :
      history.slot left.admission.history.event =
        history.slot right.admission.history.event := by
    rw [left.historySlotBound, right.historySlotBound]
    exact sameSlot
  have unique :=
    history.sameSlotUnique
      left.admission.history.event right.admission.history.event
      left.historyFinalized right.historyFinalized eventSlots
  constructor
  · exact left.historyHeadBound.symm.trans
      (unique.1.trans right.historyHeadBound)
  · constructor
    · exact left.historyConfigBound.symm.trans
        (unique.2.trans right.historyConfigBound)
    · exact settled_admissions_same_slot_equivalent
        left.admission right.admission sameSlot

/--
The source authority defines what it means to confirm one watermark over one
complete declared partition window.
-/
structure SourceWindowProtocol
    (SourceAuthority Watermark Partition Head Config : Type u) where
  InUniverse : Partition → Prop
  Confirmation : Type u
  confirms :
    Confirmation → SourceAuthority → Head → Config → Watermark →
      List Partition → Prop

/--
A finite enumeration is sound and complete for the authority-declared source
partition universe.  Empty or shortened caller lists cannot prove absence.
-/
structure CoverageCertificate
    {Partition : Type u}
    (InUniverse : Partition → Prop)
    (enumeration : List Partition) where
  sound : ∀ partition, partition ∈ enumeration → InUniverse partition
  complete : ∀ partition, InUniverse partition → partition ∈ enumeration

/--
The authoritative transition projection consumed by RCC-45.  `InUniverse`
must be instantiated from the admitted authority-transition graph; it is not a
caller-maintained status bit.  RCC-44 remains responsible for constructing this
view from lawful transition certificates.
-/
structure ConfigTransitionView
    (Slot Head Config : Type u) where
  Transition : Type u
  InUniverse : Transition → Prop
  pendingAt : Transition → Slot → Head → Config → Prop

/--
Proof that the complete admitted transition universe contains no transition
pending at this exact finalized coordinate.  Coverage prevents a caller from
hiding a real transition by passing a shortened or empty list.
-/
structure StableConfigEvidence
    {Slot Head Config : Type u}
    (view : ConfigTransitionView Slot Head Config)
    (slot : Slot) (head : Head) (config : Config) where
  transitions : List view.Transition
  coverage : CoverageCertificate view.InUniverse transitions
  noPending :
    ∀ transition,
      transition ∈ transitions →
      ¬ view.pendingAt transition slot head config

/--
An admitted in-universe transition that is pending at the coordinate excludes
stable-config evidence for that coordinate.
-/
theorem pendingTransition_excludesStability
    {Slot Head Config : Type u}
    {view : ConfigTransitionView Slot Head Config}
    {slot : Slot} {head : Head} {config : Config}
    (transition : view.Transition)
    (inUniverse : view.InUniverse transition)
    (pending : view.pendingAt transition slot head config) :
    ¬ Nonempty (StableConfigEvidence view slot head config) := by
  rintro ⟨stable⟩
  exact stable.noPending transition
    (stable.coverage.complete transition inUniverse) pending

/--
An authority-confirmed source-window seal.  Its type binds the current config,
finalized head, and declared prior-partition universe.
-/
structure FinalizedWindowSeal
    {SourceAuthority Watermark Partition Config Head : Type u}
    (protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config)
    (ConfigStable : Config → Prop)
    (config : Config) (head : Head)
    (priorPartitions : List Partition) where
  watermark : Watermark
  sourceAuthority : SourceAuthority
  confirmation : protocol.Confirmation
  authorityConfirmed :
    protocol.confirms confirmation sourceAuthority head config watermark
      priorPartitions
  coverage :
    CoverageCertificate protocol.InUniverse priorPartitions
  includedPartitions : List Partition
  allPriorPartitionsIncluded : includedPartitions = priorPartitions
  configStable : ConfigStable config

/-- Existential packaging used by the executable gate. -/
structure FinalizedWindowEnvelope
    {SourceAuthority Watermark Partition Config Head : Type u}
    (protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config)
    (ConfigStable : Config → Prop) where
  config : Config
  head : Head
  watermark : Watermark
  sourceAuthority : SourceAuthority
  priorPartitions : List Partition
  windowSeal :
    FinalizedWindowSeal protocol ConfigStable config head priorPartitions
  watermarkBound : windowSeal.watermark = watermark
  sourceAuthorityBound : windowSeal.sourceAuthority = sourceAuthority

/-- The exact canonical state against which closure eligibility is assessed. -/
structure ClosureSnapshot
    (Slot Config Head SourceAuthority Watermark Partition : Type u) where
  slot : Slot
  parent : Head
  head : Head
  config : Config
  sourceAuthority : SourceAuthority
  watermark : Watermark
  priorPartitions : List Partition
  transitionView : ConfigTransitionView Slot Head Config

/-- RCC-45 has one named refusal: the global window is not finalized. -/
inductive SourceWindowResidue
  | sourceWindowNotFinalized
  deriving DecidableEq, Repr

/--
Proof package consumed by an `EpochClosed` candidate.  It contains both
certificates and binds them to one snapshot.  It is not a local CLOSED tag.
-/
structure FinalizedClosureEvidence
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop} where
  snapshot :
    ClosureSnapshot
      Slot Config Head SourceAuthority Watermark Partition
  finalizedHead :
    FinalizedHeadEnvelope environment history ConfigLawful
  finalizedWindow :
    FinalizedWindowEnvelope protocol ConfigStable
  slotMatches :
    finalizedHead.proposal.slot = snapshot.slot
  parentMatches : finalizedHead.parent = snapshot.parent
  headMatches : finalizedHead.certificate.head = snapshot.head
  headConfigMatches : finalizedHead.config = snapshot.config
  windowHeadMatches : finalizedWindow.head = snapshot.head
  windowConfigMatches : finalizedWindow.config = snapshot.config
  sourceAuthorityMatches :
    finalizedWindow.sourceAuthority = snapshot.sourceAuthority
  watermarkMatches : finalizedWindow.watermark = snapshot.watermark
  partitionsMatch :
    finalizedWindow.priorPartitions = snapshot.priorPartitions
  stableConfig :
    StableConfigEvidence
      snapshot.transitionView snapshot.slot snapshot.head snapshot.config

/--
The gate exposes eligibility or an honest wait.  Local heads/GREENs are absent
from its authority-bearing inputs by construction.
-/
inductive FinalizedClosureAssessment
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
  | eligible :
      FinalizedClosureEvidence
        (environment := environment)
        (history := history)
        (ConfigLawful := ConfigLawful)
        (protocol := protocol)
        (ConfigStable := ConfigStable) →
      FinalizedClosureAssessment
  | await : SourceWindowResidue → FinalizedClosureAssessment

/--
Mechanically derive closure eligibility from the two global certificates.
Every missing or stale binding returns `[source_window_not_finalized]`.
-/
def assessFinalizedClosure
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName EventQ
      Config SourceAuthority Watermark Partition : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {history : FinalizedHistoryView EventQ Slot Head Config}
    {ConfigLawful : Config → Prop}
    {protocol :
      SourceWindowProtocol SourceAuthority Watermark Partition Head Config}
    {ConfigStable : Config → Prop}
    [DecidableEq Slot] [DecidableEq Config] [DecidableEq Head]
    [DecidableEq Generation] [DecidableEq SourceAuthority]
    [DecidableEq Watermark] [DecidableEq Partition]
    (snapshot :
      ClosureSnapshot
        Slot Config Head SourceAuthority Watermark Partition)
    (finalizedHead? :
      Option (FinalizedHeadEnvelope environment history ConfigLawful))
    (finalizedWindow? :
      Option (FinalizedWindowEnvelope protocol ConfigStable))
    (stableConfig? :
      Option
        (StableConfigEvidence
          snapshot.transitionView snapshot.slot snapshot.head snapshot.config)) :
    FinalizedClosureAssessment
      (environment := environment)
      (history := history)
      (ConfigLawful := ConfigLawful)
      (protocol := protocol)
      (ConfigStable := ConfigStable) :=
  match finalizedHead?, finalizedWindow?, stableConfig? with
  | some finalizedHead, some finalizedWindow, some stableConfig =>
      if bindings :
          finalizedHead.proposal.slot = snapshot.slot ∧
            finalizedHead.parent = snapshot.parent ∧
            finalizedHead.certificate.head = snapshot.head ∧
            finalizedHead.config = snapshot.config ∧
            finalizedWindow.head = snapshot.head ∧
            finalizedWindow.config = snapshot.config ∧
            finalizedWindow.sourceAuthority = snapshot.sourceAuthority ∧
            finalizedWindow.watermark = snapshot.watermark ∧
            finalizedWindow.priorPartitions = snapshot.priorPartitions then
        .eligible
          { snapshot := snapshot
            finalizedHead := finalizedHead
            finalizedWindow := finalizedWindow
            slotMatches := bindings.1
            parentMatches := bindings.2.1
            headMatches := bindings.2.2.1
            headConfigMatches := bindings.2.2.2.1
            windowHeadMatches := bindings.2.2.2.2.1
            windowConfigMatches := bindings.2.2.2.2.2.1
            sourceAuthorityMatches := bindings.2.2.2.2.2.2.1
            watermarkMatches := bindings.2.2.2.2.2.2.2.1
            partitionsMatch := bindings.2.2.2.2.2.2.2.2
            stableConfig := stableConfig }
      else
        .await .sourceWindowNotFinalized
  | _, _, _ => .await .sourceWindowNotFinalized

end Residua.RCC.FinalizedHeadWindow

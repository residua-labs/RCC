import RCC.AuthorizationFinality
import RCC.EffectSettlement
import RCC.PrimitiveOperationalTotality

/-!
# RCC-42 / RCC-43 Admission Linearizer

A canonical fenced-writer snapshot is single-valued per complete decision
slot.  Finality is emitted only for the judgment already present in that
snapshot at the active generation.  RCC-43 admission then requires the actual
successful finalizer result, an RCC-31 fenced settlement, and durable
canonical-history membership for the same proposal occurrence.

This file does not construct quorum certificates, durable vote locks, the host
CAS/storage implementation, or liveness.  Those remain separate realization
and runtime-refinement obligations.
-/

namespace Residua.RCC.AdmissionLinearizer

open Residua.RCC.AuthorizationFinality

universe u v w x y z t

/--
The complete decision-slot identity required at the finality boundary.  The
slot is not a content hash and it deliberately retains every coordinate whose
change can alter finality.
-/
structure DecisionSlot
    (Epoch Config Head OperationClass Scope Sequence Policy : Type u) where
  epoch : Epoch
  config : Config
  parentHead : Head
  operationClass : OperationClass
  scope : Scope
  sequence : Sequence
  policy : Policy
  deriving DecidableEq, Repr

/--
Canonical judgment equivalence.  Finality is single-valued modulo this
relation, rather than modulo certificate bytes or an arbitrary raw proof term.
-/
structure JudgmentEquivalence (Judgment : Type u) where
  Equivalent : Judgment → Judgment → Prop
  refl : ∀ judgment, Equivalent judgment judgment
  symm : ∀ {first second}, Equivalent first second → Equivalent second first
  trans :
    ∀ {first second third},
      Equivalent first second →
      Equivalent second third →
      Equivalent first third
  decide : ∀ first second, Decidable (Equivalent first second)

/-- Projection from the full decision slot to its parent-head coordinate. -/
structure FencedWriterSpec (Slot : Type u) (Head : Type v) where
  slotParent : Slot → Head

/--
One functional fenced-writer state.  The decision map has exactly one cell per
slot by construction; generation and canonical head are explicit fence/CAS
coordinates.
-/
structure FencedWriterState
    (Slot : Type u) (Head : Type v)
    (Judgment : Type w) (Generation : Type x) where
  generation : Generation
  canonicalHead : Head
  decisions : Slot → Option Judgment

/--
Evidence emitted by the fenced writer for one exact proposal and canonical
head. The indices prevent transport to another decision.
-/
structure FencedLinearizationEvidence
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (Generation : Type x)
    (proposal : Proposal Slot Head Judgment) (canonicalHead : Head) where
  generation : Generation
  slot : Slot
  parentHead : Head
  slotBound : slot = proposal.slot
  parentHeadBound : parentHead = canonicalHead

/-- Synchronous fenced-finalizer refusals. -/
inductive FinalizeResidue
  | slotParentMismatch
  | staleParent
  | staleGeneration
  | conflictingJudgment
  deriving DecidableEq, Repr

/-- A valid proposal has not yet won the canonical CAS decision cell. -/
inductive FinalizeWake
  | decisionCommitPending
  deriving DecidableEq, Repr

/--
A proposal is finalized in a writer state only when its slot and parent bind
the current state and the unique slot cell carries an equivalent judgment.
-/
def FinalizedInState
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w} {Generation : Type x}
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (proposal : Proposal Slot Head Judgment) : Prop :=
  spec.slotParent proposal.slot = proposal.expectedParent ∧
    proposal.expectedParent = state.canonicalHead ∧
    ∃ stored,
      state.decisions proposal.slot = some stored ∧
        equivalence.Equivalent stored proposal.judgment

/-- Authorized request presented at one explicit receiver generation. -/
structure FencedFinalizeRequest
    (Slot : Type u) (Head : Type v)
    (Judgment : Type w)
    (AuthorityEvidence : Proposal Slot Head Judgment → Type x)
    (Generation : Type y) where
  authorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence
  expectedGeneration : Generation

/-- Successful output of one concrete fenced-writer `finalize` operation. -/
structure FencedFinalizeOutput
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y}
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) where
  finality :
    FinalityCert Slot Head Judgment AuthorityEvidence
      (FencedLinearizationEvidence Slot Head Judgment Generation)
      state.canonicalHead
  authorizationBound : finality.authorization = request.authorization
  generationBound : request.expectedGeneration = state.generation
  finalized :
    FinalizedInState
      spec equivalence state request.authorization.proposal

/--
RCC-42 fenced single-writer realization.

The operation consumes an authorization certificate and expected writer
generation, checks the full slot parent, canonical head, and active generation,
then reads the canonical CAS decision cell.  An empty cell is `Await`, never a
locally fabricated finality.  Only the judgment already committed in the
single-valued cell can receive a finality certificate.
-/
def fencedFinalize
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) :
    OpResult
      (FencedFinalizeOutput spec equivalence state request)
      FinalizeWake FinalizeResidue :=
  let proposal := request.authorization.proposal
  if slotBound : spec.slotParent proposal.slot = proposal.expectedParent then
    if parentBound : proposal.expectedParent = state.canonicalHead then
      if generationBound : request.expectedGeneration = state.generation then
        match storedEq : state.decisions proposal.slot with
        | none =>
            .Await .decisionCommitPending
        | some stored =>
            match equivalence.decide stored proposal.judgment with
            | .isTrue equivalent =>
                let evidence :
                    FencedLinearizationEvidence
                      Slot Head Judgment Generation proposal
                        state.canonicalHead := {
                  generation := state.generation
                  slot := proposal.slot
                  parentHead := proposal.expectedParent
                  slotBound := rfl
                  parentHeadBound := parentBound
                }
                let finality :
                    FinalityCert Slot Head Judgment AuthorityEvidence
                      (FencedLinearizationEvidence
                        Slot Head Judgment Generation)
                      state.canonicalHead := {
                  authorization := request.authorization
                  linearizationEvidence := evidence
                  parentBound := parentBound
                }
                .Ok {
                  finality := finality
                  authorizationBound := rfl
                  generationBound := generationBound
                  finalized :=
                    ⟨slotBound, parentBound, stored, storedEq, equivalent⟩
                }
            | .isFalse _ =>
                .Refuse .conflictingJudgment
      else
        .Refuse .staleGeneration
    else
      .Refuse .staleParent
  else
    .Refuse .slotParentMismatch

/--
Proof that a finality certificate was emitted by the actual executable
`fencedFinalize` decision, not reconstructed from a caller-supplied state
predicate.
-/
structure SuccessfulFinalize
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) where
  output : FencedFinalizeOutput spec equivalence state request
  accepted :
    fencedFinalize spec equivalence state request = .Ok output

/--
The real writer state, not a caller-supplied consistency proposition, proves
single-valued finality for a decision slot.
-/
theorem finalized_in_state_equivalent
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w} {Generation : Type x}
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    {first second : Proposal Slot Head Judgment}
    (firstFinalized : FinalizedInState spec equivalence state first)
    (secondFinalized : FinalizedInState spec equivalence state second)
    (sameSlot : first.slot = second.slot) :
    equivalence.Equivalent first.judgment second.judgment := by
  obtain ⟨_, _, firstStored, firstAt, firstEquivalent⟩ := firstFinalized
  obtain ⟨_, _, secondStored, secondAt, secondEquivalent⟩ := secondFinalized
  have sameStored : firstStored = secondStored := by
    have sameOption :
        some firstStored = some secondStored := by
      calc
        some firstStored = state.decisions first.slot := firstAt.symm
        _ = state.decisions second.slot := by rw [sameSlot]
        _ = some secondStored := secondAt
    exact Option.some.inj sameOption
  subst secondStored
  exact equivalence.trans
    (equivalence.symm firstEquivalent)
    secondEquivalent

/--
Two actual successful finalizer runs against the same canonical snapshot and
decision slot have equivalent judgments.
-/
theorem successful_finalizes_same_slot_equivalent
    {Slot : Type u} {Head : Type v}
    {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y}
    [DecidableEq Head] [DecidableEq Generation]
    (spec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment)
    (state : FencedWriterState Slot Head Judgment Generation)
    {firstRequest secondRequest :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (first : SuccessfulFinalize spec equivalence state firstRequest)
    (second : SuccessfulFinalize spec equivalence state secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot) :
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment :=
  finalized_in_state_equivalent
    spec equivalence state first.output.finalized second.output.finalized
      sameSlot

/--
The global RCC-42 admission-linearizer surface.

`fencedFinalize` remains the executable check for one receiver snapshot.  This
surface supplies the missing cross-snapshot authority: all receiver snapshots
must refine one versioned canonical CAS cell, and a committed cell is preserved
along the canonical version order.  The active generation is also a function of
the canonical version and parent head, so two snapshots at the same version
cannot both claim different active generations.

The canonical decision is deliberately keyed by parent head and decision slot,
not by generation.  A generation handoff therefore cannot reset an already
committed decision and finalize an inequivalent judgment after the same parent.
-/
structure AdmissionLinearizer
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (Generation : Type x) (Version : Type y)
    (writerSpec : FencedWriterSpec Slot Head)
    (equivalence : JudgmentEquivalence Judgment) where
  Precedes : Version → Version → Prop
  precedesRefl : ∀ version, Precedes version version
  precedesTrans :
    ∀ {first second third},
      Precedes first second →
      Precedes second third →
      Precedes first third
  comparable :
    ∀ first second, Precedes first second ∨ Precedes second first
  activeGeneration : Version → Head → Generation
  canonicalDecision : Version → Head → Slot → Option Judgment
  decisionPreserved :
    ∀ {first second head slot judgment},
      Precedes first second →
      canonicalDecision first head slot = some judgment →
      canonicalDecision second head slot = some judgment

/--
Proof that a concrete receiver snapshot is a projection of one exact version
of the global admission linearizer.

Both fields are load-bearing.  `generationBound` rules out overlapping active
writer generations at one version/head; `decisionBound` prevents two
independently fabricated snapshots from presenting conflicting cells as one
canonical CAS history.
-/
structure CanonicalWriterSnapshot
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {Generation : Type x} {Version : Type y}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence)
    (version : Version)
    (state : FencedWriterState Slot Head Judgment Generation) where
  generationBound :
    state.generation =
      linearizer.activeGeneration version state.canonicalHead
  decisionBound :
    ∀ slot,
      state.decisions slot =
        linearizer.canonicalDecision version state.canonicalHead slot

/--
An actual successful local finalizer run together with its proof of membership
in the global canonical CAS evolution.
-/
structure GloballySuccessfulFinalize
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y} {Version : Type z}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence)
    (version : Version)
    (state : FencedWriterState Slot Head Judgment Generation)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) where
  snapshot : CanonicalWriterSnapshot linearizer version state
  localSuccess :
    SuccessfulFinalize
      writerSpec equivalence state request

/--
The single proof-carrying RCC-42 `finalize` interface.

It executes the existing bounded local receiver decision, but successful output
is returned only together with the caller-supplied proof that the receiver
snapshot belongs to the global canonical CAS evolution.
-/
def AdmissionLinearizer.finalize
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y} {Version : Type z}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence)
    (version : Version)
    (state : FencedWriterState Slot Head Judgment Generation)
    (snapshot : CanonicalWriterSnapshot linearizer version state)
    (request :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation) :
    OpResult
      (GloballySuccessfulFinalize linearizer version state request)
      FinalizeWake FinalizeResidue :=
  match accepted :
      fencedFinalize
        writerSpec equivalence state request with
  | .Ok output =>
      .Ok {
        snapshot := snapshot
        localSuccess := {
          output := output
          accepted := accepted
        }
      }
  | .Await wake => .Await wake
  | .Refuse residue => .Refuse residue
  | .ResourceExhausted residue => .ResourceExhausted residue

/--
Two canonical snapshots at the same global version and parent head cannot
overlap with different active writer generations.
-/
theorem canonical_snapshots_no_generation_overlap
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {Generation : Type x} {Version : Type y}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence}
    {version : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    (first : CanonicalWriterSnapshot linearizer version firstState)
    (second : CanonicalWriterSnapshot linearizer version secondState)
    (sameHead :
      firstState.canonicalHead = secondState.canonicalHead) :
    firstState.generation = secondState.generation := by
  calc
    firstState.generation =
        linearizer.activeGeneration version firstState.canonicalHead :=
      first.generationBound
    _ = linearizer.activeGeneration version secondState.canonicalHead := by
      rw [sameHead]
    _ = secondState.generation := second.generationBound.symm

/--
RCC-42 global finality: successful finalizer runs from distinct receiver
snapshots and distinct canonical versions still carry equivalent judgments
when they target the same decision slot after the same parent head.

The proof compares the two receiver cells through the versioned canonical CAS
cell.  Version comparability chooses the earlier observation; preservation
then transports its committed representative to the later observation.
-/
theorem global_finalizes_same_slot_parent_equivalent
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y} {Version : Type z}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence)
    {firstVersion secondVersion : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (first :
      GloballySuccessfulFinalize
        linearizer firstVersion firstState firstRequest)
    (second :
      GloballySuccessfulFinalize
        linearizer secondVersion secondState secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot)
    (sameParent :
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent) :
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment := by
  obtain
    ⟨_, firstParent, firstStored, firstAt, firstEquivalent⟩ :=
      first.localSuccess.output.finalized
  obtain
    ⟨_, secondParent, secondStored, secondAt, secondEquivalent⟩ :=
      second.localSuccess.output.finalized
  have sameCanonicalHead :
      firstState.canonicalHead = secondState.canonicalHead := by
    exact firstParent.symm.trans (sameParent.trans secondParent)
  have firstCanonical :
      linearizer.canonicalDecision
          firstVersion firstState.canonicalHead
            firstRequest.authorization.proposal.slot =
        some firstStored := by
    exact
      (first.snapshot.decisionBound
        firstRequest.authorization.proposal.slot).symm.trans firstAt
  have secondCanonical :
      linearizer.canonicalDecision
          secondVersion secondState.canonicalHead
            secondRequest.authorization.proposal.slot =
        some secondStored := by
    exact
      (second.snapshot.decisionBound
        secondRequest.authorization.proposal.slot).symm.trans secondAt
  have sameStored : firstStored = secondStored := by
    rcases linearizer.comparable firstVersion secondVersion with
      firstBeforeSecond | secondBeforeFirst
    · have transported :
          linearizer.canonicalDecision
              secondVersion firstState.canonicalHead
                firstRequest.authorization.proposal.slot =
            some firstStored :=
        linearizer.decisionPreserved firstBeforeSecond firstCanonical
      have secondAtFirstCoordinates :
          linearizer.canonicalDecision
              secondVersion firstState.canonicalHead
                firstRequest.authorization.proposal.slot =
            some secondStored := by
        simpa [sameCanonicalHead, sameSlot] using secondCanonical
      exact Option.some.inj (transported.symm.trans secondAtFirstCoordinates)
    · have transported :
          linearizer.canonicalDecision
              firstVersion secondState.canonicalHead
                secondRequest.authorization.proposal.slot =
            some secondStored :=
        linearizer.decisionPreserved secondBeforeFirst secondCanonical
      have firstAtSecondCoordinates :
          linearizer.canonicalDecision
              firstVersion secondState.canonicalHead
                secondRequest.authorization.proposal.slot =
            some firstStored := by
        simpa [sameCanonicalHead, sameSlot] using firstCanonical
      exact Option.some.inj (firstAtSecondCoordinates.symm.trans transported)
  subst secondStored
  exact equivalence.trans
    (equivalence.symm firstEquivalent)
    secondEquivalent

/--
The public `AdmissionLinearizer` safety law requested by RCC-42.

The generation premise makes the decision-slot contract explicit.  The global
CAS proof above is intentionally stronger: because committed decisions survive
generation handoff, it establishes the same conclusion even without assuming
the generations equal.
-/
theorem AdmissionLinearizer.atMostOneFinalized
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type x}
    {Generation : Type y} {Version : Type z}
    {writerSpec : FencedWriterSpec Slot Head}
    {equivalence : JudgmentEquivalence Judgment}
    [DecidableEq Head] [DecidableEq Generation]
    (linearizer :
      AdmissionLinearizer
        Slot Head Judgment Generation Version writerSpec equivalence)
    {firstVersion secondVersion : Version}
    {firstState secondState :
      FencedWriterState Slot Head Judgment Generation}
    {firstRequest secondRequest :
      FencedFinalizeRequest
        Slot Head Judgment AuthorityEvidence Generation}
    (first :
      GloballySuccessfulFinalize
        linearizer firstVersion firstState firstRequest)
    (second :
      GloballySuccessfulFinalize
        linearizer secondVersion secondState secondRequest)
    (sameSlot :
      firstRequest.authorization.proposal.slot =
        secondRequest.authorization.proposal.slot)
    (_sameGeneration :
      firstState.generation = secondState.generation)
    (sameParent :
      firstRequest.authorization.proposal.expectedParent =
        secondRequest.authorization.proposal.expectedParent) :
    equivalence.Equivalent
      firstRequest.authorization.proposal.judgment
      secondRequest.authorization.proposal.judgment :=
  global_finalizes_same_slot_parent_equivalent
    linearizer first second sameSlot sameParent

/-- Read-only view of the identity coordinates stored in a durable event. -/
structure HistoryEventView
    (EventQ Slot Head Judgment Occurrence : Type u) where
  preHead : EventQ → Head
  slot : EventQ → Slot
  judgment : EventQ → Judgment
  occurrence : EventQ → Occurrence

/--
Sealed canonical-history membership surface.  A runtime adapter must bind
`contains` to durable storage and the finalized canonical head.
-/
structure CanonicalHistorySnapshot (EventQ Head : Type u) where
  canonicalHead : Head
  contains : EventQ → Bool
  durableContains : EventQ → Prop
  containsSound :
    ∀ event, contains event = true → durableContains event

/--
Proof that one durable event records the exact proposal occurrence at the
canonical parent.  Judgment binding uses the declared canonical equivalence.
-/
structure CanonicalHistoryRecord
    {Slot Head Judgment Occurrence EventQ : Type u}
    (equivalence : JudgmentEquivalence Judgment)
    (view : HistoryEventView EventQ Slot Head Judgment Occurrence)
    (snapshot : CanonicalHistorySnapshot EventQ Head)
    (proposal : Proposal Slot Head Judgment)
    (expectedOccurrence : Occurrence) where
  event : EventQ
  recorded : snapshot.contains event = true
  durablyRecorded : snapshot.durableContains event
  canonicalHeadBound : snapshot.canonicalHead = proposal.expectedParent
  preHeadBound : view.preHead event = proposal.expectedParent
  slotBound : view.slot event = proposal.slot
  judgmentBound :
    equivalence.Equivalent (view.judgment event) proposal.judgment
  occurrenceBound : view.occurrence event = expectedOccurrence

/--
All same-snapshot surfaces consumed by RCC-43.  The effect snapshot is the
actual RCC-31 carrier; no parallel opaque effect tag is accepted.
-/
structure AdmissionEnvironment
    (Slot Head Judgment : Type u)
    (AuthorityEvidence : Proposal Slot Head Judgment → Type u)
    (Generation Epoch EffectSlot Occurrence FailureName EventQ : Type u) where
  writerSpec : FencedWriterSpec Slot Head
  equivalence : JudgmentEquivalence Judgment
  writerState : FencedWriterState Slot Head Judgment Generation
  effectSnapshot :
    EffectSettlement.EffectSnapshot
      Epoch Head EffectSlot Generation Occurrence FailureName
  historyView : HistoryEventView EventQ Slot Head Judgment Occurrence
  historySnapshot : CanonicalHistorySnapshot EventQ Head
  occurrenceOf : Proposal Slot Head Judgment → Occurrence
  effectSlotOf : Slot → EffectSlot
  effectHeadBound : effectSnapshot.head = writerState.canonicalHead
  historyHeadBound : historySnapshot.canonicalHead = writerState.canonicalHead
  generationCoherent :
    ∀ slot,
      effectSnapshot.currentGeneration (effectSlotOf slot) =
        writerState.generation

/--
RCC-43 proof-carrying admission.

Construction requires all three independent layers:

* a proposal finalized in the concrete RCC-42 writer state;
* an RCC-31 `FencedSettledReceipt` for the bound external effect; and
* a durable canonical-history record for the same occurrence and proposal.
-/
structure SettledAdmission
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    (environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ)
    (proposal : Proposal Slot Head Judgment) where
  finalizeRequest :
    FencedFinalizeRequest
      Slot Head Judgment AuthorityEvidence Generation
  proposalBound : finalizeRequest.authorization.proposal = proposal
  finalizeSuccess :
    SuccessfulFinalize
      environment.writerSpec environment.equivalence
        environment.writerState finalizeRequest
  effect :
    EffectSettlement.ExternalEffect Occurrence Head EffectSlot
  effectDeclared : effect ∈ environment.effectSnapshot.externalEffects
  effectOccurrenceBound :
    effect.occurrence = environment.occurrenceOf proposal
  effectParentBound : effect.expectedParent = proposal.expectedParent
  effectSlotBound : effect.effectSlot = environment.effectSlotOf proposal.slot
  effectObservation :
    EffectSettlement.EffectObservation
      Epoch Head EffectSlot Generation Occurrence FailureName
  effectReceipt :
    EffectSettlement.EffectReceipt
      Epoch Head EffectSlot Generation Occurrence FailureName
  settled :
    EffectSettlement.FencedSettledReceipt
      environment.effectSnapshot effect effectObservation effectReceipt
  history :
    CanonicalHistoryRecord
      environment.equivalence environment.historyView
        environment.historySnapshot proposal (environment.occurrenceOf proposal)

/--
RCC-43: two fully settled and durably recorded admissions in one decision
slot carry equivalent canonical judgments.
-/
theorem settled_admissions_same_slot_equivalent
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {first second : Proposal Slot Head Judgment}
    (firstAdmitted : SettledAdmission environment first)
    (secondAdmitted : SettledAdmission environment second)
    (sameSlot : first.slot = second.slot) :
    environment.equivalence.Equivalent first.judgment second.judgment :=
  by
    have requestSlot :
        firstAdmitted.finalizeRequest.authorization.proposal.slot =
          secondAdmitted.finalizeRequest.authorization.proposal.slot := by
      rw [firstAdmitted.proposalBound, secondAdmitted.proposalBound]
      exact sameSlot
    have equivalent :=
      successful_finalizes_same_slot_equivalent
        environment.writerSpec environment.equivalence environment.writerState
          firstAdmitted.finalizeSuccess secondAdmitted.finalizeSuccess
          requestSlot
    simpa [firstAdmitted.proposalBound, secondAdmitted.proposalBound] using
      equivalent

/-- Every RCC-43 admission consumes an RCC-31 terminal settlement proof. -/
theorem settled_admission_effect_terminal
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {proposal : Proposal Slot Head Judgment}
    (admission : SettledAdmission environment proposal) :
    EffectSettlement.EffectPhase.IsTerminal
      environment.effectSnapshot.policyTerminalFailure
      admission.effectReceipt.phase :=
  EffectSettlement.settlement_coherent_is_terminal
    admission.effectObservation admission.effectReceipt admission.settled.coherent

/-- Every complete RCC-43 admission retains its pre-state authorization. -/
theorem settled_admission_implies_authorized
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {proposal : Proposal Slot Head Judgment}
    (admission : SettledAdmission environment proposal) :
    AuthorizedWithReceipt
      Slot Head Judgment AuthorityEvidence proposal := by
  exact
    ⟨admission.finalizeRequest.authorization,
      admission.proposalBound⟩

/-- Every complete RCC-43 admission has durable canonical-history membership. -/
theorem settled_admission_history_durable
    {Slot Head Judgment Generation Epoch EffectSlot Occurrence FailureName
      EventQ : Type u}
    {AuthorityEvidence : Proposal Slot Head Judgment → Type u}
    [DecidableEq Head] [DecidableEq Generation]
    {environment :
      AdmissionEnvironment
        Slot Head Judgment AuthorityEvidence Generation Epoch EffectSlot
          Occurrence FailureName EventQ}
    {proposal : Proposal Slot Head Judgment}
    (admission : SettledAdmission environment proposal) :
    environment.historySnapshot.durableContains admission.history.event :=
  admission.history.durablyRecorded

/-- The semantic content retained by the admission linearizer. -/
structure FinalizedDecision (Slot : Type u) (Judgment : Type v) where
  slot : Slot
  judgment : Judgment

/-- A slot/judgment pair occurs in the finalized decision log. -/
def FinalizedByLog
    {Slot : Type u} {Judgment : Type v}
    (log : List (FinalizedDecision Slot Judgment))
    (slot : Slot) (judgment : Judgment) : Prop :=
  ∃ decision ∈ log,
    decision.slot = slot ∧ decision.judgment = judgment

/-- Every two finalized decisions in one slot carry the same judgment. -/
def ConsistentLog
    {Slot : Type u} {Judgment : Type v}
    (log : List (FinalizedDecision Slot Judgment)) : Prop :=
  ∀ first ∈ log, ∀ second ∈ log,
    first.slot = second.slot → first.judgment = second.judgment

/-- RCC-42: a consistent finalized log is single-valued per decision slot. -/
theorem finalized_by_consistent_log_unique
    {Slot : Type u} {Judgment : Type v}
    {log : List (FinalizedDecision Slot Judgment)}
    {slot : Slot} {firstJudgment secondJudgment : Judgment}
    (consistent : ConsistentLog log)
    (firstFinalized : FinalizedByLog log slot firstJudgment)
    (secondFinalized : FinalizedByLog log slot secondJudgment) :
    firstJudgment = secondJudgment := by
  obtain ⟨first, firstIn, firstSlot, firstJudgmentEq⟩ := firstFinalized
  obtain ⟨second, secondIn, secondSlot, secondJudgmentEq⟩ :=
    secondFinalized
  have sameDecisionJudgment :=
    consistent first firstIn second secondIn
      (firstSlot.trans secondSlot.symm)
  exact firstJudgmentEq.symm.trans
    (sameDecisionJudgment.trans secondJudgmentEq)

end Residua.RCC.AdmissionLinearizer

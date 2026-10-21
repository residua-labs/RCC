/-!
# RCC-39 Authorization Is Not Finality

Authorization, finality, effect settlement, and history recording are distinct
proof-carrying layers.  A proposal is admitted only when all four layers bind
the same proposal at the canonical parent head.

The evidence languages below are indexed by the proposal (and, for
linearization, by the canonical head).  Those indices prevent evidence for one
decision from being spliced into another.  Inhabiting an evidence language is
not by itself a theorem that the evidence is semantically adequate: each RCC
instance must supply that realization theorem.

This kernel does not construct threshold authorization, an admission
linearizer, an external effect receipt, or a durable append receipt.  RCC-34,
RCC-40..42, RCC-31, and the history runtime own those realizations.

Prelude-only Lean 4.14; no Mathlib, no `sorry`, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.AuthorizationFinality

universe u v w x y z t

/-- The full decision identity needed by the authorization/finality boundary. -/
structure Proposal
    (Slot : Type u) (Head : Type v) (Judgment : Type w) where
  slot : Slot
  expectedParent : Head
  judgment : Judgment
  deriving Repr

/--
A proposal plus domain-supplied proof-carrying authority evidence indexed by
that exact proposal.

The family index is a binding law only.  The domain adapter remains
responsible for proving that inhabitants really witness pre-state authority.
-/
structure AuthorizedProposal
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x) where
  proposal : Proposal Slot Head Judgment
  authorityEvidence : AuthorityEvidence proposal

/--
Finality consumes authorization and independent linearization evidence indexed
by both the exact proposal and canonical head.  It also proves that the
proposal expected that canonical parent.
-/
structure FinalityCert
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x)
    (LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y)
    (canonicalHead : Head) where
  authorization :
    AuthorizedProposal Slot Head Judgment AuthorityEvidence
  linearizationEvidence :
    LinearizationEvidence authorization.proposal canonicalHead
  parentBound : authorization.proposal.expectedParent = canonicalHead

/--
Settled external-effect evidence is indexed by the exact proposal it settles.
The instance still owns the theorem connecting this evidence to the physical
effect protocol.
-/
structure EffectSettlementCert
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (EffectEvidence :
      Proposal Slot Head Judgment → Type x) where
  proposal : Proposal Slot Head Judgment
  effectEvidence : EffectEvidence proposal

/--
Durable history-record evidence is indexed by the exact proposal it records.
The instance still owns the theorem connecting this evidence to durable
canonical-history membership.
-/
structure HistoryRecordCert
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (HistoryEvidence :
      Proposal Slot Head Judgment → Type x) where
  proposal : Proposal Slot Head Judgment
  historyEvidence : HistoryEvidence proposal

/--
Admission is a product of finality, effect settlement, and history recording.
The equality fields prevent valid certificates for different proposals from
being spliced together.
-/
structure AdmittedCert
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x)
    (LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y)
    (EffectEvidence :
      Proposal Slot Head Judgment → Type z)
    (HistoryEvidence :
      Proposal Slot Head Judgment → Type t)
    (canonicalHead : Head) where
  finality :
    FinalityCert Slot Head Judgment AuthorityEvidence
      LinearizationEvidence canonicalHead
  effectSettlement :
    EffectSettlementCert Slot Head Judgment EffectEvidence
  historyRecord :
    HistoryRecordCert Slot Head Judgment HistoryEvidence
  effectBindsProposal :
    effectSettlement.proposal = finality.authorization.proposal
  historyBindsProposal :
    historyRecord.proposal = finality.authorization.proposal

/-- Existential authorization judgment for a fixed receipt language. -/
def AuthorizedWithReceipt
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x)
    (proposal : Proposal Slot Head Judgment) : Prop :=
  ∃ certificate :
      AuthorizedProposal Slot Head Judgment AuthorityEvidence,
    certificate.proposal = proposal

/-- Existential finality judgment for fixed authorization/linearizer languages. -/
def FinalizedWithReceipts
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x)
    (LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y)
    (proposal : Proposal Slot Head Judgment)
    (canonicalHead : Head) : Prop :=
  ∃ certificate :
      FinalityCert Slot Head Judgment AuthorityEvidence
        LinearizationEvidence canonicalHead,
    certificate.authorization.proposal = proposal

/-- Existential admission judgment for fixed proof-carrying receipt languages. -/
def AdmittedWithReceipts
    (Slot : Type u) (Head : Type v) (Judgment : Type w)
    (AuthorityEvidence :
      Proposal Slot Head Judgment → Type x)
    (LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y)
    (EffectEvidence :
      Proposal Slot Head Judgment → Type z)
    (HistoryEvidence :
      Proposal Slot Head Judgment → Type t)
    (proposal : Proposal Slot Head Judgment)
    (canonicalHead : Head) : Prop :=
  ∃ certificate :
      AdmittedCert Slot Head Judgment AuthorityEvidence LinearizationEvidence
        EffectEvidence HistoryEvidence canonicalHead,
    certificate.finality.authorization.proposal = proposal

/-- Finality retains the exact authorization certificate it consumed. -/
theorem finalized_implies_authorized
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence :
      Proposal Slot Head Judgment → Type x}
    {LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y}
    {proposal : Proposal Slot Head Judgment} {canonicalHead : Head}
    (finalized :
      FinalizedWithReceipts Slot Head Judgment AuthorityEvidence
        LinearizationEvidence proposal canonicalHead) :
    AuthorizedWithReceipt Slot Head Judgment AuthorityEvidence proposal := by
  obtain ⟨certificate, binds⟩ := finalized
  exact ⟨certificate.authorization, binds⟩

/-- Admission retains the exact finality certificate it consumed. -/
theorem admitted_implies_finalized
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence :
      Proposal Slot Head Judgment → Type x}
    {LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y}
    {EffectEvidence :
      Proposal Slot Head Judgment → Type z}
    {HistoryEvidence :
      Proposal Slot Head Judgment → Type t}
    {proposal : Proposal Slot Head Judgment} {canonicalHead : Head}
    (admitted :
      AdmittedWithReceipts Slot Head Judgment AuthorityEvidence
        LinearizationEvidence EffectEvidence HistoryEvidence
        proposal canonicalHead) :
    FinalizedWithReceipts Slot Head Judgment AuthorityEvidence
      LinearizationEvidence proposal canonicalHead := by
  obtain ⟨certificate, binds⟩ := admitted
  exact ⟨certificate.finality, binds⟩

/-- The complete admission chain contains authorization through finality. -/
theorem admitted_implies_authorized
    {Slot : Type u} {Head : Type v} {Judgment : Type w}
    {AuthorityEvidence :
      Proposal Slot Head Judgment → Type x}
    {LinearizationEvidence :
      Proposal Slot Head Judgment → Head → Type y}
    {EffectEvidence :
      Proposal Slot Head Judgment → Type z}
    {HistoryEvidence :
      Proposal Slot Head Judgment → Type t}
    {proposal : Proposal Slot Head Judgment} {canonicalHead : Head}
    (admitted :
      AdmittedWithReceipts Slot Head Judgment AuthorityEvidence
        LinearizationEvidence EffectEvidence HistoryEvidence
        proposal canonicalHead) :
    AuthorizedWithReceipt Slot Head Judgment AuthorityEvidence proposal :=
  finalized_implies_authorized (admitted_implies_finalized admitted)

end Residua.RCC.AuthorizationFinality

/-!
# RCC-28 Exactly-Once Premise

This module proves the scoped premise from ADR §21.4:

```
AtLeastOnce delivery
+ current fencing
+ atomic receiver dedup keyed by occurrence identity
→ exactly one observable enactment
```

The receiver state contains an `AtomicCommit`: enactment and receiver receipt
are one value installed by one state transition.  A lookup is keyed by logical
occurrence, not payload content.  Retries observe the existing commit.

This is a finite, receiver-local safety theorem.  Fair delivery / external
liveness, digest faithfulness from AddressKernel, distributed transaction
implementation, and compensation are explicit nonclaims.

Prelude-only Lean 4.14; no Mathlib and no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.ExactlyOnce

universe u v w x

/--
The receiver fence binds the epoch, canonical head, effect slot, and logical
generation.  RCC-28 treats construction and authenticity of these coordinates
as an external premise; the receiver only accepts its current token.
-/
structure FencingToken
    (Epoch : Type u) (Head : Type v)
    (EffectSlot : Type w) (Generation : Type x) where
  epoch : Epoch
  head : Head
  effectSlot : EffectSlot
  generation : Generation
  deriving DecidableEq, Repr

/-- A delivery attempt presents one logical occurrence and a fencing token. -/
structure Delivery (Occurrence : Type u) (Fence : Type v) where
  occurrence : Occurrence
  fence : Fence

/--
The only receiver representation of an enacted effect.  Effect and receipt
cannot be represented independently inside this contract.
-/
structure AtomicCommit
    (Occurrence : Type u) (Fence : Type v)
    (Effect : Type w) (Receipt : Type x) where
  occurrence : Occurrence
  fence : Fence
  enactment : Effect
  receipt : Receipt

/--
Receiver-owned atomic state.  One occurrence key has at most one committed
value because lookup returns an `Option`, not a list of attempts.
-/
abbrev ReceiverState
    (Occurrence : Type u) (Fence : Type v)
    (Effect : Type w) (Receipt : Type x) :=
  Occurrence → Option (AtomicCommit Occurrence Fence Effect Receipt)

/--
The receiver contract fixes the current fence and the effect/receipt associated
with a logical occurrence.  The atomic transition below is the only writer.
-/
structure AtomicReceiverContract
    (Occurrence : Type u) (Fence : Type v)
    (Effect : Type w) (Receipt : Type x) where
  currentFence : Occurrence → Fence
  effectFor : Occurrence → Effect
  receiptFor : Occurrence → Fence → Effect → Receipt

def emptyState
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x} :
    ReceiverState Occurrence Fence Effect Receipt :=
  fun _ => none

/--
Fenced atomic receiver step.  A stale fence changes nothing.  A retry of an
already committed occurrence changes nothing.  Only an empty, current-fence
slot installs one coupled enactment+receipt commit.
-/
def atomicReceive
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (delivery : Delivery Occurrence Fence) :
    ReceiverState Occurrence Fence Effect Receipt :=
  if delivery.fence = contract.currentFence delivery.occurrence then
    match state delivery.occurrence with
    | some _ => state
    | none =>
        fun candidate =>
          if candidate = delivery.occurrence then
            let effect := contract.effectFor delivery.occurrence
            some
              { occurrence := delivery.occurrence
              , fence := delivery.fence
              , enactment := effect
              , receipt :=
                  contract.receiptFor
                    delivery.occurrence delivery.fence effect }
          else
            state candidate
  else
    state

def run
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt) :
    ReceiverState Occurrence Fence Effect Receipt →
      List (Delivery Occurrence Fence) →
      ReceiverState Occurrence Fence Effect Receipt
  | state, [] => state
  | state, delivery :: rest =>
      run contract (atomicReceive contract state delivery) rest

/-- The finite schedule contains at least one attempt for this occurrence. -/
def AtLeastOnce
    {Occurrence : Type u} {Fence : Type v}
    (deliveries : List (Delivery Occurrence Fence))
    (occurrence : Occurrence) : Prop :=
  ∃ delivery, delivery ∈ deliveries ∧ delivery.occurrence = occurrence

/-- Every admitted attempt in this finite schedule carries the current fence. -/
def FencedDeliveries
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (deliveries : List (Delivery Occurrence Fence)) : Prop :=
  ∀ delivery, delivery ∈ deliveries →
    delivery.fence = contract.currentFence delivery.occurrence

/-- An effect is observable only through an installed atomic commit. -/
def ObservableEnactment
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (occurrence : Occurrence) (effect : Effect) : Prop :=
  ∃ commit, state occurrence = some commit ∧ commit.enactment = effect

/-- A receipt is observable through the same installed atomic commit. -/
def ObservableReceipt
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (occurrence : Occurrence) (receipt : Receipt) : Prop :=
  ∃ commit, state occurrence = some commit ∧ commit.receipt = receipt

def ExactlyOnceObservable
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (occurrence : Occurrence) : Prop :=
  ∃ effect : Effect,
    ObservableEnactment state occurrence effect ∧
      ∀ other : Effect,
        ObservableEnactment state occurrence other → other = effect

theorem atomic_receive_preserves_commit
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (delivery : Delivery Occurrence Fence)
    (occurrence : Occurrence)
    (commit : AtomicCommit Occurrence Fence Effect Receipt)
    (committed : state occurrence = some commit) :
    atomicReceive contract state delivery occurrence = some commit := by
  unfold atomicReceive
  split
  · cases stateAtDelivery : state delivery.occurrence with
    | none =>
        dsimp only
        split
        · subst occurrence
          rw [stateAtDelivery] at committed
          contradiction
        · exact committed
    | some existing =>
        dsimp only
        exact committed
  · exact committed

theorem run_preserves_commit
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (deliveries : List (Delivery Occurrence Fence))
    (occurrence : Occurrence)
    (commit : AtomicCommit Occurrence Fence Effect Receipt)
    (committed : state occurrence = some commit) :
    run contract state deliveries occurrence = some commit := by
  induction deliveries generalizing state with
  | nil =>
      exact committed
  | cons delivery rest induction =>
      exact induction
        (atomicReceive contract state delivery)
        (atomic_receive_preserves_commit
          contract state delivery occurrence commit committed)

theorem atomic_receive_current_fence_commits
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (delivery : Delivery Occurrence Fence)
    (current :
      delivery.fence = contract.currentFence delivery.occurrence) :
    ∃ commit,
      atomicReceive contract state delivery delivery.occurrence = some commit := by
  unfold atomicReceive
  rw [if_pos current]
  cases stateAtDelivery : state delivery.occurrence with
  | none =>
      dsimp only
      let effect := contract.effectFor delivery.occurrence
      let commit :
          AtomicCommit Occurrence Fence Effect Receipt :=
        { occurrence := delivery.occurrence
        , fence := delivery.fence
        , enactment := effect
        , receipt :=
            contract.receiptFor
              delivery.occurrence delivery.fence effect }
      refine ⟨commit, ?_⟩
      rw [if_pos rfl]
  | some commit =>
      exact ⟨commit, stateAtDelivery⟩

theorem run_commits_delivered_occurrence
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (deliveries : List (Delivery Occurrence Fence))
    (target : Delivery Occurrence Fence)
    (member : target ∈ deliveries)
    (current : target.fence = contract.currentFence target.occurrence) :
    ∃ commit,
      run contract state deliveries target.occurrence = some commit := by
  induction deliveries generalizing state with
  | nil =>
      contradiction
  | cons delivery rest induction =>
      cases member with
      | head =>
        rcases atomic_receive_current_fence_commits
          contract state target current with ⟨commit, committed⟩
        exact
          ⟨commit,
            run_preserves_commit
              contract (atomicReceive contract state target) rest
              target.occurrence commit committed⟩
      | tail _ tailMember =>
        exact induction
          (atomicReceive contract state delivery)
          tailMember

theorem exactly_once_observable_of_commit
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (occurrence : Occurrence)
    (commit : AtomicCommit Occurrence Fence Effect Receipt)
    (committed : state occurrence = some commit) :
    ExactlyOnceObservable state occurrence := by
  refine ⟨commit.enactment, ⟨commit, committed, rfl⟩, ?_⟩
  intro effect observable
  rcases observable with ⟨other, otherCommitted, otherEffect⟩
  have sameCommit : other = commit :=
    Option.some.inj (otherCommitted.symm.trans committed)
  exact (sameCommit ▸ otherEffect).symm

/--
RCC-28.  At-least-once delivery plus current fencing and receiver-owned atomic
deduplication by occurrence identity yields exactly one observable enactment.
-/
theorem exactly_once_observable_of_at_least_once
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    [DecidableEq Occurrence] [DecidableEq Fence]
    (contract : AtomicReceiverContract Occurrence Fence Effect Receipt)
    (deliveries : List (Delivery Occurrence Fence))
    (occurrence : Occurrence)
    (atLeastOnce : AtLeastOnce deliveries occurrence)
    (fenced : FencedDeliveries contract deliveries) :
    ExactlyOnceObservable
      (run contract emptyState deliveries) occurrence := by
  rcases atLeastOnce with ⟨delivery, member, sameOccurrence⟩
  have current := fenced delivery member
  rcases run_commits_delivered_occurrence
      contract emptyState deliveries delivery member current with
    ⟨commit, committed⟩
  subst occurrence
  exact exactly_once_observable_of_commit
    (run contract emptyState deliveries)
    delivery.occurrence commit committed

/--
Atomicity is load-bearing: every observable enactment exposes the receipt from
the very same commit.  This model has no representable applied/unrecorded or
recorded/not-applied state.
-/
theorem observable_enactment_has_coupled_receipt
    {Occurrence : Type u} {Fence : Type v}
    {Effect : Type w} {Receipt : Type x}
    (state : ReceiverState Occurrence Fence Effect Receipt)
    (occurrence : Occurrence) (effect : Effect)
    (observable : ObservableEnactment state occurrence effect) :
    ∃ receipt, ObservableReceipt state occurrence receipt := by
  rcases observable with ⟨commit, committed, _⟩
  exact ⟨commit.receipt, commit, committed, rfl⟩

#print axioms atomic_receive_preserves_commit
#print axioms atomic_receive_current_fence_commits
#print axioms run_commits_delivered_occurrence
#print axioms exactly_once_observable_of_commit
#print axioms exactly_once_observable_of_at_least_once
#print axioms observable_enactment_has_coupled_receipt

end Residua.RCC.ExactlyOnce


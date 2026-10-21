/-!
# RCC-22 Await Wake Adequacy Kernel

`Await` is admissible only with a non-empty, currently unsatisfied wake predicate,
an identified observation source, an affected goal and invalidation rule, a causal
evidence effect, no same-epoch advance, and an expiry/recheck policy.

No-observation rechecks are represented as externally suspended, receipt-free,
state-preserving polls.  Once the policy is expired, the indexed disposition type
can inhabit only `Ready`, `Stuck`, `Reepoch`, or `Halt`.

This is a parametric kernel.  It does not claim that a concrete observation source is
authentic or live, that a runtime dependency extractor is complete, that a scheduler
is fair, or that detector/registry/workflow/aggregator wiring exists.

Prelude-only Lean 4.14; no Mathlib, no proof placeholders, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC

universe u v w x y z

/-- A wake either has a finite expiry boundary or an explicit external recheck trigger. -/
inductive ExpiryOrRecheckPolicy (Deadline : Type u) (Recheck : Type v)
  | expiresAt (deadline : Deadline)
  | recheckOn (trigger : Recheck)
  deriving DecidableEq

/-- Domain operations and state projections consumed by the RCC-22 kernel. -/
structure WakeSystem where
  State : Type u
  Goal : Type v
  Observation : Type w
  Source : Type x
  InvalidationRule : Type y
  Evidence : Type z
  History : Type z
  GoalView : Type z
  Receipt : Type z
  ReceiptLog : Type z
  Deadline : Type z
  Recheck : Type z
  currentGoal : State → Option Goal
  goalOpen : State → Goal → Prop
  goalObstructed : State → Goal → Prop
  sameEpochAdvance : State → State → Prop
  observed : State → Observation → Prop
  sourceOf : Observation → Source
  goalDependsOn : State → Goal → Observation → Prop
  ruleApplies : InvalidationRule → Observation → Goal → Prop
  admitObservation : State → Observation → State
  goalEvidence : State → Goal → Option Evidence
  measure : State → Nat
  history : State → History
  goalView : State → Goal → GoalView
  receiptLog : State → ReceiptLog
  expired : State → ExpiryOrRecheckPolicy Deadline Recheck → Prop

/-- There is no executable same-epoch successor from the current state. -/
def NoSameEpochAdvance (S : WakeSystem) (state : S.State) : Prop :=
  ∀ next, ¬ S.sameEpochAdvance state next

/--
Admitting a causal observation either clears an existing evidence packet or recomputes
it to a definitionally different packet.
-/
inductive EvidencePacketEffect
    (S : WakeSystem) (state : S.State)
    (observation : S.Observation) (goal : S.Goal) : Prop
  | invalidated
      (prior : ∃ evidence, S.goalEvidence state goal = some evidence)
      (cleared :
        S.goalEvidence (S.admitObservation state observation) goal = none)
  | recomputed
      (changed :
        S.goalEvidence (S.admitObservation state observation) goal ≠
          S.goalEvidence state goal)

/--
The six-field WakeContract from ADR §20.4.  `predicateNonempty` prevents placeholder
predicates, while `predicateSource` binds every match to the named source.
-/
structure WakeContract (S : WakeSystem) (state : S.State) where
  wakePredicate : S.Observation → Prop
  predicateNonempty : ∃ observation, wakePredicate observation
  observationSource : S.Source
  predicateSource :
    ∀ observation, wakePredicate observation →
      S.sourceOf observation = observationSource
  currentlyUnsatisfied :
    ¬ ∃ observation, S.observed state observation ∧ wakePredicate observation
  affectedGoal : S.Goal
  currentGoalBinding : S.currentGoal state = some affectedGoal
  affectedGoalOpen : S.goalOpen state affectedGoal
  affectedGoalObstructed : S.goalObstructed state affectedGoal
  invalidationRule : S.InvalidationRule
  expiryOrRecheckPolicy : ExpiryOrRecheckPolicy S.Deadline S.Recheck

/--
Proof that `Await contract` is adequate at one state.  Source binding and current
unsatisfaction live in the contract; these additional fields prove progress exclusion,
goal causality, effective invalidation/recomputation, and admission-time freshness.
-/
structure AwaitCertificate
    (S : WakeSystem) (state : S.State) (contract : WakeContract S state) where
  noSameEpochAdvance : NoSameEpochAdvance S state
  causalDependency :
    ∀ observation, contract.wakePredicate observation →
      S.goalDependsOn state contract.affectedGoal observation
  invalidationEffective :
    ∀ observation, contract.wakePredicate observation →
      S.ruleApplies contract.invalidationRule observation contract.affectedGoal ∧
        EvidencePacketEffect S state observation contract.affectedGoal
  notExpiredAtAdmission :
    ¬ S.expired state contract.expiryOrRecheckPolicy

/-- Await admission exposes the absence of any same-epoch successor. -/
theorem await_requires_no_same_epoch_advance
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    NoSameEpochAdvance S state := by
  exact certificate.noSameEpochAdvance

/-- Await admission exposes that no already-observed value satisfies its predicate. -/
theorem await_requires_currently_unsatisfied
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (_certificate : AwaitCertificate S state contract) :
    ¬ ∃ observation,
      S.observed state observation ∧ contract.wakePredicate observation := by
  exact contract.currentlyUnsatisfied

/-- Await is bound to the current Goal and that Goal is both open and obstructed. -/
theorem await_requires_current_open_obstructed_goal
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (_certificate : AwaitCertificate S state contract) :
    S.currentGoal state = some contract.affectedGoal ∧
      S.goalOpen state contract.affectedGoal ∧
      S.goalObstructed state contract.affectedGoal := by
  exact ⟨
    contract.currentGoalBinding,
    contract.affectedGoalOpen,
    contract.affectedGoalObstructed
  ⟩

/--
Every matching wake is source-bound, is a dependency of the affected goal, activates
the named invalidation rule, and invalidates or recomputes that goal's evidence.
-/
theorem await_requires_causal_dependency
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract)
    (observation : S.Observation)
    (hpredicate : contract.wakePredicate observation) :
    S.sourceOf observation = contract.observationSource ∧
      S.goalDependsOn state contract.affectedGoal observation ∧
      S.ruleApplies contract.invalidationRule observation contract.affectedGoal ∧
      EvidencePacketEffect S state observation contract.affectedGoal := by
  exact ⟨
    contract.predicateSource observation hpredicate,
    certificate.causalDependency observation hpredicate,
    (certificate.invalidationEffective observation hpredicate).1,
    (certificate.invalidationEffective observation hpredicate).2
  ⟩

/-- Non-emptiness plus adequacy yields at least one potential causally effective wake. -/
theorem await_has_nonempty_causal_wake
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    ∃ observation,
      contract.wakePredicate observation ∧
      S.sourceOf observation = contract.observationSource ∧
      S.goalDependsOn state contract.affectedGoal observation ∧
      S.ruleApplies contract.invalidationRule observation contract.affectedGoal ∧
      EvidencePacketEffect S state observation contract.affectedGoal := by
  rcases contract.predicateNonempty with ⟨observation, hpredicate⟩
  refine ⟨observation, hpredicate, ?_⟩
  exact await_requires_causal_dependency
    certificate observation hpredicate

/--
RCC-22 headline: one Await certificate simultaneously excludes same-epoch
progress, binds an unsatisfied current open obstruction, is unexpired at its
indexed admission state, and supplies a nonempty source-bound wake that
causally changes its evidence.
-/
theorem AwaitCertificate.sound
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    NoSameEpochAdvance S state ∧
      (¬ ∃ observation,
        S.observed state observation ∧ contract.wakePredicate observation) ∧
      S.currentGoal state = some contract.affectedGoal ∧
      S.goalOpen state contract.affectedGoal ∧
      S.goalObstructed state contract.affectedGoal ∧
      (¬ S.expired state contract.expiryOrRecheckPolicy) ∧
      ∃ observation,
        contract.wakePredicate observation ∧
        S.sourceOf observation = contract.observationSource ∧
        S.goalDependsOn state contract.affectedGoal observation ∧
        S.ruleApplies contract.invalidationRule observation
          contract.affectedGoal ∧
        EvidencePacketEffect S state observation contract.affectedGoal :=
  ⟨certificate.noSameEpochAdvance,
    contract.currentlyUnsatisfied,
    contract.currentGoalBinding,
    contract.affectedGoalOpen,
    contract.affectedGoalObstructed,
    certificate.notExpiredAtAdmission,
    await_has_nonempty_causal_wake certificate⟩

/-- Scheduler action after a no-observation poll. -/
inductive AwaitControl
  | suspendUntilObservation
  | retryImmediately
  deriving DecidableEq

/-- The exact non-Await range required when a wake has expired. -/
inductive WakeReclassification
  | ready
  | stuck
  | reepoch
  | halt
  deriving DecidableEq

/--
Disposition of the original contract at a checked state.  The Await constructor carries
fresh non-expiry evidence; the other four constructors are the exact reclassification
range.
-/
inductive WakeDisposition
    (S : WakeSystem) {origin : S.State}
    (checked : S.State) (contract : WakeContract S origin)
  | await
      (active : ¬ S.expired checked contract.expiryOrRecheckPolicy)
  | ready
  | stuck
  | reepoch
  | halt

namespace WakeDisposition

/-- `none` means Await; `some` is one of the four exact expired-wake outcomes. -/
def reclassification?
    {S : WakeSystem} {origin checked : S.State}
    {contract : WakeContract S origin} :
    WakeDisposition S checked contract → Option WakeReclassification
  | .await _ => none
  | .ready => some .ready
  | .stuck => some .stuck
  | .reepoch => some .reepoch
  | .halt => some .halt

/-- Executable anti-loop observation used by adversarial tests. -/
def awaitsAgain
    {S : WakeSystem} {origin checked : S.State}
    {contract : WakeContract S origin} :
    WakeDisposition S checked contract → Bool
  | .await _ => true
  | .ready => false
  | .stuck => false
  | .reepoch => false
  | .halt => false

end WakeDisposition

/-- One externally triggered poll of an existing Await contract. -/
structure AwaitPollResult
    (S : WakeSystem) {origin : S.State} (contract : WakeContract S origin) where
  state : S.State
  disposition : WakeDisposition S state contract
  emittedReceipts : List S.Receipt
  control : AwaitControl

/-- A no-observation poll returns the identical state and suspends externally. -/
def awaitWithoutObservation
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    AwaitPollResult S contract where
  state := state
  disposition := .await certificate.notExpiredAtAdmission
  emittedReceipts := []
  control := .suspendUntilObservation

/--
Repeated external no-observation polls.  This function records externally initiated
polls; it never schedules an immediate retry internally.
-/
def repeatAwaitWithoutObservation
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    Nat → List (AwaitPollResult S contract)
  | 0 => []
  | Nat.succ rechecks =>
      awaitWithoutObservation certificate ::
        repeatAwaitWithoutObservation certificate rechecks

/-- Explicit operational laws pinned for every no-observation result. -/
structure AwaitInert
    (S : WakeSystem) (origin : S.State) (contract : WakeContract S origin)
    (result : AwaitPollResult S contract) : Prop where
  stateUnchanged : result.state = origin
  measureUnchanged : S.measure result.state = S.measure origin
  historyUnchanged : S.history result.state = S.history origin
  goalUnchanged :
    ∀ goal, S.goalView result.state goal = S.goalView origin goal
  receiptLogUnchanged : S.receiptLog result.state = S.receiptLog origin
  emittedNoReceipt : result.emittedReceipts = []
  remainsAwait : result.disposition.awaitsAgain = true
  suspended : result.control = .suspendUntilObservation

/-- A single no-observation Await poll satisfies every explicit inertness law. -/
theorem await_without_observation_is_inert
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) :
    AwaitInert S state contract (awaitWithoutObservation certificate) := by
  exact {
    stateUnchanged := rfl
    measureUnchanged := rfl
    historyUnchanged := rfl
    goalUnchanged := fun _ => rfl
    receiptLogUnchanged := rfl
    emittedNoReceipt := rfl
    remainsAwait := rfl
    suspended := rfl
  }

/-- Every member of any finite sequence of external no-observation polls is inert. -/
theorem repeated_await_without_observation_is_inert
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) (rechecks : Nat) :
    ∀ result,
      result ∈ repeatAwaitWithoutObservation certificate rechecks →
        AwaitInert S state contract result := by
  induction rechecks with
  | zero =>
      intro result hmembership
      cases hmembership
  | succ rechecks inductionHypothesis =>
      intro result hmembership
      change result ∈
        awaitWithoutObservation certificate ::
          repeatAwaitWithoutObservation certificate rechecks at hmembership
      cases hmembership with
      | head =>
          exact await_without_observation_is_inert certificate
      | tail _ htail =>
          exact inductionHypothesis result htail

/-- In particular, no repeated no-observation poll requests an immediate retry. -/
theorem repeated_await_without_observation_does_not_busy_loop
    {S : WakeSystem} {state : S.State} {contract : WakeContract S state}
    (certificate : AwaitCertificate S state contract) (rechecks : Nat) :
    ∀ result,
      result ∈ repeatAwaitWithoutObservation certificate rechecks →
        result.control = .suspendUntilObservation := by
  intro result hmembership
  exact (repeated_await_without_observation_is_inert
    certificate rechecks result hmembership).suspended

/-- The sole expired-wake reclassification boundary; it has no Await branch. -/
def reclassifyExpired
    {S : WakeSystem} {origin checked : S.State}
    (contract : WakeContract S origin)
    (_hexpired : S.expired checked contract.expiryOrRecheckPolicy) :
    WakeReclassification → WakeDisposition S checked contract
  | .ready => .ready
  | .stuck => .stuck
  | .reepoch => .reepoch
  | .halt => .halt

/--
At an expired checked state, the Await constructor is contradictory; every legal
disposition therefore has exactly one of the four reclassification kinds.
-/
theorem expired_wake_must_reclassify
    {S : WakeSystem} {origin checked : S.State}
    (contract : WakeContract S origin)
    (hexpired : S.expired checked contract.expiryOrRecheckPolicy)
    (disposition : WakeDisposition S checked contract) :
    ∃ classification : WakeReclassification,
      disposition.reclassification? = some classification := by
  cases disposition with
  | await active =>
      exact False.elim (active hexpired)
  | ready =>
      exact ⟨.ready, rfl⟩
  | stuck =>
      exact ⟨.stuck, rfl⟩
  | reepoch =>
      exact ⟨.reepoch, rfl⟩
  | halt =>
      exact ⟨.halt, rfl⟩

/-- An expired wake cannot legally return Await again. -/
theorem expired_wake_cannot_await_again
    {S : WakeSystem} {origin checked : S.State}
    (contract : WakeContract S origin)
    (hexpired : S.expired checked contract.expiryOrRecheckPolicy)
    (disposition : WakeDisposition S checked contract) :
    disposition.awaitsAgain = false := by
  cases disposition with
  | await active =>
      exact False.elim (active hexpired)
  | ready =>
      rfl
  | stuck =>
      rfl
  | reepoch =>
      rfl
  | halt =>
      rfl

end Residua.RCC

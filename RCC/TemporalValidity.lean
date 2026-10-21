/-!
# RCC-29 Temporal Judgment Validity

Historical validity, current usability, and successor-epoch transportability
are different predicates.  A typed revocation preserves the historical receipt
while forcing every declared dependent judgment to revalidate, transport with
a certificate, or reopen.

The dependency relation consumed here is supplied as already dependency-closed.
This kernel makes no completeness claim about any repository dependency
extractor.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or custom assumptions.
The cascade/state theorems use Lean's `propext` exactly where reported by
`#print axioms`; the historical-receipt preservation theorem has no additional
assumptions.
-/

namespace Residua.RCC.TemporalValidity

universe u

/-- The role of a revocation target is part of its typed identity. -/
inductive RevocationTargetKind where
  | assumption
  | evidence
  | implementationBinding
  | authority
  | kernel
  deriving DecidableEq, Repr

/-- A revocation target combines its domain-local identity with its role. -/
structure TargetRef (TargetQ : Type u) where
  q : TargetQ
  kind : RevocationTargetKind
  deriving DecidableEq, Repr

/-- Current authority is not the same object as immutable historical validity. -/
inductive CurrentJudgmentState (Judgment : Type u) where
  | usable
  | revalidate
  | transported (replacement : Judgment)
  | reopened
  deriving DecidableEq, Repr

/--
The temporal kernel consumes an explicitly supplied dependency relation and an
explicit successor-epoch transport relation.
-/
structure TemporalValiditySystem where
  TargetQ : Type u
  Judgment : Type u
  Window : Type u
  Epoch : Type u
  Authority : Type u
  Receipt : Type u
  ReasonQ : Type u
  dependsOn : Judgment → TargetRef TargetQ → Prop
  dependsOnDecidable :
    (judgment : Judgment) → (target : TargetRef TargetQ) →
      Decidable (dependsOn judgment target)
  authorized : Authority → TargetRef TargetQ → Window → Prop
  effectiveAt : Window → Window → Prop
  transportable : Judgment → Judgment → Epoch → Epoch → Prop
  /--
  A successor judgment must describe the replacement target named by the
  revocation event.  Transportability across epochs alone is insufficient.
  -/
  replacementJudgmentFor : TargetRef TargetQ → Judgment → Prop

/-- Historical receipts and current authority are deliberately separate fields. -/
structure TemporalSnapshot (S : TemporalValiditySystem) where
  epoch : S.Epoch
  window : S.Window
  historicalReceipt : S.Judgment → S.Window → Option S.Receipt
  currentState : S.Judgment → CurrentJudgmentState S.Judgment

/-- Immutable fact that one receipt was admitted for a judgment at an old window. -/
def ValidAt {S : TemporalValiditySystem} (snapshot : TemporalSnapshot S)
    (judgment : S.Judgment) (window : S.Window) (receipt : S.Receipt) : Prop :=
  snapshot.historicalReceipt judgment window = some receipt

/-- Current permission to rely on a judgment at this snapshot. -/
def UsableAt {S : TemporalValiditySystem} (snapshot : TemporalSnapshot S)
    (judgment : S.Judgment) : Prop :=
  snapshot.currentState judgment = .usable

/-- Proof relation for carrying a judgment into a successor epoch. -/
def Transportable (S : TemporalValiditySystem)
    (judgment replacement : S.Judgment)
    (source successor : S.Epoch) : Prop :=
  S.transportable judgment replacement source successor

/--
A transported current-state marker is sound only when the original judgment
has an explicit proof for the source and successor epochs.  Non-transport
states impose no transport claim.
-/
def TransportStateSound (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (successorEpoch : S.Epoch)
    (judgment : S.Judgment) :
    CurrentJudgmentState S.Judgment → Prop
  | .transported replacement =>
      Transportable S judgment replacement snapshot.epoch successorEpoch
  | _ => True

/-- Proof-carrying, effective revocation event. -/
structure Revoke (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S) where
  target : TargetRef S.TargetQ
  effectiveWindow : S.Window
  reasonQ : S.ReasonQ
  authority : S.Authority
  replacement : Option (TargetRef S.TargetQ)
  authorityProof : S.authorized authority target effectiveWindow
  effectiveProof : S.effectiveAt effectiveWindow snapshot.window

/--
Every declared dependency must be dispositioned.  Transport additionally
requires both a replacement target named by the event and an explicit
successor-epoch transport certificate.
-/
inductive CascadeDisposition
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (judgment : S.Judgment) where
  | revalidate
  | transport
      (replacementTarget : TargetRef S.TargetQ)
      (replacementMatches : event.replacement = some replacementTarget)
      (replacementJudgment : S.Judgment)
      (replacementBinding :
        S.replacementJudgmentFor replacementTarget replacementJudgment)
      (certificate :
        S.transportable judgment replacementJudgment
          snapshot.epoch successorEpoch)
  | reopen

/-- Pointwise disposition for every judgment declared dependent on the target. -/
structure CascadePlan
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch) where
  resolve :
    (judgment : S.Judgment) →
      S.dependsOn judgment event.target →
        CascadeDisposition S snapshot event successorEpoch judgment

/-- The three lawful non-usable outcomes of a revocation cascade. -/
def RequiresRevalidationTransportOrReopen {Judgment : Type u} :
    CurrentJudgmentState Judgment → Prop
  | .usable => False
  | .revalidate => True
  | .transported _ => True
  | .reopened => True

/--
Apply one effective revocation.  Historical receipts, epoch, and current window
are copied definitionally.  Only declared dependents change current authority.
-/
def applyRevoke
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch) :
    TemporalSnapshot S where
  epoch := snapshot.epoch
  window := snapshot.window
  historicalReceipt := snapshot.historicalReceipt
  currentState := fun judgment =>
    letI : Decidable (S.dependsOn judgment event.target) :=
      S.dependsOnDecidable judgment event.target
    if hdep : S.dependsOn judgment event.target then
      match plan.resolve judgment hdep with
      | .revalidate => .revalidate
      | .transport _ _ replacementJudgment _ _ =>
          .transported replacementJudgment
      | .reopen => .reopened
    else
      snapshot.currentState judgment

/-- Revocation does not alter any historical receipt lookup. -/
theorem revoke_preserves_historical_receipt
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (window : S.Window) :
    (applyRevoke S snapshot event successorEpoch plan).historicalReceipt
        judgment window =
      snapshot.historicalReceipt judgment window := by
  rfl

/-- Historical `ValidAt` is invariant under a current revocation. -/
theorem revoke_preserves_valid_at
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (window : S.Window)
    (receipt : S.Receipt) :
    ValidAt (applyRevoke S snapshot event successorEpoch plan)
        judgment window receipt ↔
      ValidAt snapshot judgment window receipt := by
  rfl

/-- Every declared dependent enters one of the three required dispositions. -/
theorem dependent_judgment_requires_resolution
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hdep : S.dependsOn judgment event.target) :
    RequiresRevalidationTransportOrReopen
      ((applyRevoke S snapshot event successorEpoch plan).currentState judgment) := by
  cases hresolution : plan.resolve judgment hdep <;>
    simp [applyRevoke, hdep, hresolution,
      RequiresRevalidationTransportOrReopen]

/-- In particular, a declared dependent cannot retain stale current authority. -/
theorem dependent_judgment_not_usable_after_revoke
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hdep : S.dependsOn judgment event.target) :
    ¬ UsableAt (applyRevoke S snapshot event successorEpoch plan) judgment := by
  intro husable
  have hresolved :=
    dependent_judgment_requires_resolution
      S snapshot event successorEpoch plan judgment hdep
  change
    (applyRevoke S snapshot event successorEpoch plan).currentState judgment =
      .usable at husable
  rw [husable] at hresolved
  exact hresolved

/-- A lawful cascade never manufactures a transport marker without its proof. -/
theorem dependent_judgment_transport_sound
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hdep : S.dependsOn judgment event.target) :
    TransportStateSound S snapshot successorEpoch judgment
      ((applyRevoke S snapshot event successorEpoch plan).currentState
        judgment) := by
  cases hresolution : plan.resolve judgment hdep with
  | revalidate =>
      simp [applyRevoke, hdep, hresolution, TransportStateSound]
  | transport replacementTarget replacementMatches replacementJudgment
      replacementBinding certificate =>
      simpa [applyRevoke, hdep, hresolution, TransportStateSound, Transportable]
        using certificate
  | reopen =>
      simp [applyRevoke, hdep, hresolution, TransportStateSound]

/-- Revoking one target leaves an unrelated judgment's current state unchanged. -/
theorem unrelated_judgment_state_preserved
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hnot : ¬ S.dependsOn judgment event.target) :
    (applyRevoke S snapshot event successorEpoch plan).currentState judgment =
      snapshot.currentState judgment := by
  simp [applyRevoke, hnot]

/-- The transport branch exposes the exact proof required by the system relation. -/
theorem transport_disposition_has_certificate
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (judgment replacementJudgment : S.Judgment)
    (replacementTarget : TargetRef S.TargetQ)
    (replacementMatches : event.replacement = some replacementTarget)
    (replacementBinding :
      S.replacementJudgmentFor replacementTarget replacementJudgment)
    (certificate :
      S.transportable judgment replacementJudgment
        snapshot.epoch successorEpoch) :
    event.replacement = some replacementTarget ∧
      S.replacementJudgmentFor replacementTarget replacementJudgment ∧
      Transportable S judgment replacementJudgment
        snapshot.epoch successorEpoch :=
  ⟨replacementMatches, replacementBinding, certificate⟩

/--
Whenever a declared dependent is transported, the current replacement
judgment is tied to the exact replacement target named by the revocation
event.  This prevents a valid epoch-transport proof from being attached to an
unrelated target.
-/
theorem dependent_judgment_transport_target_sound
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch)
    (judgment : S.Judgment)
    (hdep : S.dependsOn judgment event.target) :
    match
      (applyRevoke S snapshot event successorEpoch plan).currentState judgment
    with
    | .transported replacementJudgment =>
        ∃ replacementTarget,
          event.replacement = some replacementTarget ∧
          S.replacementJudgmentFor replacementTarget replacementJudgment
    | _ => True := by
  cases hresolution : plan.resolve judgment hdep with
  | revalidate =>
      simp [applyRevoke, hdep, hresolution]
  | transport replacementTarget replacementMatches replacementJudgment
      replacementBinding certificate =>
      simp only [applyRevoke, hdep, hresolution]
      exact ⟨replacementTarget, replacementMatches, replacementBinding⟩
  | reopen =>
      simp [applyRevoke, hdep, hresolution]

/--
RCC-29 headline: one cascade preserves every historical `ValidAt` judgment,
removes current usability from every declared dependent, proves every
transport marker and its exact event replacement target, and preserves every
nondependent current state.
-/
theorem CascadePlan.sound
    (S : TemporalValiditySystem)
    (snapshot : TemporalSnapshot S)
    (event : Revoke S snapshot)
    (successorEpoch : S.Epoch)
    (plan : CascadePlan S snapshot event successorEpoch) :
    (∀ judgment window receipt,
      ValidAt (applyRevoke S snapshot event successorEpoch plan)
          judgment window receipt ↔
        ValidAt snapshot judgment window receipt) ∧
      (∀ judgment, S.dependsOn judgment event.target →
        (¬ UsableAt
          (applyRevoke S snapshot event successorEpoch plan) judgment) ∧
        TransportStateSound S snapshot successorEpoch judgment
          ((applyRevoke S snapshot event successorEpoch plan).currentState
            judgment) ∧
        match
          (applyRevoke S snapshot event successorEpoch plan).currentState
            judgment
        with
        | .transported replacementJudgment =>
            ∃ replacementTarget,
              event.replacement = some replacementTarget ∧
              S.replacementJudgmentFor
                replacementTarget replacementJudgment
        | _ => True) ∧
      (∀ judgment, ¬ S.dependsOn judgment event.target →
        (applyRevoke S snapshot event successorEpoch plan).currentState
            judgment =
          snapshot.currentState judgment) := by
  refine ⟨?_, ?_, ?_⟩
  · intro judgment window receipt
    exact revoke_preserves_valid_at
      S snapshot event successorEpoch plan judgment window receipt
  · intro judgment dependent
    exact
      ⟨dependent_judgment_not_usable_after_revoke
          S snapshot event successorEpoch plan judgment dependent,
        dependent_judgment_transport_sound
          S snapshot event successorEpoch plan judgment dependent,
        dependent_judgment_transport_target_sound
          S snapshot event successorEpoch plan judgment dependent⟩
  · intro judgment independent
    exact unrelated_judgment_state_preserved
      S snapshot event successorEpoch plan judgment independent

end Residua.RCC.TemporalValidity

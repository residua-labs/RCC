import RCC.FormalCore

/-!
# RCC proof-carrying outcomes

`ResiduaRCCFormalCore` freezes the four final branch tags, but its compatibility
surface stores reepoch and halt explanations as strings.  This module supplies
the stronger execution carrier needed by a closure capstone:

* every final branch carries a domain certificate;
* every internal advance carries a domain transition certificate and a strict
  measure decrease;
* branch selection is the single common decision tree;
* normalization recurses only through certified advances; and
* the induced `CoreObject` has exactly the packet-derived closed states as its
  fixed points.

The certificate types remain parameters so individual RCC instances can use
their existing admission, migration, wake, and terminal-failure kernels.  A
capstone must instantiate them with those concrete indexed certificates, not
with strings or packet-local booleans.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.ProofCarryingOutcome

open Residua.RCC

universe u a c w m h

/-- One certified internal successor, including its structural decrease. -/
structure CertifiedAdvance
    (State : Type u)
    (measure : State → Nat)
    (AdvancePacket : State → State → Type a)
    (state : State) where
  next : State
  certificate : AdvancePacket state next
  decreases : measure next < measure state

/--
The proof-carrying branch vocabulary for one executable RCC instance.

The readers are ordinary total Lean functions.  They return either an indexed
certificate or `none`; there is no caller-supplied final branch tag.
-/
structure BranchSystem where
  State : Type u
  measure : State → Nat

  ClosedPacket : State → Type c
  AdvancePacket : State → State → Type a
  WakePacket : State → Type w
  MigrationPacket : State → Type m
  HaltPacket : State → Type h

  closedAt :
    (state : State) → Option (ClosedPacket state)
  advanceAt :
    (state : State) →
      Option (CertifiedAdvance State measure AdvancePacket state)
  wakeAt :
    (state : State) → Option (WakePacket state)
  migrationAt :
    (state : State) → Option (MigrationPacket state)
  haltAt :
    (state : State) → HaltPacket state

/-- One common open-state decision tree. -/
inductive OpenOutcome
    (K : BranchSystem) (state : K.State) where
  | advanced
      (next : K.State)
      (certificate : K.AdvancePacket state next)
      (decreases : K.measure next < K.measure state)
  | await
      (certificate : K.WakePacket state)
  | reepoch
      (certificate : K.MigrationPacket state)
  | halt
      (certificate : K.HaltPacket state)

/--
Only the common derivation selects a branch.  The priority is fixed:
`Advanced > Await > Reepoch > Halt`.
-/
def deriveOpen (K : BranchSystem) (state : K.State) :
    OpenOutcome K state :=
  match K.advanceAt state with
  | some next =>
      .advanced next.next next.certificate next.decreases
  | none =>
      match K.wakeAt state with
      | some wake => .await wake
      | none =>
          match K.migrationAt state with
          | some migration => .reepoch migration
          | none => .halt (K.haltAt state)

/-- The four externally visible outcomes, all proof-carrying. -/
inductive NormalizeOutcome (K : BranchSystem) where
  | closed
      (state : K.State)
      (certificate : K.ClosedPacket state)
  | await
      (state : K.State)
      (certificate : K.WakePacket state)
  | reepoch
      (state : K.State)
      (certificate : K.MigrationPacket state)
  | halt
      (state : K.State)
      (certificate : K.HaltPacket state)

namespace NormalizeOutcome

/-- Only a genuinely certified closed result contributes a successor state. -/
def closedState? {K : BranchSystem} :
    NormalizeOutcome K → Option K.State
  | .closed state _ => some state
  | .await _ _ => none
  | .reepoch _ _ => none
  | .halt _ _ => none

end NormalizeOutcome

/--
Well-founded same-epoch normalization.  No external branch recurses.
-/
def normalize (K : BranchSystem) (state : K.State) :
    NormalizeOutcome K :=
  match K.closedAt state with
  | some closed => .closed state closed
  | none =>
      match deriveOpen K state with
      | .advanced next _ _decreases =>
          normalize K next
      | .await wake =>
          .await state wake
      | .reepoch migration =>
          .reepoch state migration
      | .halt residue =>
          .halt state residue
termination_by K.measure state
decreasing_by exact _decreases

/-- A selected advance exposes its indexed transition certificate. -/
theorem deriveOpen_advanced_certificate
    (K : BranchSystem)
    (state next : K.State)
    (certificate : K.AdvancePacket state next)
    (decreases : K.measure next < K.measure state)
    (_selected :
      deriveOpen K state = .advanced next certificate decreases) :
    Nonempty (K.AdvancePacket state next) :=
  ⟨certificate⟩

/-- A selected reepoch exposes its migration certificate, never a reason string. -/
theorem deriveOpen_reepoch_certificate
    (K : BranchSystem)
    (state : K.State)
    (certificate : K.MigrationPacket state)
    (_selected : deriveOpen K state = .reepoch certificate) :
    Nonempty (K.MigrationPacket state) :=
  ⟨certificate⟩

/-- A selected halt exposes its terminal failure certificate. -/
theorem deriveOpen_halt_certificate
    (K : BranchSystem)
    (state : K.State)
    (certificate : K.HaltPacket state)
    (_selected : deriveOpen K state = .halt certificate) :
    Nonempty (K.HaltPacket state) :=
  ⟨certificate⟩

/--
The closed reader is exact when every semantically available closed packet is
returned.  Soundness is inherent in the dependent codomain of `closedAt`.
-/
structure ClosedReaderComplete (K : BranchSystem) : Prop where
  complete :
    ∀ state,
      Nonempty (K.ClosedPacket state) →
        ∃ certificate, K.closedAt state = some certificate

/--
Exactness of every optional branch reader.  This is the closed-world premise
that prevents a reader from hiding a lawful higher-priority continuation and
thereby selecting Await, Reepoch, or Halt too early.
-/
structure BranchReadersComplete (K : BranchSystem) : Prop where
  closed : ClosedReaderComplete K
  advance :
    ∀ state,
      Nonempty
          (CertifiedAdvance K.State K.measure K.AdvancePacket state) →
        ∃ certificate, K.advanceAt state = some certificate
  wake :
    ∀ state,
      Nonempty (K.WakePacket state) →
        ∃ certificate, K.wakeAt state = some certificate
  migration :
    ∀ state,
      Nonempty (K.MigrationPacket state) →
        ∃ certificate, K.migrationAt state = some certificate

/-- An Await selection proves that no certified same-epoch advance exists. -/
theorem await_excludes_hidden_advance
    (K : BranchSystem)
    (readers : BranchReadersComplete K)
    (state : K.State)
    (wake : K.WakePacket state)
    (selected : deriveOpen K state = .await wake) :
    ¬ Nonempty
        (CertifiedAdvance K.State K.measure K.AdvancePacket state) := by
  intro hidden
  obtain ⟨certificate, found⟩ := readers.advance state hidden
  simp [deriveOpen, found] at selected

/--
A Reepoch selection proves both that no same-epoch advance and no wake packet
exist in the exact reader universes.
-/
theorem reepoch_excludes_hidden_higher_priority
    (K : BranchSystem)
    (readers : BranchReadersComplete K)
    (state : K.State)
    (migration : K.MigrationPacket state)
    (selected : deriveOpen K state = .reepoch migration) :
    (¬ Nonempty
        (CertifiedAdvance K.State K.measure K.AdvancePacket state)) ∧
      ¬ Nonempty (K.WakePacket state) := by
  constructor
  · intro hidden
    obtain ⟨certificate, found⟩ := readers.advance state hidden
    simp [deriveOpen, found] at selected
  · intro hidden
    obtain ⟨certificate, found⟩ := readers.wake state hidden
    cases advanceFound : K.advanceAt state with
    | some advance =>
        simp [deriveOpen, advanceFound] at selected
    | none =>
        simp [deriveOpen, advanceFound, found] at selected

/--
A Halt selection is the exact remainder: no advance, wake, or migration packet
exists in the corresponding sealed reader universes.
-/
theorem halt_excludes_hidden_continuation
    (K : BranchSystem)
    (readers : BranchReadersComplete K)
    (state : K.State)
    (failure : K.HaltPacket state)
    (selected : deriveOpen K state = .halt failure) :
    (¬ Nonempty
        (CertifiedAdvance K.State K.measure K.AdvancePacket state)) ∧
      (¬ Nonempty (K.WakePacket state)) ∧
      ¬ Nonempty (K.MigrationPacket state) := by
  constructor
  · intro hidden
    obtain ⟨certificate, found⟩ := readers.advance state hidden
    simp [deriveOpen, found] at selected
  · constructor
    · intro hidden
      obtain ⟨certificate, found⟩ := readers.wake state hidden
      cases advanceFound : K.advanceAt state with
      | some advance =>
          simp [deriveOpen, advanceFound] at selected
      | none =>
          simp [deriveOpen, advanceFound, found] at selected
    · intro hidden
      obtain ⟨certificate, found⟩ := readers.migration state hidden
      cases advanceFound : K.advanceAt state with
      | some advance =>
          simp [deriveOpen, advanceFound] at selected
      | none =>
          cases wakeFound : K.wakeAt state with
          | some wake =>
              simp [deriveOpen, advanceFound, wakeFound] at selected
          | none =>
              simp [deriveOpen, advanceFound, wakeFound, found] at selected

/-- A closed packet makes normalization stop at the same state. -/
theorem normalize_of_closed
    (K : BranchSystem)
    (reader : ClosedReaderComplete K)
    (state : K.State)
    (closed : Nonempty (K.ClosedPacket state)) :
    ∃ certificate,
      normalize K state = .closed state certificate := by
  obtain ⟨certificate, found⟩ := reader.complete state closed
  refine ⟨certificate, ?_⟩
  rw [normalize]
  simp only [found]

/--
The proof-carrying normalizer induces the same minimal CoreObject shape as the
compatibility core.  Await, reepoch, and halt do not create `D` edges.
-/
def coreObject (K : BranchSystem) : CoreObject where
  Ext := K.State
  Adm := fun state => Nonempty (K.ClosedPacket state)
  D := fun state target =>
    (normalize K state).closedState? = some target
  singleValued := by
    intro state left right leftFound rightFound
    have same :
        (some left : Option K.State) = some right :=
      leftFound.symm.trans rightFound
    exact Option.some.inj same

/-- Any normalizer fixed point carries a genuine closed packet. -/
theorem core_sound
    (K : BranchSystem)
    (state : K.State) :
    (coreObject K).D state state →
      (coreObject K).Adm state := by
  intro fixed
  change (normalize K state).closedState? = some state at fixed
  change Nonempty (K.ClosedPacket state)
  cases result : normalize K state with
  | closed target certificate =>
      simp [NormalizeOutcome.closedState?, result] at fixed
      subst target
      exact ⟨certificate⟩
  | await target certificate =>
      simp [NormalizeOutcome.closedState?, result] at fixed
  | reepoch target certificate =>
      simp [NormalizeOutcome.closedState?, result] at fixed
  | halt target certificate =>
      simp [NormalizeOutcome.closedState?, result] at fixed

/-- Every closed state is a normalizer fixed point. -/
theorem core_complete
    (K : BranchSystem)
    (reader : ClosedReaderComplete K)
    (state : K.State) :
    (coreObject K).Adm state →
      (coreObject K).D state state := by
  intro admitted
  change Nonempty (K.ClosedPacket state) at admitted
  change (normalize K state).closedState? = some state
  obtain ⟨certificate, normalized⟩ :=
    normalize_of_closed K reader state admitted
  rw [normalized]
  rfl

/-- Fixed points are exactly packet-derived closed states. -/
theorem core_exact
    (K : BranchSystem)
    (reader : ClosedReaderComplete K) :
    (coreObject K).Exact := by
  intro state
  exact
    ⟨core_sound K state,
      core_complete K reader state⟩

end Residua.RCC.ProofCarryingOutcome

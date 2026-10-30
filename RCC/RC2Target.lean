import RCC.FormalCore

/-!
# ResiduaRCCRC2Target — RC-2: diagnostic completeness

Obligation RC-2: *"A diagnostic completeness theorem: every non-closed run
yields a diagnostic."*

The verdict machine is `Residua.RCC.normalize` over an `Exec`.  Its result
type already forces every non-closed run to carry a residue; the load-bearing
content this module proves is that the residue is **genuine**:

* `normalize_await_terminal` / `normalize_reepoch_terminal` /
  `normalize_halt_terminal` — the state `st` carried by a residue result is a
  truly-open terminal state of the run (`¬ E.closed st`), and its stepper
  emits exactly the residue the surface reports
  (`E.stepOpen st hopen = .await/.reepoch/.halt kind`).  A caller cannot
  invent a message or attach a diagnostic to a state the machine never
  reached: the equality pins the diagnostic to the stepper's own output.
* `normalize_nonclosed_yields_diagnostic` — completeness itself: every
  normalize run either closes (with the reached state's closed proof) or
  yields a terminal diagnostic of one of the three named kinds.
* `closed_state_never_diagnosed` — the type-level tooth: `stepOpen` is only
  callable on open states, so no diagnostic can be manufactured for a closed
  state.

Positive fixture: `fixtureExec` halts out of fuel and reports the *named*
residue at the *reached* state.  Discriminating tooth:
`foreign_diagnostic_rejected` pins the reported string to `stepOpen`'s own
output, so a fabricated wake cannot satisfy the terminal equality.
-/

namespace Residua.RCC.RC2

open Residua.RCC

/-! ## The terminal-diagnostic invariant -/

/--
Every `Await` result the normalizer returns is the stepper's own diagnostic at
a genuinely-open terminal state: `¬ closed st`, and `stepOpen st` is exactly
`.await kind`.  Induction on the state's measure.
-/
theorem normalize_await_terminal (E : Exec) (s : E.State)
    {st : E.State} {w : String}
    (h : normalize E s = .await st w) :
    ∃ hopen : ¬ E.closed st, E.stepOpen st hopen = .await w := by
  generalize hn : E.measure s = n
  induction n using Nat.strongRecOn generalizing s
  next n ih =>
    rw [normalize] at h
    split at h
    · exact nomatch h
    · rename_i hclosed
      split at h
      · rename_i next dec heq
        exact ih (E.measure next) (hn ▸ dec) next h rfl
      · rename_i heq
        injection h with hst hw
        subst hst; subst hw
        exact ⟨hclosed, heq⟩
      · exact nomatch h
      · exact nomatch h

/-- Same invariant for the `Reepoch` residue. -/
theorem normalize_reepoch_terminal (E : Exec) (s : E.State)
    {st : E.State} {w : String}
    (h : normalize E s = .reepoch st w) :
    ∃ hopen : ¬ E.closed st, E.stepOpen st hopen = .reepoch w := by
  generalize hn : E.measure s = n
  induction n using Nat.strongRecOn generalizing s
  next n ih =>
    rw [normalize] at h
    split at h
    · exact nomatch h
    · rename_i hclosed
      split at h
      · rename_i next dec heq
        exact ih (E.measure next) (hn ▸ dec) next h rfl
      · exact nomatch h
      · rename_i heq
        injection h with hst hw
        subst hst; subst hw
        exact ⟨hclosed, heq⟩
      · exact nomatch h

/-- Same invariant for the `Halt` residue. -/
theorem normalize_halt_terminal (E : Exec) (s : E.State)
    {st : E.State} {w : String}
    (h : normalize E s = .halt st w) :
    ∃ hopen : ¬ E.closed st, E.stepOpen st hopen = .halt w := by
  generalize hn : E.measure s = n
  induction n using Nat.strongRecOn generalizing s
  next n ih =>
    rw [normalize] at h
    split at h
    · exact nomatch h
    · rename_i hclosed
      split at h
      · rename_i next dec heq
        exact ih (E.measure next) (hn ▸ dec) next h rfl
      · exact nomatch h
      · exact nomatch h
      · rename_i heq
        injection h with hst hw
        subst hst; subst hw
        exact ⟨hclosed, heq⟩

/-! ## Completeness -/

/-- A terminal diagnostic: the reached open state, the named residue kind, and
the equality pinning the surface message to the stepper's own output. -/
structure TerminalDiagnostic (E : Exec) where
  state : E.State
  open_ : ¬ E.closed state
  kind : String
  stepIsDiagnostic :
    E.stepOpen state open_ = .await kind ∨
    E.stepOpen state open_ = .reepoch kind ∨
    E.stepOpen state open_ = .halt kind

/-- **RC-2 diagnostic completeness.** Every normalize run either closes — the
result carries the reached state's closed proof — or yields a terminal
diagnostic: an open state whose stepper emitted exactly the residue reported. -/
theorem normalize_nonclosed_yields_diagnostic (E : Exec) (s : E.State) :
    (∃ st pf, normalize E s = .closed st pf ∧ E.closed st) ∨
      ∃ diag : TerminalDiagnostic E,
        normalize E s = .await diag.state diag.kind ∨
        normalize E s = .reepoch diag.state diag.kind ∨
        normalize E s = .halt diag.state diag.kind := by
  cases h : normalize E s with
  | closed st pf =>
      exact Or.inl ⟨st, pf, rfl, pf⟩
  | await st w =>
      obtain ⟨hopen, hstep⟩ := normalize_await_terminal E s h
      exact Or.inr ⟨⟨st, hopen, w, Or.inl hstep⟩, Or.inl rfl⟩
  | reepoch st w =>
      obtain ⟨hopen, hstep⟩ := normalize_reepoch_terminal E s h
      exact Or.inr ⟨⟨st, hopen, w, Or.inr (Or.inl hstep)⟩, Or.inr (Or.inl rfl)⟩
  | halt st w =>
      obtain ⟨hopen, hstep⟩ := normalize_halt_terminal E s h
      exact Or.inr ⟨⟨st, hopen, w, Or.inr (Or.inr hstep)⟩, Or.inr (Or.inr rfl)⟩

/-- A closed state never reaches a diagnostic branch: `normalize` returns the
`Closed` proof payload, not a residue. -/
theorem closed_state_never_diagnosed (E : Exec) (s : E.State)
    (hclosed : E.closed s) :
    normalize E s = .closed s hclosed := by
  rw [normalize]
  simp only [hclosed, ↓reduceDIte]

/-! ## Concrete fixture and the fabrication refusal -/

/-- The smallest honest run: a counter that must reach 0; at 1 the stepper
halts with a named residue instead of manufacturing progress. -/
def fixtureExec : Exec where
  State := Nat
  measure := id
  closed := fun n => n = 0
  closedDecidable := fun n => inferInstanceAs (Decidable (n = 0))
  stepOpen := fun n _ =>
    if n ≤ 1 then .halt "fuel-exhausted-at-one"
    else .advanced (n - 1) (show n - 1 < n by omega)

/-- One unfold step specialized to a halting stepper: if the current open
state's stepper halts with residue `w`, `normalize` reports `.halt s w`. -/
theorem normalize_halt_of_stepOpen_halt (E : Exec) (s : E.State) (w : String)
    (hopen : ¬ E.closed s) (hstep : E.stepOpen s hopen = .halt w) :
    normalize E s = .halt s w := by
  rw [normalize, dif_neg hopen, hstep]

/-- The fixture run halts at state 1 with the named residue. -/
theorem fixture_run_halts :
    normalize fixtureExec (1 : Nat) =
      .halt (1 : Nat) "fuel-exhausted-at-one" :=
  normalize_halt_of_stepOpen_halt fixtureExec (1 : Nat)
    "fuel-exhausted-at-one" (show ¬ (1 : Nat) = 0 by decide) rfl

/-- The non-closed run yields exactly the named terminal diagnostic. -/
theorem fixture_diagnostic_is_terminal :
    ∃ diag : TerminalDiagnostic fixtureExec,
      normalize fixtureExec (1 : Nat) = .halt diag.state diag.kind := by
  obtain ⟨hopen, hstep⟩ :=
    normalize_halt_terminal fixtureExec _ fixture_run_halts
  exact
    ⟨⟨(1 : Nat), hopen, "fuel-exhausted-at-one", Or.inr (Or.inr hstep)⟩,
      fixture_run_halts⟩

/-- The discriminating tooth: any `Halt` residue this exec reports is the
stepper's own string at the reached open state — a caller cannot attribute a
foreign diagnostic. -/
theorem foreign_diagnostic_rejected :
    ∀ st w, normalize fixtureExec (1 : Nat) = .halt st w →
      st = (1 : Nat) ∧ w = "fuel-exhausted-at-one" := by
  intro st w h
  have hrun := fixture_run_halts
  have := hrun.symm.trans h
  injection this with hst hw
  exact ⟨hst.symm, hw.symm⟩

#print axioms normalize_await_terminal
#print axioms normalize_reepoch_terminal
#print axioms normalize_halt_terminal
#print axioms normalize_nonclosed_yields_diagnostic
#print axioms closed_state_never_diagnosed
#print axioms normalize_halt_of_stepOpen_halt
#print axioms fixture_run_halts
#print axioms fixture_diagnostic_is_terminal
#print axioms foreign_diagnostic_rejected

# RCC self-closure — class C: FC-3 and RC-2 discharged (devin-fcd, 2026-10-29)

`closure_claim = 0`. Draft. Stacked on class B (#8297).

Class C of the work order: the two genuinely-missing obligations, stated as
exact Lean contracts first, then proved. No remainder, no boundary residue —
both closed. Two new target modules; additive registry entries only.

## FC-3 — `lean/algorithms/ResiduaRCCFC3Target.lean`

*"Deletion countermodels establish necessity of every load-bearing facet."*

- `CoherentLaws world` — the joint bundle of all seven law surfaces a
  certificate draws from; `FacetNecessaryAt world := ¬ Nonempty (bundle)`.
- Eight concrete **deletion worlds**, one per `RCCFacet`, each breaking
  exactly its law surface while the others stay vacuously true (the deleted
  facet is the sole break — minimal countermodel):
  `addressKernel→addressSound` collision, `noetherianReduction→
  reductionCongruent` nondeterminism, `groundedEvidence→admittedGrounded`
  ungrounded admission, `reflectionStrata` same-level verifier,
  `runtimeBinding` unrefined step, `lineageCoalgebra` uncarried token,
  `compositionKernel` severed glue.
- Honest shape for `resourceLedger`: its world-law is vacuous without
  reductions, so the witness lives at delta level
  (`forged_delta_is_no_ledger_proof`) plus the existing
  `missing_resource_delta_mutant_cannot_certify`; the FC-1 origin's
  countermodel is `differentPairSnapshotsCannotBind` (cited).
- `facetNecessity : ∀ f, Σ' residue : Prop, residue` — total by match;
  `every_loadBearing_facet_necessary`; positive tooth
  `vacuous_world_coherent`.
- Axioms: all `∅` or `{propext}` (`raw/rcc_evidence_c/fc3_axioms.txt`).

## RC-2 — `lean/algorithms/ResiduaRCCRC2Target.lean`

*"Every non-closed run yields a diagnostic."*

- `normalize_{await,reepoch,halt}_terminal` (measure induction): the carried
  state is genuinely open and `stepOpen` emits exactly the reported residue —
  the diagnostic is the machine's own output, never caller-supplied.
- `normalize_nonclosed_yields_diagnostic`: every run is `Closed` (with the
  reached state's proof) or a `TerminalDiagnostic` — the completeness theorem.
- `closed_state_never_diagnosed`: `stepOpen` is only callable on open states —
  no diagnostic can be manufactured for a closed state.
- Site: `fixtureExec` + `fixture_run_halts` (positive);
  `foreign_diagnostic_rejected` (fabricated wakes fail the terminal equality).
- Axioms: `∅` or `{propext, Quot.sound}` (`raw/rcc_evidence_c/rc2_axioms.txt`).

## Verdict delta (the executable, never asserted)

| Reading | class B | **after C** |
|---|---|---|
| literal | 10 open | **8 open** — exactly the 8 named gaps |
| strict | 11 open | **9 open** — gaps + R1 |

`raw/rcc_evidence_c/` has coverage, both graphs, the verdict text, axiom dumps.
Remaining: 8 named gaps (class D), R1 (class E).

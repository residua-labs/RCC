# RCC — Relative Closure Calculus

**English** · [中文](README.zh-CN.md)

**"Done" should be computed, not claimed.** RCC decides, for one frozen epoch, whether a body of work is *closed relative to* an admitted intent and context. When it is not, RCC says exactly which kind of not-closed it is.

## Why

Projects routinely declare things finished: "the proof is complete", "CI is green", "all targets discharged". Each of those is an assertion, made by whoever did the work, against whatever context they had in mind. When most work comes from automated agents, assertions like these cannot be read and checked one by one. Closure has to be **computed** from the evidence against a fixed intent, and an unfinished state has to be **named** rather than rounded up.

RCC's normalizer returns exactly one of:
- `Closed`: closed relative to the admitted intent and context;
- `Await`: waiting on named, still-open obligations;
- `Reepoch`: the context changed, so the question must be re-asked in a new epoch;
- `Halt`: a contradiction that no amount of further work repairs.

RCC is an instance of [MST-NF](https://github.com/residua-labs/MST-NF): every claim ends admitted as `Closed` or refused with a typed non-closure.

## How Residua uses it

- **Publication claims:** every property sentence in the [MST-NF](https://github.com/residua-labs/MST-NF) README resolves through a claims registry that RCC checks; the published verdict is `Closed`.
- **Risk frontiers:** the open obligations of the R-CIC kernel ([Residua](https://github.com/residua-labs/Residua)) are tracked as an RCC frontier, where a remaining obligation shows up as `Await`, not as prose.
- **Institutional cuts:** [IEC](https://github.com/residua-labs/IEC) obtains its closure verdicts and snapshots from RCC.

## Status, stated exactly

- This repository is the complete RCC Lean development, apart from one excluded module listed below. It contains 239 library modules and 190 test modules, and every theorem's axioms are audited.
- **RCC's own closure is computed, like everyone else's.** Its own obligation catalogue (108 entries, published in [`self-closure/`](self-closure/)), run through RCC's normalizer, gives `Closed|closed=117` on both the literal and the strict reading (raw output and inputs: [`self-closure/verdict.txt`](self-closure/verdict.txt)). `closed=117` counts the executable's graph nodes, not catalogue entries: the graph has 116 nodes — the 108 obligations plus 8 `disposition:*` producer nodes that feed the eight named gaps' dispositions back into the graph — and the count adds the `RCC-V2-closure` intent node itself. The named caveat is inside the catalogue itself: `RC-3b`, "RCC self-check may govern only a successor epoch", is one of the eight `out_of_scope_documented` dispositions. `closure_claim = 0`.
- **This release.** Built from Residua `main` at `b54a914fcf`. No theorem uses `Classical.choice` any more: the previous release listed 7 that did (in `RCC.ClosureExhaustion`, `RCC.CrossEpochFairness94`, `RCC.E2Target`, `RCC.RCC94Target`). Each was re-proved with its statement byte-identical, and the census below is the raw output of `scripts/PrintAxioms.lean`. Before publication, two independent auditors from different model families each passed the same seven checks: file digests, the axiom census reproduced from a fresh build, the closure verdict, the delta against the previous stage, the census script itself, hygiene, and that every number in this README is present in the raw outputs.
- RCC is part of the dependency closure of Residua's releases, which start at **0.1** (bootstrap version + R-CIC current state + dependency closure). See [residua-labs/Residua](https://github.com/residua-labs/Residua).

## Contents

Machine-checked Lean 4 modules for the **Relative Closure Calculus (RCC)**,
extracted from the Residua project.

RCC is a calculus for deciding, for one frozen epoch, whether a body of work is
*closed relative to* an admitted intent and context, and — when it is not — for
returning which typed non-closure it is. The core normalizer returns exactly one of
`Closed | Await | Reepoch | Halt`.

## What is included

This is the **complete** RCC development from Residua, apart from the one
module listed under *Excluded* below:

* 239 library modules under `RCC/` (declarations in `Residua.RCC.*`);
* 190 test modules under `RCCTests/` — concrete witnesses and refusal cases for
  the corresponding `RCC.*` modules, most finishing with `#print axioms` checks,
  including the five discriminating self-closure sites `RCCTests.Sites*`;
* 4 vendored support modules under `RCC/Support/` (see below);
* the self-closure evidence pack under [`self-closure/`](self-closure/) — the
  obligation catalogue, registry, evidence pass, executable checker and the
  computed verdict with its inputs.

The full module list is in [`MODULES.md`](MODULES.md). Declarations keep their
original `Residua.*` namespaces. Apart from import lines, the code is unchanged from
the Residua source, except that: one comment was edited to remove an internal issue
reference; module comments that said "no axioms" were corrected to name the standard
axioms actually used; and two comment lines in `RCC.Support.SlotSemanticsCore` were
rewritten in English (one of them used a non-Latin sample string in a comment).
Module paths were renamed for this standalone release (`algorithms.ResiduaRCC<Name>`
→ `RCC.<Name>`, `algorithms.ResiduaRCC<Name>Tests` → `RCCTests.<Name>`), so file
hashes differ from those in the original source tree.

### Vendored support modules (`RCC/Support/`)

A few RCC modules depend on Residua code outside RCC. That code is vendored here,
unchanged apart from import lines, as separate modules; their declarations keep their
original Residua namespaces.

| Module | Residua source | Used by |
|---|---|---|
| `RCC.Support.LeanOnceSoundnessProduction` | `algorithms.LeanOnceSoundnessProduction` | `RCC.DefeqFragment` and the modules built on it |
| `RCC.Support.PatchFabricMWE` | `algorithms.ResiduaPatchFabricMWE` | `RCC.ProofTermCompiler` |
| `RCC.Support.SlotSemanticsCore` | `Residua.SlotSemanticsCore` | `RCC.Support.PatchFabricMWE` |
| `RCC.Support.SHA256` | `Residua.SHA256` | `RCC.Support.SlotSemanticsCore` |

`RCC.ProofTermCompiler` is a metaprogram (it imports `Lean.Elab.Command`) that
serializes RCC proof terms for Residua's SCM toolchain; it only defines commands and
writes nothing during `lake build`.

### Excluded

* `RCC.ProofTermGenerateLetter`: a generator that writes emitted proof terms into
  Residua's `conformance/` tree as a side effect of being built; it proves nothing.
  (`RCC.M1Target`/`RCCTests.M1Target`, excluded from the first release because the
  source then did not build at 4.14, now build and are included.)

## What is *not* claimed

* The numbered `*Target` modules discharge individual targets of the obligation
  catalogue published in [`self-closure/`](self-closure/). Several say in their own
  docstrings that they are fixture-level discharges (concrete witnesses and mutant
  refusals) rather than general theorems. Read each module's docstring for its exact
  scope.
* Many modules name interfaces whose later obligations are deliberately left open.
* Residua's generated proof terms, SCM artifacts and admission workflows are not
  included.

## Trust base

* Lean 4 core only (`leanprover/lean4:v4.14.0`). No Mathlib, no dependencies.
* No `sorry`, no `axiom` declarations, no `implemented_by`, `extern` or `unsafe`.
  `native_decide` is not used in any theorem; it appears only in 137 `example`
  sanity checks inside the vendored `RCC.Support.SlotSemanticsCore` (examples are not
  exported and no theorem depends on them).
* `scripts/PrintAxioms.lean` checks every theorem in `RCC.*` (7,354 theorems, including
  `RCC.Support.*`; full raw census shipped as
  [`self-closure/axiom_census.txt`](self-closure/axiom_census.txt)). The exact axiom
  sets are: 4,879 theorems use no axioms; 1,508 use `{propext}`; 951 use
  `{propext, Quot.sound}`; and 16 use `{Quot.sound}`. No theorem uses
  `Classical.choice` or any other axiom (in particular none uses
  `Lean.ofReduceBool`).

## Build

```sh
# install elan: https://github.com/leanprover/elan
lake build                                   # builds RCC and RCCTests
lake env lean --run scripts/PrintAxioms.lean # axiom summary for all RCC theorems
```

## License

Apache-2.0. See `LICENSE` and `NOTICE`.

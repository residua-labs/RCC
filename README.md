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

- This repository is the complete RCC Lean development, apart from three excluded modules listed below. It contains 236 library modules and 184 test modules, and every theorem's axioms are audited.
- **RCC itself is not claimed closed.** Its own obligation catalogue (108 entries), run through RCC, gives `Await`, with 8 named gaps; `closure_claim = 0`. RCC is used to compute the closure of other work while its own closure is still being completed, and that is reported the same way it reports everyone else's.
- RCC is part of the dependency closure of Residua's releases, which start at **0.1** (bootstrap version + R-CIC current state + dependency closure). See [residua-labs/Residua](https://github.com/residua-labs/Residua).

## Contents

Machine-checked Lean 4 modules for the **Relative Closure Calculus (RCC)**,
extracted from the Residua project.

RCC is a calculus for deciding, for one frozen epoch, whether a body of work is
*closed relative to* an admitted intent and context, and — when it is not — for
returning which typed non-closure it is. The core normalizer returns exactly one of
`Closed | Await | Reepoch | Halt`.

## What is included

This is the **complete** RCC development from Residua, apart from the three
modules listed under *Excluded* below:

* 236 library modules under `RCC/` (declarations in `Residua.RCC.*`);
* 184 test modules under `RCCTests/` — concrete witnesses and refusal cases for
  the corresponding `RCC.*` modules, most finishing with `#print axioms` checks;
* 4 vendored support modules under `RCC/Support/` (see below).

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

* `RCC.M1Target` and its test `RCCTests.M1Target`: the module does not build in the
  Residua source (a `rw` step fails at line 246 under Lean 4.14.0).
* `RCC.ProofTermGenerateLetter`: a generator that writes emitted proof terms into
  Residua's `conformance/` tree as a side effect of being built; it proves nothing.

## What is *not* claimed

* The numbered `*Target` modules discharge individual targets of an internal
  obligation catalogue that is not published here. Several say in their own docstrings
  that they are fixture-level discharges (concrete witnesses and mutant refusals)
  rather than general theorems. Read each module's docstring for its exact scope.
* Many modules name interfaces whose later obligations are deliberately left open.
* Residua's generated proof terms, SCM artifacts and admission workflows are not
  included.

## Trust base

* Lean 4 core only (`leanprover/lean4:v4.14.0`). No Mathlib, no dependencies.
* No `sorry`, no `axiom` declarations, no `implemented_by`, `extern` or `unsafe`.
  `native_decide` is not used in any theorem; it appears only in 137 `example`
  sanity checks inside the vendored `RCC.Support.SlotSemanticsCore` (examples are not
  exported and no theorem depends on them).
* `scripts/PrintAxioms.lean` checks every theorem in `RCC.*` (7,242 theorems, including
  `RCC.Support.*`): 4,808 use no axioms; 1,488 use `propext`; 923 use `propext` and
  `Quot.sound`; 16 use only `Quot.sound`; 7 use `propext`, `Quot.sound` and
  `Classical.choice` (in `RCC.ClosureExhaustion`, `RCC.CrossEpochFairness94`,
  `RCC.E2Target`, `RCC.RCC94Target`). No theorem uses any other axiom
  (in particular none uses `Lean.ofReduceBool`).

## Build

```sh
# install elan: https://github.com/leanprover/elan
lake build                                   # builds RCC and RCCTests
lake env lean --run scripts/PrintAxioms.lean # axiom summary for all RCC theorems
```

## License

Apache-2.0. See `LICENSE` and `NOTICE`.

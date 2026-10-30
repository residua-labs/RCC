# RCC evidence-grade pass (cc-releaseclosure, 2026-10-24)

`closure_claim = 0`. Draft. Base: `527793d471` (#7995, `cc/closure-check-mstnf-rcc`). Evidence is added alongside the registry:
`conformance/rcc/RCC_EVIDENCE_PASS_V1.json` (new), `conformance/rcc/nanoda/evidence_pass/` (new carrier), raw logs in `raw/rcc_evidence/`.
No registry byte, target statement or existing carrier was changed. The 8 named gaps (BH-1/2/3, AK-9, ME-2, RC-3b, EF-2, EF-3) are untouched.

## 0. Result

| Reading | Before (#7995) | After this pass |
|---|---|---|
| Literal (registry id or mapped slot) | **9 open** | **15 open** (the 9 + AK-3, DQ-1, FC-2, FC-3, CM-1, RC-2) |
| Evidence-checked | **47 open** | **17 open** (the 15 + R1, M1) |

Both numbers come from rerunning the same RCC executable (`normalize` over the obligation graph, tools of #7995) on a Lean 4.14.0 scratch build: the "before" graphs reproduce 9/47 exactly (`raw/rcc_evidence/rcc_verdict_before_after.txt`), verdict `Await` in all four runs, never `Halt`.

**The literal reading did not converge to 9; it moved to 15.** Re-adjudicating the six low-confidence mappings rejected all six (§3). The 47 → 17 drop is evidence quality, as expected; the 9 → 15 rise is the mappings. Caveat (THE GATE RULE): the producer rules are mine, as in #7995; the information is in the builds, the axiom lines, the content-addressed pins and the statements read against the obligation text.

## 1. (b) Carrier toolchain — rebuilt at 4.14.0 on GCP, **not re-pinned**

All 104 carriers copied to a scratch tree with `lean-toolchain` set to `leanprover/lean4:v4.14.0` and built with `lake build` on `gcp-lean` (`raw/rcc_evidence/carriers_lean_4_14_summary.txt`, 447 s of CPU in total):
**102 of 104 exit 0**, 0 `sorryAx`, `Classical.choice` only in `e2` and `rcc94` as before. The two failures are `m1` and `carried` (`RCCCarriedIndependent` imports `M1Target`): `ResiduaRCCM1Target.lean:246:8` rewrite failure, the known 4.14 failure.

**I did not re-pin the 98 carriers that passed, and recommend not doing it.** Each carrier's independent leg (`conformance/rcc/nanoda/run_k1_probe.sh`) copies the carrier's `lean-toolchain` into a build of `lean4export` at the pinned commit `caccfbebbc99`, whose own `lean-toolchain` is 4.29.0. Built at 4.14.0 that commit fails (`Export.lean:391: invalid field 'toJson', the environment does not contain 'Array.toJson'`, plus two more errors; reproduced on `lean-w1`). The export must be produced at the same toolchain that built the oleans, so a 4.14 pin would silently cut the Nanoda K+1 leg from every re-pinned carrier. The 4.29 pin is load-bearing for that leg. Instead the 4.14 results are recorded as a second seat (this document + sidecar). Re-pinning becomes possible only with an older `lean4export` commit that builds at 4.14 and a re-run of K+1 for it — a change to the independent checker's pin, which I did not make.
Net: the toolchain mismatch is a two-seat situation, not a defect: 4.14 seat (repository toolchain) 102/104; 4.29 seat (K+1) 104/104 per #7995.

## 2. (d) Registry pins — 59 defective pins, resolved by sidecar (45 ids)

(The 42 "malformed" and 17 "stale" pins of #7995; `pins` in the sidecar.)
- **26 of the 42 malformed pins name `ResiduaRCCRCC<N>TargetTests.lean` (N = 32, 68–92) which does not exist in the tree** — those targets have no Tests module. They are dangling, not re-pinnable, and not a declaration file of any entry (the entries' declarations are in the Target files). Recorded as such.
- The other 16 malformed pins (`HEAD:path` rev-specs) and all 17 stale pins: sidecar records the path and the **current blob sha** (`git hash-object`), and the owning entry's 4.14 carrier result (102/104 pass, built against exactly those bytes).
- **Stale pins were checked against history, not just refreshed.** Every stale blob is an earlier version of the file, replaced by a named repair commit: `RCC39` ("#2973 proposal-indexed acceptance predicates"), `RCC32` ("#2973 drop tautological generic_* theorems"), `RCC40` ("#2973 correct docstring overclaim"), `RCC0` ("use non-degenerate address kernel witness #2760"), `RCC87` ("independent root did not audit the discriminating field #2438"), `RCC106` ("bind context-omission mutant to distinct contexts #2761"), `RCC95` and the C/E independent roots ("RCC packet is the law … retarget statement_q #3501", "axiom-dep gates across all probes #2663"). These match the registry's own revocation/downgrade nonclaims (RCC32 revoked then re-registered as fixture; RCC40 demo-only; RCC39 revoked then re-registered proposal-indexed). The pins were simply never moved to the repaired bytes. Nothing found is hollow; the repaired entries are fixture-scoped, which their scope text already says.
- Unresolved: **M1** (its carrier does not build at 4.14; it builds only at 4.29).

## 3. (a) The six low-confidence mappings — all REJECTED

Read each obligation title (`RCC_V2_OBLIGATION_MIGRATION.json`) against the mapped target slot's certificate and the library module that actually states the subject.

| Obligation | Mapped slot | Verdict | Reason |
|---|---|---|---|
| AK-3 | RCC57 | **rejected** | Slot RCC57 states a collision-policy slice only; the structural floor (preimage = kind+algorithm+domain+schema+bytes, injective frame, collision refusal) is Residua.RCC.Addressing in algorithms.ResiduaRCCDigestBinding (general, parametric), which no registered target imports as its subject. Candidate owner: DigestBinding; unregistered, no Tests module. |
| CM-1 | RCC89 | **rejected** | RCC89 covers the probabilistic/statistical pair (2 of 6 modalities). The six-modality typed index with alignEvidence and mismatched_modalities_are_refused is ClaimModality. Candidate owner: ClaimModality; unregistered, no Tests module. |
| DQ-1 | RCC105 | **rejected** | RCC105 pins only the out-of-fragment boundary. The sound-and-complete classifier is DefeqFragment (classify_supported_iff, classify_unsupported_iff) for the current twelve-constructor Term surface; DefeqFragmentTests exists. Candidate owner: DefeqFragment; unregistered. |
| FC-2 | RCC63 | **rejected** | RCC63 derives a gluing certificate from FacetCoherence; the seven bridge laws (address, evidence, resource delta, reflection stratification, migration, runtime refinement, composition gluing) with BoundFacetPairAt origin are FacetCoherence itself (+Tests, missingResourceDeltaRefused). Candidate owner: FacetCoherence; unregistered. |
| FC-3 | RCC70 | **rejected** | RCC70 missingResidueRefused is one deletion countermodel (residue facet). No module states deletion countermodels for every load-bearing facet; no owner exists. |
| RC-2 | RCC96 | **rejected** | RCC96 covers the diagnostic-naming fragment. No module states that every non-closed run yields a diagnostic; no owner exists. |

For AK-3, DQ-1, FC-2, CM-1 a general, building, Prelude-only library module states the obligation (candidate owners above). They are **proposals**, not discharges: unregistered, authored by others but adjudicated here by me alone, and two have no Tests module. Registering them needs an independent review and (for AK-3, CM-1) a discriminating test; I did not count them. FC-3 and RC-2 have no owner. Rejected mappings are uncovered in both readings.

## 4. (c) The 18 lower-grade entries — fields read one by one

`raw/rcc_evidence/certificate_fields_17_targets.txt` lists every field of each `Certificate` (type printed by Lean 4.14; M1 excluded because it does not build). A site is *discriminating* if a positive field at a concrete fixture sits beside a refusal (`¬`/`≠`/`MutantRefusal`) that a named mutant breaks.
- **Discriminating (13):** C1, C2, C4, E1, E3, E4, E5, R2, R3, R4, R5, RCC20, RCC24 — each has a concrete positive and one or more concrete refusals (e.g. C2: `identityExact` vs four `…Rejected`; R4/RCC20/RCC24: `MutantRefusal` with 2/7/6 refusals).
- **Universal only, no concrete witness (5):** E2, R1, RCC22, RCC23, M1. A certificate quantified over every system is vacuous if no system exists. Added: new carrier `conformance/rcc/nanoda/evidence_pass/` (Lean 4.14, builds, exit 0, `raw/rcc_evidence/evidence_pass_carrier_build.txt`):
  - **E2** (`SitesE2`): a one-point `ClosureStateSystem`; the premises of `invalidWorkDoesNotClose` hold there, and dropping `unsatisfied` breaks the conclusion at the mutant. Axioms: `propext, Classical.choice, Quot.sound` (inherited from the library theorem).
  - **RCC22** (`Sites22`): a concrete `WakeSystem` family indexed by `adv`; an `AwaitCertificate` exists at `adv := False`, none at `adv := True`. No axioms.
  - **RCC23** (`Sites23`): the target's fields applied to the library's legitimate `ReepochCert`, plus the library's missing-trigger and parent-cycle rejections. `propext` only.
  - **R1: not possible yet.** Its refusal fields quantify over `ClosureContext`, and **no concrete `ClosureContext` exists anywhere in the tree** (the same gap covers the `RC-1`/`RelativeCompleteClosureTests` stack, which also quantifies over an arbitrary `C`). Building one is the RC-1 content work; left open.
  - **M1:** stays open — not buildable at 4.14, and the registry's own nonclaim says M1 is open (Step-MST q/a/σ/ρ, admitted traces, GlobalEpochClosed bridge not all encoded).

## 5. Per-entry table (the 47 open entries of #7995)

| id | status | blockers before | carrier @4.14 | action | after |
|---|---|---|---|---|---|
| RCC-0 | DISCHARGED | (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier | covered |
| R1 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; NO site possible yet | open |
| R2 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| R3 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| R4 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| R5 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| E1 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| E2 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; site added (evidence_pass) | covered |
| E3 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| E4 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| E5 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| C1 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| C2 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| C3 | DISCHARGED | (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier | covered |
| C4 | DISCHARGED | (c), (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier; fields read: positive + concrete mutant present | covered |
| M1 | DISCHARGED | (c), (d) pin | **exit 1** | pin sidecar: current blob + 4.14 carrier; NO site possible yet | open |
| RCC-20 | DISCHARGED | (c) | exit 0 | fields read: positive + concrete mutant present | covered |
| RCC-22 | DISCHARGED | (c) | exit 0 | site added (evidence_pass) | covered |
| RCC-23 | DISCHARGED | (c) | exit 0 | site added (evidence_pass) | covered |
| RCC-24 | DISCHARGED | (c) | exit 0 | fields read: positive + concrete mutant present | covered |
| RCC-32 | DISCHARGED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| RCC-39 | DISCHARGED | (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier | covered |
| RCC-40 | DISCHARGED | (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier | covered |
| AK-3 | MAPPED | (a) | exit 0 | mapping rejected | open |
| AK-9 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| DQ-1 | MAPPED | (a) | exit 0 | mapping rejected | open |
| DQ-7 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + 4.14 carrier | covered |
| FC-2 | MAPPED | (a) | exit 0 | mapping rejected | open |
| FC-3 | MAPPED | (a), (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier; mapping rejected | open |
| BH-1 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| BH-2 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| BH-3 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| CM-1 | MAPPED | (a), (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier; mapping rejected | open |
| CM-2 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| CM-3 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-1 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-2 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-3 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-4 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-5 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| WI-6 | MAPPED | (d) pin | exit 0 | pin sidecar: current blob + dangling Tests pins noted + 4.14 carrier | covered |
| EF-2 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| EF-3 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| ME-2 | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| RC-1 | MAPPED_SLOT_NOT_DISCHARGED | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |
| RC-2 | MAPPED | (a) | exit 0 | mapping rejected | open |
| RC-3b | NAMED_GAP | literal-open | — | out of scope (named gap / RC-1 unregistered) | open |

## 6. What this does not do

No target statement changed; no registry byte changed; no discharge revoked (none found hollow); the 8 gaps are untouched; no Nanoda K+1 re-run. Still open from #7995: records disagree (3/73/100/9), 49 thin-audit entries are not re-read for audit surface, 0 of 117 certificates is a statement over an arbitrary RCC instance.

## 7. Reproduce

```text
carriers: copy lean/ and conformance/rcc/nanoda/ to a scratch tree, write leanprover/lean4:v4.14.0 into each carrier lean-toolchain, `lake build` per carrier (6 in parallel)
lean4export check: clone leanprover/lean4export @ caccfbebbc99, lean-toolchain := 4.14.0, lake build
fields: Lean run_cmd over getStructureInfo? of each <T>Target.Certificate (17 targets)
verdict: InstJson.lean of #7995 on rcc_graph_after_{literal,strict}.json (+ the two old graphs as control)
```
Scripts live outside the repo under the lane directory; no `.py/.sh/.js` was added.

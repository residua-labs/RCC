# RCC self-closure evidence

RCC is a calculus for computing closure. This directory contains the artifacts of
running RCC **on its own obligation catalogue** — the same judgement it applies
to everything else, applied to itself.

## Verdict (computed, not asserted)

```
literal:  RCC-V2-closure: Closed|closed=117
strict:   RCC-V2-closure: Closed|closed=117
```

Raw output: [`verdict.txt`](verdict.txt). `closure_claim = 0` — the verdict is
what the executable printed on the inputs below; nothing here is claimed beyond
that run.

- **literal** — obligations count as covered when their registered discharge or
  an un-rejected mapping exists.
- **strict** — additionally requires every registered evidence pin to resolve
  (no malformed, stale or missing `checked_source_git_blob_sha`) and every
  letter-target discharge to meet the upgraded evidence grade (field-read or
  discriminating-site evidence, including the concrete `ClosureContext`
  inhabitant `demoContext` in `RCCTests/SitesR1`).

## Reproduce

```sh
lake build                                                  # builds RCC + RCCTests
RCC_DATA=self-closure/data_literal.json \
  lake env lean self-closure/CheckClosure.lean              # prints the literal verdict
RCC_DATA=self-closure/data_strict.json \
  lake env lean self-closure/CheckClosure.lean              # prints the strict verdict
```

`CheckClosure.lean` loads `data_*.json` (obligation nodes + routes + the
`RCC-V2-closure` intent) and runs `Residua.RCC.normalize` from `RCC.FormalCore`
over it. Both data files are byte-identical at this revision — under the strict
reading every obligation is covered by on-tree evidence, so no node is dropped.

## Inputs (this run)

| input | value |
|---|---|
| Residua source commit | `b54a914fcf20d6715412d11f1a2e69f2b52c07cd` (main) |
| executable (this file's sha256) | `ad901c74339cb3822f1440d3fb8d46d9457363f34a3cd370828e96a8940e8ec1` |
| `data_literal.json` sha256 | `8ec85cfd76decf4bc3876cd70244d0199b90e9ef15cdc87b8c690105d07bc57f` |
| `data_strict.json` sha256 | `8ec85cfd76decf4bc3876cd70244d0199b90e9ef15cdc87b8c690105d07bc57f` |
| `RCC_V2_OBLIGATION_MIGRATION.json` sha256 | `d8b9b472e3840503fadf88c2fdf95117a54a1e7d5db314d17c36fc12046d2ed9` |
| `RCC_FORMAL_PROOF_REGISTRY_V1.json` sha256 | `d43494d345551c8e73bd620de23c3f2a8e9a0e23ebd77707f2b4e8eddd266cfa` |
| `RCC_EVIDENCE_PASS_V1.json` sha256 | `1eb55367dc01bf3ee4adf9ecb326ced2d274959179bc6622a6b3860e5c148847` |

## What is here

- `RCC_V2_OBLIGATION_MIGRATION.json` — the 108-entry obligation catalogue the
  verdict runs over (source: `docs/rcc/` in Residua).
- `RCC_V2_LETTER_TO_SLOT_SEMANTIC_MAPPING.json` — letter-obligation → slot map
  used by the coverage pass (source: `docs/rcc/`).
- `RCC_FORMAL_PROOF_REGISTRY_V1.json` — the formal-proof registry: discharged
  targets, evidence pins (`checked_source_git_blob_sha`) and the eight
  `out_of_scope_documented` dispositions (named gaps, not discharge).
- `RCC_EVIDENCE_PASS_V1.json` — per-target evidence pass with mapping
  adjudications.
- `CheckClosure.lean` — the executable: `Residua.RCC.normalize` over the
  obligation graph (transformed from `InstJson.lean` in Residua).
- `data_literal.json` / `data_strict.json` — the obligation graphs the
  executable consumed for this verdict.
- `verdict.txt` — raw output.
- `axiom_census.txt` — the axiom census over all 7,354 `RCC.*` theorems, raw
  stdout of `scripts/PrintAxioms.lean`: a count per exact axiom set, the fixed
  buckets, the theorems that use `Classical.choice` (none at this revision),
  any non-standard axiom uses, and one `name / axiom set / module` row per
  theorem.
- `docs/` — the self-closure write-ups per class (A–E) and the evidence-pass
  note (source: `research/release/closure/`).
- `raw/` — the per-class raw evidence packs: coverage census, pin audit,
  generated graphs and build/verdict logs (source:
  `research/release/closure/raw/`). The instruments that produced them are
  shipped as inert `*.txt` snapshots for provenance only — no host tooling is
  included. The sha256 of every file under `self-closure/` is listed in
  `SHA256SUMS.txt`.
- `SHA256SUMS.txt` — content ids (sha256) of every file shipped under
  `self-closure/`.

## Coverage census

108 obligations: 73 discharged + 8 named gaps (explicit registry dispositions)
+ 27 mapped to discharged slots. The executable's graph has 116 nodes (108
obligations + 8 disposition producers); `closed=117` counts every node plus the
`RCC-V2-closure` intent itself.

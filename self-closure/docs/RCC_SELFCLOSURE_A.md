# RCC self-closure — class A: evidence landed on main, verdict rerun (devin-fcd, 2026-10-29)

`closure_claim = 0`. Draft.

This is class A of the RCC self-closure work order (cc INBOX 20261028T230451Z): #8037
(`cc/rcc-evidence-pass`) rebased onto `main` and the verdict rerun there. #7995 stays
unmerged; this branch carries only #8037's own commit (cherry-picked, byte-identical)
plus the rerun artifacts under `raw/rcc_evidence_main/` and this note.

## Verdict (the RCC executable, never asserted)

Same pipeline as #7995/#8037: `coverage` (catalogue + registry + letter mapping +
module presence) → graph prep → `InstJson.lean` (`Residua.RCC.normalize` over the
obligation graph). Run on `main` @ `2806dd1049` + this branch's evidence:

| Reading | #7995 | #8037 (on #7995) | **now (on main)** |
|---|---|---|---|
| literal | 9 open | 15 open | **14 open** |
| evidence-checked (strict) | 47 open | 17 open | **15 open** |

Both runs: `Await`, never `Halt` (`raw/rcc_evidence_main/rcc_verdict_main.txt`).

- **RC-1 covered**: its slot RCC95 was re-registered on main (#8033/#8064) and its
  `rcc95_*_v2` pins equal the current blobs byte-for-byte (verified by
  `git hash-object`; the stale `rcc95_*` originals are superseded bookkeeping).
  High-confidence mapping → covered in both readings.
- **M1 covered**: #8032 made `ResiduaRCCM1Target`(+Tests) build at 4.14. Re-verified:
  the `conformance/rcc/nanoda/m1` carrier rebuilt at `leanprover/lean4:v4.14.0` in a
  scratch tree, exit 0, axioms `{propext, Quot.sound}`
  (`raw/rcc_evidence_main/m1_carrier_414_main.txt`). Its `Certificate` fields are
  discriminating, not universal-only: `incoherentHeadRefused`,
  `incoherentEventRefused`, `nonadmittedCannotBind`, `emptyEventCannotCover`,
  `nonSettledRefused` at the concrete `Phase`/slot-mismatch fixtures.
- **Pins**: fresh audit on main (`raw/rcc_evidence_main/registry_pin_audit_main.json`):
  473 pins, 42 malformed (the same `HEAD:`/dangling-`TargetTests` set), 18 stale,
  0 unresolved after the evidence-pass sidecar (the 3 rcc95 stale originals are
  superseded by the `_v2` pins, not by this sidecar).

## Open set (the work of classes B–E)

Literal (14): `AK-3 DQ-1 CM-1 FC-2` (class B: registration onto real owners),
`FC-3 RC-2` (class C: truly missing), `BH-1 BH-2 BH-3 AK-9 ME-2 RC-3b EF-2 EF-3`
(class D: evidenced scope dispositions).
Strict adds `R1` (class E: a concrete `ClosureContext` fixture; none in the tree).

## Method notes

- `raw/rcc_evidence_main/` carries every input and output of the rerun:
  `coverage_main.json`, `registry_pin_audit_main.json`, both graphs, the verdict
  text, and the instruments as `.txt` (`coverage.py.txt`, `pin_audit.py.txt`,
  `prep_main.py.txt`, `InstJson.lean.txt`). No `.py/.sh/.js` added.
- `conformance/rcc/RCC_EVIDENCE_PASS_V1.json` gained two additive fields
  (`reverified_against`, `reverify_note`); no evidence byte changed.
- Caveat carried forward (THE GATE RULE): the producer rules are this lane's
  reimplementation of #7995/#8037's semantics; the information is in the builds,
  the pin audit, the content-addressed sidecar and the certificate fields.

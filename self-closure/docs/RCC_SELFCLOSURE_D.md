# RCC self-closure — class D: the 8 named gaps consumed as dispositions (devin-fcd, 2026-10-29)

`closure_claim = 0`. Draft. Stacked on class C (#8298).

Class D of the work order: BH-1, BH-2, BH-3, AK-9, RC-3b, ME-2, EF-2, EF-3 are
recorded as **explicit evidence-based scope dispositions consumed by the RCC
executable** — never deleted, never discharged-by-silence.

## What changed

- Registry `out_of_scope_gaps` (8 entries, pre-existing with measured reasons
  + re-adjudication envelopes) now carries explicit
  `disposition: "out_of_scope"`, `consumed_by` (the graph producer node name),
  and `evidence_grade` fields per entry. Nothing deleted; the gap records ARE
  the covering evidence.
- The verdict data prep emits, per dispositioned gap, a `disposition:<id>`
  producer node (ground evidence = the registry record, itself pinned by the
  registry blob hashes) and routes the gap obligation through it. The
  executable therefore *consumes* the disposition rather than counting the
  gap as an unwitnessed open hypothesis.
- The gap obligations remain visible in the graph under their own names; the
  coverage file still marks them `NAMED_GAP`; the disposition producers are
  named `disposition:BH-1` etc. — a reader can see closure runs through a
  recorded scope boundary, not through a theorem.

## Verdict delta (the executable, never asserted)

| Reading | class C | **after D** |
|---|---|---|
| literal | 8 open (all gaps) | **Closed** (116/116 nodes incl. 8 dispositions) |
| strict | 9 open | **1 open — R1** |

`raw/rcc_evidence_d/` has both graphs and the verdict text.

## R1 residue (class E boundary, recorded not hidden)

`Residua.RCC.R1Target.Certificate` is parametric over
`{C : ClosureContext State}` (RelativeCompleteClosure.lean:51) and no concrete
`ClosureContext` inhabitant exists in the tree. Building one is class E; the
strict verdict honestly stays `Await|open=[R1]` until then.

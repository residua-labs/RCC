# RCC self-closure — class E+F: the concrete `ClosureContext` inhabitant and final strict verdict (devin-fcd, 2026-10-29)

`closure_claim = 0`. Draft. Stacked on class D (#8299).

Class E of the work order: build a concrete `ClosureContext` inhabitant so the
`{C : ClosureContext State}`-parametric fields of `Residua.RCC.R1Target.Certificate`
can be exercised at a real instance — the gap the class-D strict verdict named
as its only residue. Class F: rerun both readings.

## The fixture

`conformance/rcc/nanoda/registration_sites/SitesR1.lean` constructs

    Residua.RCC.RegistrationSites.R1.demoContext
      : ClosureContext FacetCoherence.Tests.Carrier

— the first `ClosureContext` inhabitant in the tree (measured before building:
none existed; every consumer held `C` parametrically). ~78 dependent fields
filled without vacuous shortcuts:

- FC-1: `IsSealed := True` seal spec; snapshot coordinates and carrier are the
  state's own projections, so every `SnapshotCarrier` bound is `rfl` and
  `carrierValueBound` is `rfl`.
- FC-2: the existing `FacetCoherence.Tests` adapter, head-tagged payload, and
  seven decode surfaces reused per-state; `facetCertificateAt` discharges by
  head-case `rfl`.
- Intent/support/replay/primitive/reepoch/effect/failure/closure systems all
  inhabited explicitly — trivial-but-honest types (`Unit`/`Nat`/`[]`), real
  verifier fields that refuse, and the engineered equalities doing real work:
  `liveGoalAt` reads the current intent profile's `mandatoryGoals` so
  `intentClosureGoalLiveExactAt` is a `∃`-witness iff, not `True`;
  `failureContextExact` is `rfl` on the state's own head/failure-model pair.

## Discriminating sites at the concrete context

One admitted `AdvancePacket` between the two fixture carriers
(`.h1 ↦ .before`, `.h2 ↦ .after`):

- positive — `advance_resolves_at_concrete_context`: the packet binds a
  durable `HistoryEdge`;
- mutant — `nonadmitted_refuses_at_concrete_context`: the same packet with
  `admitted := false` cannot bind;
- mutant — `empty_event_refuses_at_concrete_context`: the empty-settled-event
  surface cannot append;
- `demo_packet_is_admitted` (rfl) — the positive/mutant pair genuinely
  discriminates on admission at one concrete packet;
- `work_preserves_goal_presence`, `work_preserves_goal_status`,
  `acted_target_stays_open_and_disposed` — the four `GoalWorkSystem`-indexed
  fields at one concrete system/snapshot.

## Independent check (two compiler versions)

- `registration_sites` package at `leanprover/lean4:v4.14.0`: `demoContext`
  and all sites build; `#print axioms` reports **no axioms at all** for
  `demoContext` and six of eight sites, `[propext]` for the rest — no
  `sorryAx`.
- `conformance/rcc/nanoda/r1` at `leanprover/lean4:v4.29.0` (a second compiler
  generation): new `R1SitesSource` lib re-elaborates `SitesR1` and
  `R1Independent.lean` `#check`s/`#print axioms` every site declaration —
  identical results. (This is why no `.{u…}` universe pins appear in
  `SitesR1.lean`: `ClosureContext`'s pooled binder count differs between the
  two versions; all instantiations go through the concrete arguments.)
- `pin_audit`: `r1_independent_root`, `r1_lakefile` re-pinned to current blobs;
  `r1_target` remains `HEAD:`-pinned and sidecar-resolved as before (target
  file untouched — no landed declaration edited).
- `dupdecl.py origin/main`: exit 0.

## Registry / evidence changes

- `discharged_targets` R1 entry: `proof_kind`
  `carrier_built_certificate_with_concrete_context_fixture`; declarations now
  include the nine site declarations; scope rewritten to describe the concrete
  fixture, the exercised fields, and the dual-compiler check. The earlier
  "LOWER EVIDENCE GRADE" note is removed by construction.
- `RCC_EVIDENCE_PASS_V1.json`: `sites_missing.R1` marked RESOLVED;
  `reverify_note4` records the class.
- prep `upgraded` set: `r1` added **after** the fixture existed and was
  independently checked — the gate change follows the evidence, not vice
  versa.

## Verdict delta (the executable, never asserted)

| Reading | class D | **after E** |
|---|---|---|
| literal | Closed (117) | **Closed** (117) |
| strict | Await, open=[R1] (115/117) | **Closed** (117) |

`raw/rcc_evidence_e/` has both graphs, the verdict text, both seat build logs,
coverage, and the pin audit.

## What this does and does not claim

- The strict reading is now Closed: every remaining named residue is either
  discharged, consumed by an explicit measured disposition, or — R1's case —
  witnessed by a compiled, independently re-elaborated concrete instance.
- `demoContext` is deliberately minimal (trivial-but-honest `Unit`/`Nat`
  carriers, engineered equalities). It proves the certificate is exercisable
  and its refusals real; it is a fixture, not a production topology.
- `closure_claim = 0` remains: the executable's own verdict is reported, not
  asserted.

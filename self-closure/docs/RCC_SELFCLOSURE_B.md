# RCC self-closure — class B: registrations onto the real owners (devin-fcd, 2026-10-29)

`closure_claim = 0`. Draft. Stacked on class A (#8295).

Class B of the work order: the four rejected mappings whose content **exists in
library modules** are now registered onto their real owners — additive
`discharged_targets` entries only; no registry byte, target statement or mapping
was edited. Each entry carries a compiled discriminating site in the new carrier
`conformance/rcc/nanoda/registration_sites/` (Lean 4.14.0, `#print axioms` per
file; SitesDQ1/SitesFC2 report no axioms, SitesAK3/SitesCM1 report `propext`
only — `raw/rcc_evidence_b/registration_sites_build.txt`).

## Registrations

| id | owner module | positive site | mutant |
|---|---|---|---|
| AK-3 | `ResiduaRCCDigestBinding` (`Residua.RCC.Addressing`) | `reuse`/`miss`, conditional address↔bytes iff | constant-digest → named `collision`; `mutant_injectivity_impossible` |
| DQ-1 | `ResiduaRCCDefeqFragment` | both classifier iffs at concrete terms; residue locates `mul` | accept-all mutant proven unsound |
| CM-1 | `ResiduaRCCClaimModality` | matched-envelope alignment; six-modality index enumerated | caller-tag mutant accepts what the boundary refuses |
| FC-2 | `ResiduaRCCFacetCoherence`(+Tests) | seven live bridges at the sealed-snapshot fixture | cross-snapshot bind, detached payload, missing resource delta |

**FC-2 audit note (class C remainder):** the obligation names eight facets —
addressing, evidence, reduction, resources, reflection, runtime, migration,
composition. All seven bridge laws covering them exist with live bridges and
refusals; the "bridge laws that have no module" remainder is **empty** after
this audit (recorded in the FC-2 entry's scope).

## Verdict delta (the executable, never asserted)

| Reading | class A | **after B** |
|---|---|---|
| literal | 14 open | **10 open** |
| strict | 15 open | **11 open** |

`raw/rcc_evidence_b/` has coverage, both graphs, the verdict text. Remaining:
`FC-3 RC-2` (class C), the 8 named gaps (class D), `R1` (class E).

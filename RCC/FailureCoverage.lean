/-!
# RCC-32 Failure-Mode Evidence Coverage

This module proves the safety half of ADR §22.1 / §22.10: relative to one
declared finite failure universe and one opaque evidence context, every
mandatory failure mode has evidence explicitly admitted for mandatory
coverage of that same mode.

The finite enumeration is proof-carrying.  An empty scan is never enough to
prove absence: callers must supply soundness and completeness for the declared
scope.  Coverage additionally refuses an empty mandatory set, an empty
evidence bundle, wrong-mode evidence, optional-grade evidence, and an unsealed
universe.

`AdmittedAt` and `CoversAt` are relational inputs.  This kernel does not claim
that an implementation extracts them faithfully, that the declared universe
is a complete real-world threat model, that evidence remains currently usable,
that the opaque evidence carrier has a faithful concrete address, that aliases
are deduplicated, or that pieces of evidence are independent.  Those are
runtime-refinement, policy-root, RCC-37, AddressKernel/RCC-36, and RCC-33
obligations respectively.

Prelude-only Lean 4.14; no Mathlib and no custom axioms.  The exported theorem
surface may report Lean's standard `propext`.
-/

namespace Residua.RCC.FailureCoverage

universe u v w

/--
The declared failure universe separates the semantic scope predicate from its
finite enumeration.  `mandatoryInScope` prevents policy from requiring an
unscanned failure mode.
-/
structure FailureUniverse (FailureMode : Type u) where
  inScope : FailureMode → Prop
  mandatory : FailureMode → Prop
  mandatoryInScope :
    ∀ failure, mandatory failure → inScope failure
  declared : List FailureMode

/--
Closed-world certificate for one declared finite universe.

`declaredSound` prevents irrelevant entries from pretending to be the scope.
`declaredComplete` is the load-bearing negative-claim premise: every in-scope
failure occurs in the finite enumeration.
-/
structure FailureUniverseSeal
    {FailureMode : Type u} (model : FailureUniverse FailureMode) : Prop where
  declaredSound :
    ∀ failure, failure ∈ model.declared → model.inScope failure
  declaredComplete :
    ∀ failure, model.inScope failure → failure ∈ model.declared

/--
The policy grade under which one admitted evidence item may cover one failure.
Optional context remains valuable, but cannot be upgraded into mandatory
coverage.
-/
inductive CoverageGrade where
  | mandatory
  | optional
  deriving DecidableEq, Repr

/--
Relational evidence authority at one context.

`Context` is intentionally opaque: a concrete RCC instance may use it to bind
epoch, sealed window, canonical head, and assumption root.  Evidence is a
generic carrier rather than a freely constructible self-grading row.

The two relations are separate because an item may be admitted evidence yet
not support every failure or grade.  Their runtime derivation and authenticity
remain refinement obligations.
-/
structure FailureEvidenceSystem
    (Context : Type u) (FailureMode : Type v) (Evidence : Type w) where
  modelAt : Context → FailureUniverse FailureMode
  AdmittedAt : Context → Evidence → Prop
  CoversAt : Context → Evidence → FailureMode → CoverageGrade → Prop

/--
One item covers a mandatory requirement only when the same evidence context
both admits it and grants mandatory-grade coverage for that exact failure.
-/
def CoversMandatoryAt
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (evidence : Evidence)
    (failure : FailureMode) : Prop :=
  system.AdmittedAt context evidence ∧
    system.CoversAt context evidence failure .mandatory

/--
The universe lifecycle distinguishes a proof-carrying seal from an open
enumeration.  The unsealed constructor carries no absence authority.
-/
inductive FailureUniverseStatus
    {FailureMode : Type u} (model : FailureUniverse FailureMode) where
  | unsealed
  | sealed (certificate : FailureUniverseSeal model)

/--
Proof-carrying RCC-32 coverage for one evidence bundle.

`mandatoryNonempty` blocks the policy-vacuity case.  Together with
`everyMandatoryCovered`, it mechanically implies that the evidence bundle is
nonempty; callers do not provide a second, potentially disconnected flag.
-/
structure FailureCoverageCertificate
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (_seal : FailureUniverseSeal (system.modelAt context))
    (evidence : List Evidence) : Prop where
  mandatoryNonempty :
    ∃ failure, (system.modelAt context).mandatory failure
  everyMandatoryCovered :
    ∀ failure, (system.modelAt context).mandatory failure →
      ∃ item, item ∈ evidence ∧
        CoversMandatoryAt system context item failure

/--
The only admitted coverage state.  An unsealed universe reduces to `False`;
a sealed universe must carry the complete RCC-32 certificate.
-/
def CoverageAdmissible
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (status : FailureUniverseStatus (system.modelAt context))
    (evidence : List Evidence) : Prop :=
  match status with
  | .unsealed => False
  | .sealed certificate =>
      FailureCoverageCertificate system context certificate evidence

/--
A mandatory failure lacking admitted mandatory-grade evidence in this exact
context and bundle.
-/
def UncoveredMandatory
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (evidence : List Evidence)
    (failure : FailureMode) : Prop :=
  (system.modelAt context).mandatory failure ∧
    ¬ ∃ item, item ∈ evidence ∧
      CoversMandatoryAt system context item failure

/--
RCC-32: every mandatory failure mode has admitted, exact mandatory-grade
evidence in the same context.
-/
theorem every_mandatory_failure_has_covering_evidence
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (coverageSeal : FailureUniverseSeal (system.modelAt context))
    (evidence : List Evidence)
    (coverage :
      FailureCoverageCertificate system context coverageSeal evidence) :
    ∀ failure, (system.modelAt context).mandatory failure →
      ∃ item, item ∈ evidence ∧
        CoversMandatoryAt system context item failure := by
  exact coverage.everyMandatoryCovered

/-- Every item projected by RCC-32's headline theorem is actually admitted. -/
theorem covering_evidence_is_admitted
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (evidence : Evidence)
    (failure : FailureMode)
    (covers : CoversMandatoryAt system context evidence failure) :
    system.AdmittedAt context evidence :=
  covers.1

/--
Mandatory nonemptiness plus coverage derives bundle nonemptiness.  No separate
caller-supplied `evidenceNonempty` flag can disguise an empty bundle.
-/
theorem coverage_bundle_nonempty
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (coverageSeal : FailureUniverseSeal (system.modelAt context))
    (evidence : List Evidence)
    (coverage :
      FailureCoverageCertificate system context coverageSeal evidence) :
    evidence ≠ [] := by
  intro empty
  obtain ⟨failure, mandatory⟩ := coverage.mandatoryNonempty
  obtain ⟨item, member, _⟩ :=
    coverage.everyMandatoryCovered failure mandatory
  rw [empty] at member
  simp at member

/--
The equivalent negative conclusion is lawful only because it consumes the
sealed finite universe and its coverage certificate.
-/
theorem failure_coverage_has_no_uncovered_mandatory
    {Context : Type u} {FailureMode : Type v} {Evidence : Type w}
    (system : FailureEvidenceSystem Context FailureMode Evidence)
    (context : Context)
    (coverageSeal : FailureUniverseSeal (system.modelAt context))
    (evidence : List Evidence)
    (coverage :
      FailureCoverageCertificate system context coverageSeal evidence) :
    ¬ ∃ failure, UncoveredMandatory system context evidence failure := by
  rintro ⟨failure, mandatory, uncovered⟩
  exact uncovered
    (coverage.everyMandatoryCovered failure mandatory)

/--
Absence from the finite list implies absence from the declared scope only
through the universe completeness certificate.
-/
theorem not_declared_not_in_scope
    {FailureMode : Type u}
    (model : FailureUniverse FailureMode)
    (coverageSeal : FailureUniverseSeal model)
    (failure : FailureMode)
    (notDeclared : failure ∉ model.declared) :
    ¬ model.inScope failure := by
  intro inScope
  exact notDeclared (coverageSeal.declaredComplete failure inScope)

/-- Mandatory failures are necessarily members of the sealed enumeration. -/
theorem mandatory_failure_is_declared
    {FailureMode : Type u}
    (model : FailureUniverse FailureMode)
    (coverageSeal : FailureUniverseSeal model)
    (failure : FailureMode)
    (mandatory : model.mandatory failure) :
    failure ∈ model.declared := by
  exact coverageSeal.declaredComplete failure
    (model.mandatoryInScope failure mandatory)

end Residua.RCC.FailureCoverage

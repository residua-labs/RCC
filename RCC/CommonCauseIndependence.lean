import RCC.FailureCoverage

/-!
# RCC-33 Common-Cause Independence

Evidence multiplicity is not evidence independence.  For one mandatory failure
mode, a fault-domain cut breaks an RCC-32-admitted support bundle when every
evidence item in the bundle depends on at least one domain in the cut.
Independence at threshold `k` means that every valid breaking cut costs at
least `k`.

The topology is closed-world only because its RCC-32 evidence context and
fault-domain universe carry finite soundness/completeness witnesses.  The
kernel counts only evidence admitted in that same context and granted
mandatory-grade coverage for the exact failure mode.  It does not infer
independence from evidence count, public-key count, engine count, actor labels,
or string inequality.

This is a logical topology theorem.  It deliberately does not prove that the
declared custodian, host, generator, or other physical fault domains match the
real world.  Authenticity of that observation remains an explicit RCC
assumption/source-window obligation.  The `FaultDomain` carrier is the
instance's declared canonical logical domain; alias/lineage canonicalization
and concrete topology invalidation remain RCC-36/RCC-37 obligations.

Prelude-only Lean 4.14; no Mathlib, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.CommonCause

open Residua.RCC.FailureCoverage

universe u v w x

/--
A finite topology over one exact RCC-32 evidence context.

`evidenceSound` and `evidenceComplete` seal precisely the evidence admitted by
RCC-32 in this context; an arbitrary member of the carrier cannot enter a cut
independence judgment.  `failureUniverseSeal` seals the RCC-32 failure model.

`dependsFor` is indexed by failure mode: the same evidence may be independent
for one failure and correlated for another.  `dependencyRooted` prevents an
evidence item with no declared root from acquiring infinite independence by
vacuity.  The full sealed domain universe therefore breaks every nonempty
admitted support bundle.
-/
structure SealedFiniteTopology
    (Context : Type u) (Evidence : Type v)
    (FailureMode : Type w) (FaultDomain : Type x) where
  evidenceSystem : FailureEvidenceSystem Context FailureMode Evidence
  context : Context
  failureUniverseSeal :
    FailureUniverseSeal (evidenceSystem.modelAt context)
  evidenceUniverse : List Evidence
  faultDomainUniverse : List FaultDomain
  evidenceNoDup : evidenceUniverse.Nodup
  faultDomainNoDup : faultDomainUniverse.Nodup
  evidenceSound :
    ∀ evidence, evidence ∈ evidenceUniverse →
      evidenceSystem.AdmittedAt context evidence
  evidenceComplete :
    ∀ evidence, evidenceSystem.AdmittedAt context evidence →
      evidence ∈ evidenceUniverse
  faultDomainComplete : ∀ domain, domain ∈ faultDomainUniverse
  dependsFor : Evidence → FailureMode → FaultDomain → Prop
  dependencyRooted :
    ∀ evidence failureMode,
      evidence ∈ evidenceUniverse →
      CoversMandatoryAt evidenceSystem context evidence failureMode →
      ∃ domain,
        domain ∈ faultDomainUniverse ∧
          dependsFor evidence failureMode domain
  domainCost : FaultDomain → Nat
  domainCostPositive : ∀ domain, 0 < domainCost domain

/--
The exact support bundle admitted for one RCC-32 mandatory failure.

The bundle is nonempty, the failure is mandatory in the same context, and
every counted item is both in the sealed admitted universe and granted
mandatory-grade coverage for this exact failure.  Irrelevant or merely
optional evidence cannot inflate a cut.
-/
structure AdmittedSupportBundle
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (failureMode : FailureMode)
    (bundle : List Evidence) : Prop where
  failureMandatory :
    (topology.evidenceSystem.modelAt topology.context).mandatory failureMode
  nonempty : bundle ≠ []
  everyItemSupports :
    ∀ evidence, evidence ∈ bundle →
      evidence ∈ topology.evidenceUniverse ∧
        CoversMandatoryAt
          topology.evidenceSystem topology.context evidence failureMode

/--
A valid cut has no duplicate domains and contains only domains from the sealed
fault-domain universe.
-/
def ValidCut
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (cut : List FaultDomain) : Prop :=
  cut.Nodup ∧
    ∀ domain, domain ∈ cut → domain ∈ topology.faultDomainUniverse

/--
The cut breaks the bundle for the declared failure mode when every evidence
item has a dependency root in the cut.
-/
def BreaksBundle
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (failureMode : FailureMode)
    (bundle : List Evidence)
    (cut : List FaultDomain) : Prop :=
  ∀ evidence, evidence ∈ bundle →
    ∃ domain,
      domain ∈ cut ∧ topology.dependsFor evidence failureMode domain

/-- Additive policy cost of a fault-domain cut. -/
def CutCost
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain) :
    List FaultDomain → Nat
  | [] => 0
  | domain :: rest => topology.domainCost domain + CutCost topology rest

/--
Independence at threshold `required` is a universal lower bound over all valid
breaking cuts.  It is not a count of evidence items.
-/
def IndependentAtLeast
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (failureMode : FailureMode)
    (bundle : List Evidence)
    (required : Nat) : Prop :=
  AdmittedSupportBundle topology failureMode bundle ∧
    ∀ cut,
      ValidCut topology cut →
      BreaksBundle topology failureMode bundle cut →
      required ≤ CutCost topology cut

/-- RCC-33 can count only evidence admitted by RCC-32 in the exact context. -/
theorem independent_bundle_item_is_admitted
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {failureMode : FailureMode} {bundle : List Evidence} {required : Nat}
    (independent :
      IndependentAtLeast topology failureMode bundle required)
    (evidence : Evidence)
    (member : evidence ∈ bundle) :
    topology.evidenceSystem.AdmittedAt topology.context evidence := by
  exact (independent.1.everyItemSupports evidence member).2.1

/-- Every RCC-33 headline claim is indexed by an RCC-32 mandatory failure. -/
theorem independent_failure_is_mandatory
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {failureMode : FailureMode} {bundle : List Evidence} {required : Nat}
    (independent :
      IndependentAtLeast topology failureMode bundle required) :
    (topology.evidenceSystem.modelAt topology.context).mandatory failureMode :=
  independent.1.failureMandatory

/--
A proof-carrying exact minimum cut.  Its minimality quantifies over every valid
cut in the sealed domain universe, so an empty scanner result is never enough.
-/
structure MinimumCutCertificate
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (failureMode : FailureMode)
    (bundle : List Evidence) where
  supportBundle : AdmittedSupportBundle topology failureMode bundle
  cut : List FaultDomain
  cutValid : ValidCut topology cut
  breaks : BreaksBundle topology failureMode bundle cut
  minimal :
    ∀ candidate,
      ValidCut topology candidate →
      BreaksBundle topology failureMode bundle candidate →
      CutCost topology cut ≤ CutCost topology candidate

/-- A nonempty cut has positive cost because each declared domain does. -/
theorem cut_cost_positive_of_nonempty
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (cut : List FaultDomain)
    (nonempty : cut ≠ []) :
    0 < CutCost topology cut := by
  cases cut with
  | nil =>
      exact False.elim (nonempty rfl)
  | cons domain rest =>
      change 0 < topology.domainCost domain + CutCost topology rest
      exact Nat.add_pos_left (topology.domainCostPositive domain) _

/--
The complete sealed domain universe is a lawful cut that breaks every admitted
support bundle.  Consequently, the minimum-cut obligation cannot become true
merely because no breaking cut exists.
-/
theorem full_domain_universe_breaks_support
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    (topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain)
    (failureMode : FailureMode)
    (bundle : List Evidence)
    (support : AdmittedSupportBundle topology failureMode bundle) :
    ValidCut topology topology.faultDomainUniverse ∧
      BreaksBundle topology failureMode bundle topology.faultDomainUniverse := by
  constructor
  · exact ⟨topology.faultDomainNoDup, fun _ member => member⟩
  · intro evidence member
    have supported := (support.everyItemSupports evidence member)
    exact topology.dependencyRooted evidence failureMode supported.1 supported.2

/--
Every RCC-33 independence claim has at least one valid breaking cut.  Thus a
rootless dependency graph cannot prove an arbitrary threshold by vacuity.
-/
theorem independent_has_breaking_cut
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {failureMode : FailureMode} {bundle : List Evidence} {required : Nat}
    (independent :
      IndependentAtLeast topology failureMode bundle required) :
    ∃ cut,
      ValidCut topology cut ∧
        BreaksBundle topology failureMode bundle cut := by
  exact
    ⟨topology.faultDomainUniverse,
      full_domain_universe_breaks_support
        topology failureMode bundle independent.1⟩

/--
An exact minimum-cut certificate whose cost meets the policy threshold proves
common-cause independence at that threshold.
-/
theorem minimum_cut_meets_requirement
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {failureMode : FailureMode} {bundle : List Evidence} {required : Nat}
    (certificate :
      MinimumCutCertificate topology failureMode bundle)
    (meets : required ≤ CutCost topology certificate.cut) :
    IndependentAtLeast topology failureMode bundle required := by
  constructor
  · exact certificate.supportBundle
  · intro candidate candidateValid candidateBreaks
    exact Nat.le_trans meets
      (certificate.minimal candidate candidateValid candidateBreaks)

/--
If the exact minimum cut costs less than the policy threshold, the bundle is
not independent enough for that declared failure mode.
-/
theorem minimum_cut_below_requirement_refutes
    {Context : Type u} {Evidence : Type v}
    {FailureMode : Type w} {FaultDomain : Type x}
    {topology :
      SealedFiniteTopology Context Evidence FailureMode FaultDomain}
    {failureMode : FailureMode} {bundle : List Evidence} {required : Nat}
    (certificate :
      MinimumCutCertificate topology failureMode bundle)
    (below : CutCost topology certificate.cut < required) :
    ¬ IndependentAtLeast topology failureMode bundle required := by
  intro independent
  have requiredAtMostMinimum :
      required ≤ CutCost topology certificate.cut :=
    independent.2 certificate.cut certificate.cutValid certificate.breaks
  exact (Nat.not_le_of_lt below) requiredAtMostMinimum

end Residua.RCC.CommonCause

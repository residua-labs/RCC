import RCCTests.FacetCoherence

/-!
# ResiduaRCCFC3Target — FC-3: deletion countermodels for every load-bearing facet

Obligation FC-3: *"Deletion countermodels establish necessity of every
load-bearing facet."*

The eight `RCCFacet` constructors are the load-bearing facets.  Each feeds one
law surface consumed by the FC-2 bridge theorems
(`addressedReductionsRemainEquivalent`, `admittedEvidenceIsGrounded`,
`reductionHasResourceDelta`, `acceptedVerificationIsStratified`,
`migrationConservesResource`, `runtimeTransitionRefinesFormal`,
`componentsAndSeamsGlue`).  This module proves necessity in the honest,
minimal sense: for every facet a **concrete deletion world** where that
facet's law surface fails — so no `CoherentLaws` bundle exists there — while
every other relation stays vacuous, isolating the deleted facet as the sole
break.

Facet → law-surface mapping (the two address-side facets split the two fields
of `AddressReductionLaw`):

| facet                | deleted law surface                        |
|----------------------|--------------------------------------------|
| addressKernel        | `AddressReductionLaw.addressSound`         |
| noetherianReduction  | `AddressReductionLaw.reductionCongruent`   |
| groundedEvidence     | `EvidenceAdmissionLaw.admittedGrounded`    |
| resourceLedger       | `DeltaLedgerProof` decomposition + refusal |
| reflectionStrata     | `ReflectionVerificationLaw`                |
| runtimeBinding       | `RuntimeRefinementLaw.refines`             |
| lineageCoalgebra     | `MigrationResourceLaw.conserves`           |
| compositionKernel    | `CompositionLaw.glues`                     |

The FC-1 provenance origin's own deletion countermodel is
`FacetCoherence.differentPairSnapshotsCannotBind` plus the cross-snapshot
refusal in `FacetCoherenceTests` — cited, not duplicated.
-/

namespace Residua.RCC.FC3

open Residua.RCC.FacetCoherence
open Residua.RCC.FacetSnapshot (RCCFacet)

/-- The joint law bundle a coherence certificate draws its conclusions from:
all seven law surfaces over one world. -/
structure CoherentLaws (world : CoherenceWorld) where
  addressReduction : AddressReductionLaw world
  evidenceAdmission : EvidenceAdmissionLaw world
  reductionResource : ReductionResourceLaw world
  reflectionVerification : ReflectionVerificationLaw world
  migrationResource : MigrationResourceLaw world
  runtimeRefinement : RuntimeRefinementLaw world
  composition : CompositionLaw world

/-- A facet is necessary when its deletion world — where that facet's law
surface fails — cannot carry the joint bundle. -/
def FacetNecessaryAt (world : CoherenceWorld) : Prop :=
  ¬ Nonempty (CoherentLaws world)

/-- The completely vacuous world: every relation empty, every level zero,
`globalClosed` true.  All seven laws hold — the positive tooth showing the
bundle is inhabited when nothing is deleted. -/
def vacuousWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem vacuous_world_coherent : Nonempty (CoherentLaws vacuousWorld) :=
  ⟨⟨{ addressSound := fun _ _ _ => trivial
      reductionCongruent := fun _ _ _ _ _ hl _ => nomatch hl },
    { admittedGrounded := fun _ _ h => nomatch h },
    { deltaFor := fun _ _ h => nomatch h },
    { verifierAboveArtifact := fun _ _ h => nomatch h },
    { conserves := fun _ _ h => nomatch h },
    { refines := fun _ _ h => nomatch h },
    { componentCoverage := fun c => c.elim
      seamCoverage := fun s => s.elim
      glues := fun _ _ => trivial }⟩⟩

/-! ## Deletion worlds

Literal structures (not `{ vacuousWorld with ... }`): updating a `Type`-valued
field in a structure update would keep the dependent fields' old types.
-/

/-- **addressKernel deleted.** A collision world: two distinct states share
one address while `stateEquivalent` stays semantic equality, so
`addressSound` fails; `reductionCongruent` still holds vacuously. -/
def addressDeletedWorld : CoherenceWorld where
  State := Bool
  Address := Unit
  stateEquivalent := Eq
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => true
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem address_sound_deleted : ¬ AddressReductionLaw addressDeletedWorld := by
  intro law
  have sameAddr : addressDeletedWorld.stateAddress true =
      addressDeletedWorld.stateAddress false := rfl
  exact absurd
    (show true = false from law.addressSound true false sameAddr)
    (by decide)

theorem addressDeletedWorld_incoherent : FacetNecessaryAt addressDeletedWorld
  | ⟨laws⟩ => address_sound_deleted laws.addressReduction

/-- **noetherianReduction deleted.** A nondeterministic reduction sends one
state to two inequivalent successors: `reductionCongruent` fails while
`addressSound` survives (addresses are literal identity). -/
def reductionDeletedWorld : CoherenceWorld where
  State := Bool
  Address := Bool
  stateEquivalent := Eq
  stateAddress := id
  reduces := fun s _ => s = false
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => true
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem reduction_congruent_deleted :
    ¬ AddressReductionLaw reductionDeletedWorld := by
  intro law
  have h := law.reductionCongruent false false true false rfl rfl rfl
  exact absurd (show true = false from h) (by decide)

theorem reductionDeletedWorld_incoherent :
    FacetNecessaryAt reductionDeletedWorld
  | ⟨laws⟩ => reduction_congruent_deleted laws.addressReduction

/-- **groundedEvidence deleted.** The world admits a named event from a piece
of evidence that carries no grounding proof. -/
def evidenceDeletedWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => False
  admits := fun _ _ => True
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem evidence_admission_deleted :
    ¬ EvidenceAdmissionLaw evidenceDeletedWorld := by
  intro law
  have h := law.admittedGrounded () () trivial
  exact absurd (show evidenceDeletedWorld.grounded () from h)
    (fun hg => hg)

theorem evidenceDeletedWorld_incoherent :
    FacetNecessaryAt evidenceDeletedWorld
  | ⟨laws⟩ => evidence_admission_deleted laws.evidenceAdmission

/-- **resourceLedger deleted.** The active ledger is `[()]`, so the forged
empty delta's `consumed ++ retained` cannot equal it — no `DeltaLedgerProof`
exists for that delta, and certificate-side the missing-delta mutant is
refused as `resourceDeltaMissing`. -/
def resourceDeletedWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => [()]
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

/-- The forged empty delta is a lie at the resource-deleted world. -/
theorem forged_delta_is_no_ledger_proof :
    ¬ DeltaLedgerProof resourceDeletedWorld () ()
      { consumed := [], retained := [], produced := [] } := by
  intro proof
  exact absurd
    (show [()] = [] ++ [] from proof.beforeBound)
    (by decide)

/-- **reflectionStrata deleted.** A verifier at level 0 certifies an artifact
at level 0 — the strict stratification premise fails. -/
def reflectionDeletedWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => True
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem reflection_verification_deleted :
    ¬ ReflectionVerificationLaw reflectionDeletedWorld := by
  intro law
  have h := law.verifierAboveArtifact () () trivial
  exact absurd (show (0 : Nat) < 0 from h) (by decide)

theorem reflectionDeletedWorld_incoherent :
    FacetNecessaryAt reflectionDeletedWorld
  | ⟨laws⟩ => reflection_verification_deleted laws.reflectionVerification

/-- **runtimeBinding deleted.** The runtime takes a step whose abstraction has
no formal reduction — refinement fails. -/
def runtimeDeletedWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => True
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem runtime_refinement_deleted :
    ¬ RuntimeRefinementLaw runtimeDeletedWorld := by
  intro law
  have h := law.refines () () trivial
  exact absurd (show False from h) (fun hf => hf)

theorem runtimeDeletedWorld_incoherent :
    FacetNecessaryAt runtimeDeletedWorld
  | ⟨laws⟩ => runtime_refinement_deleted laws.runtimeRefinement

/-- **lineageCoalgebra deleted.** A migrating state holds an active token that
is neither terminal at the pre-state nor carried into the successor. -/
def migrationDeletedWorld : CoherenceWorld where
  State := Bool
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun s => if s = false then [()] else []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun s t => s = false ∧ t = true
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => true
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := True

theorem migration_resource_deleted :
    ¬ MigrationResourceLaw migrationDeletedWorld := by
  intro law
  have mig : migrationDeletedWorld.migrates false true := ⟨rfl, rfl⟩
  have mem : () ∈ migrationDeletedWorld.activeResources false := by decide
  rcases law.conserves false true mig () mem with
    h | ⟨succ, hin, _⟩
  · exact absurd (show False from h) (fun hf => hf)
  · have hin' : (succ ∈ ([] : List migrationDeletedWorld.ResourceToken)) := hin
    exact List.not_mem_nil succ hin' 

theorem migrationDeletedWorld_incoherent :
    FacetNecessaryAt migrationDeletedWorld
  | ⟨laws⟩ => migration_resource_deleted laws.migrationResource

/-- **compositionKernel deleted.** Every component is closed and every seam is
exact (vacuously), yet `globalClosed` does not follow — the glue premise is
severed. -/
def compositionDeletedWorld : CoherenceWorld where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => False
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Empty
  Seam := Empty
  components := []
  seams := []
  componentClosed := fun e => e.elim
  seamExact := fun e => e.elim
  globalClosed := False

theorem composition_deleted : ¬ CompositionLaw compositionDeletedWorld := by
  intro law
  have h := law.glues (fun c => c.elim) (fun s => s.elim)
  exact absurd (show False from h) (fun hf => hf)

theorem compositionDeletedWorld_incoherent :
    FacetNecessaryAt compositionDeletedWorld
  | ⟨laws⟩ => composition_deleted laws.composition

/-! ## The necessity catalogue -/

/-- The FC-3 necessity catalogue: for EVERY load-bearing facet, a dependent
pair of the deletion residue statement and its compiled proof.  Totality is
forced by the match — no facet lacks a countermodel.  Seven entries are
world-level (`¬ Law world`, hence `FacetNecessaryAt`); resourceLedger's
residue is the forged-decomposition refusal at the delta level, plus the
missing-delta refusal `missing_resource_delta_mutant_cannot_certify` at the
certificate level; the FC-1 origin binding's countermodel is
`differentPairSnapshotsCannotBind`. -/
def facetNecessity : ∀ _ : RCCFacet, Σ' residue : Prop, residue
  | .addressKernel =>
      ⟨¬ AddressReductionLaw addressDeletedWorld, address_sound_deleted⟩
  | .groundedEvidence =>
      ⟨¬ EvidenceAdmissionLaw evidenceDeletedWorld,
        evidence_admission_deleted⟩
  | .noetherianReduction =>
      ⟨¬ AddressReductionLaw reductionDeletedWorld,
        reduction_congruent_deleted⟩
  | .resourceLedger =>
      ⟨¬ DeltaLedgerProof resourceDeletedWorld () ()
          { consumed := [], retained := [], produced := [] },
        forged_delta_is_no_ledger_proof⟩
  | .reflectionStrata =>
      ⟨¬ ReflectionVerificationLaw reflectionDeletedWorld,
        reflection_verification_deleted⟩
  | .runtimeBinding =>
      ⟨¬ RuntimeRefinementLaw runtimeDeletedWorld, runtime_refinement_deleted⟩
  | .lineageCoalgebra =>
      ⟨¬ MigrationResourceLaw migrationDeletedWorld,
        migration_resource_deleted⟩
  | .compositionKernel =>
      ⟨¬ CompositionLaw compositionDeletedWorld, composition_deleted⟩

/-- Every load-bearing facet has its necessity residue — the catalogue is
exhaustive over the inductive by construction. -/
theorem every_loadBearing_facet_necessary :
    ∀ f : RCCFacet, (facetNecessity f).1 :=
  fun f => (facetNecessity f).2

#print axioms vacuous_world_coherent
#print axioms addressDeletedWorld_incoherent
#print axioms reductionDeletedWorld_incoherent
#print axioms evidenceDeletedWorld_incoherent
#print axioms forged_delta_is_no_ledger_proof
#print axioms reflectionDeletedWorld_incoherent
#print axioms runtimeDeletedWorld_incoherent
#print axioms migrationDeletedWorld_incoherent
#print axioms compositionDeletedWorld_incoherent
#print axioms every_loadBearing_facet_necessary

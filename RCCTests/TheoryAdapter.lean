import RCC.TheoryAdapter

/-!
# RCC TA-1 theory-import firewall countermodels

The fixtures show one lawful Newman transfer, one RCC-native Grade-B proof,
and one Grade-C interpretive lineage.  They then pin the forbidden shortcuts:
analogy-as-proof, missing theorem bridge, unmet source assumptions, Newman
without local confluence, and coalgebraic finality used as normal-form proof.
-/

namespace Residua.RCC.TheoryAdapter.Tests

open Residua.RCC.TheoryAdapter

inductive SourceObject
  | abstractReduction

inductive RCCObject
  | internalAdvanced

inductive SourceAssumptions
  | available

inductive RCCAssumptions
  | ready
  | incomplete

inductive SourceTheorem
  | confluence
  | bisimulation

inductive RCCTheorem
  | scheduleIndependent
  | lineageEquivalent
  | nativeGroundedness
  deriving DecidableEq, Repr

inductive TerminationCertificate
  | decreasingMeasure

inductive LocalConfluenceCertificate
  | localDiamond

abbrev Adapter :=
  TheoryCollisionAdapter
    SourceObject RCCObject SourceAssumptions RCCAssumptions
    SourceTheorem RCCTheorem TerminationCertificate
    LocalConfluenceCertificate

def coordinates : TheoryAdapterCoordinates where
  facetQ := "rcc:noetherian-reduction"
  sourceTheoryQ := "theory:abstract-rewriting"
  sourceObjectsQ := "source:reduction-system"
  rccObjectsQ := "rcc:internal-advanced-relation"
  mismatchResidue := "[borrowed_theorem_scope_mismatch]"

def lawfulNewmanAdapter : Adapter where
  coordinates := coordinates
  grade := .theoremTransfer
  family := .newmanConfluence
  targetRole := .internalAdvancedConfluence
  objectTranslationQ := some "bridge:advanced-as-reduction"
  objectTranslation := some fun _ => .internalAdvanced
  assumptionTranslationQ := some "bridge:rcc-assumptions-to-newman"
  assumptionTranslation := some fun
    | .ready => some .available
    | .incomplete => none
  borrowedTheoremQ := some "theorem:newman"
  borrowedTheorem := some fun _ => .confluence
  bridgeTheoremQ := some "bridge:newman-to-rcc-confluence"
  theoremBridge := some fun
    | .confluence => .scheduleIndependent
    | .bisimulation => .lineageEquivalent
  rccReproofQ := none
  rccReproof := none
  terminationEvidence := some .decreasingMeasure
  localConfluenceEvidence := some .localDiamond
  interpretation := none

theorem lawful_grade_A_transfer_imports_theorem :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .ready =
      TheoryDependencyResult.imported .scheduleIndependent := by
  rfl

theorem imported_result_requires_grade_A :
    lawfulNewmanAdapter.grade = .theoremTransfer :=
  imported_dependency_requires_grade_A
    lawfulNewmanAdapter .ready (by rfl)

def groundednessTemplateAdapter : Adapter where
  coordinates :=
    { coordinates with
      facetQ := "rcc:grounded-evidence"
      sourceTheoryQ := "theory:well-founded-semantics" }
  grade := .proofTemplate
  family := .generic
  targetRole := .generic
  objectTranslationQ := none
  objectTranslation := none
  assumptionTranslationQ := none
  assumptionTranslation := none
  borrowedTheoremQ := none
  borrowedTheorem := none
  bridgeTheoremQ := none
  theoremBridge := none
  rccReproofQ := some "rcc-proof:grounded-support-rank"
  rccReproof := some fun _ => .nativeGroundedness
  terminationEvidence := none
  localConfluenceEvidence := none
  interpretation := none

theorem grade_B_uses_only_RCC_native_reproof :
    deriveTheoryDependency
        groundednessTemplateAdapter .proofDependency .ready =
      TheoryDependencyResult.locallyProved .nativeGroundedness := by
  rfl

def autopoiesisAnalogyAdapter : Adapter where
  coordinates :=
    { coordinates with
      facetQ := "rcc:institution-growth"
      sourceTheoryQ := "lineage:autopoiesis" }
  grade := .interpretiveAnalogy
  family := .generic
  targetRole := .generic
  objectTranslationQ := none
  objectTranslation := none
  assumptionTranslationQ := none
  assumptionTranslation := none
  borrowedTheoremQ := none
  borrowedTheorem := none
  bridgeTheoremQ := none
  theoremBridge := none
  rccReproofQ := none
  rccReproof := none
  terminationEvidence := none
  localConfluenceEvidence := none
  interpretation := some "operationally self-producing institution"

theorem interpretive_lineage_remains_non_authoritative :
    deriveTheoryDependency
        autopoiesisAnalogyAdapter .interpretiveCitation .ready =
      TheoryDependencyResult.interpretiveOnly := by
  rfl

/-! ## Mutant 1: interpretive analogy presented as proof. -/

theorem analogy_as_proof_is_refused :
    deriveTheoryDependency
        autopoiesisAnalogyAdapter .proofDependency .ready =
      TheoryDependencyResult.refuse
        .theoryAnalogyPresentedAsProof :=
  interpretive_analogy_never_enters_proof_dependencies
    autopoiesisAnalogyAdapter rfl .ready

/-! ## Mutant 2: citation and object mapping exist, theorem bridge is absent. -/

def missingBridgeAdapter : Adapter :=
  { lawfulNewmanAdapter with
      bridgeTheoremQ := none
      theoremBridge := none }

theorem missing_bridge_is_refused :
    deriveTheoryDependency missingBridgeAdapter .proofDependency .ready =
      TheoryDependencyResult.refuse
        .theoremTransferAdapterMissing := by
  rfl

/-! ## Mutant 3: the source theorem assumptions do not follow. -/

theorem unmet_borrowed_assumptions_are_refused :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .incomplete =
      TheoryDependencyResult.refuse
        .borrowedTheoremAssumptionsUnmet := by
  rfl

/-! ## Mutant 4: Newman transfer without local confluence. -/

def newmanWithoutLocalConfluence : Adapter :=
  { lawfulNewmanAdapter with
      localConfluenceEvidence := none }

theorem newman_without_local_confluence_is_refused :
    deriveTheoryDependency
        newmanWithoutLocalConfluence .proofDependency .ready =
      TheoryDependencyResult.refuse
        .newmanWithoutLocalConfluence := by
  rfl

/-! ## Mutant 5: final-coalgebra reasoning presented as canonical NF. -/

def coalgebraAsNormalForm : Adapter :=
  { lawfulNewmanAdapter with
      family := .coalgebraFinality
      targetRole := .canonicalNormalForm
      terminationEvidence := none
      localConfluenceEvidence := none }

theorem coalgebra_finality_cannot_prove_normal_form :
    deriveTheoryDependency
        coalgebraAsNormalForm .proofDependency .ready =
      TheoryDependencyResult.refuse
        .coalgebraFinalityMisusedAsNormalForm := by
  rfl

end Residua.RCC.TheoryAdapter.Tests

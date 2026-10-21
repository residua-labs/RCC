import RCCTests.TheoryAdapter

/-! RCC-65 candidate: theory-transfer firewall and scope mutants. -/

namespace Residua.RCC.RCC65Target

open Residua.RCC.TheoryAdapter.Tests
open Residua.RCC.TheoryAdapter

def gradeATransfer := lawful_grade_A_transfer_imports_theorem
def gradeBReproof := grade_B_uses_only_RCC_native_reproof
def gradeCNonAuthoritative := interpretive_lineage_remains_non_authoritative
def analogyRefused := analogy_as_proof_is_refused
def missingBridgeRefused := missing_bridge_is_refused
def unmetAssumptionRefused := unmet_borrowed_assumptions_are_refused
def missingLocalConfluenceRefused := newman_without_local_confluence_is_refused
def coalgebraNormalFormRefused := coalgebra_finality_cannot_prove_normal_form

structure Certificate where
  gradeATransfer :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .ready =
      TheoryDependencyResult.imported .scheduleIndependent
  gradeBReproof :
    deriveTheoryDependency
        groundednessTemplateAdapter .proofDependency .ready =
      TheoryDependencyResult.locallyProved .nativeGroundedness
  gradeCNonAuthoritative :
    deriveTheoryDependency
        autopoiesisAnalogyAdapter .interpretiveCitation .ready =
      TheoryDependencyResult.interpretiveOnly
  analogyRefused :
    deriveTheoryDependency
        autopoiesisAnalogyAdapter .proofDependency .ready =
      TheoryDependencyResult.refuse
        .theoryAnalogyPresentedAsProof
  missingBridgeRefused :
    deriveTheoryDependency missingBridgeAdapter .proofDependency .ready =
      TheoryDependencyResult.refuse
        .theoremTransferAdapterMissing
  unmetAssumptionRefused :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .incomplete =
      TheoryDependencyResult.refuse
        .borrowedTheoremAssumptionsUnmet
  missingLocalConfluenceRefused :
    deriveTheoryDependency
        newmanWithoutLocalConfluence .proofDependency .ready =
      TheoryDependencyResult.refuse
        .newmanWithoutLocalConfluence
  coalgebraNormalFormRefused :
    deriveTheoryDependency
        coalgebraAsNormalForm .proofDependency .ready =
      TheoryDependencyResult.refuse
        .coalgebraFinalityMisusedAsNormalForm

def certificate : Certificate where
  gradeATransfer := gradeATransfer
  gradeBReproof := gradeBReproof
  gradeCNonAuthoritative := gradeCNonAuthoritative
  analogyRefused := analogyRefused
  missingBridgeRefused := missingBridgeRefused
  unmetAssumptionRefused := unmetAssumptionRefused
  missingLocalConfluenceRefused := missingLocalConfluenceRefused
  coalgebraNormalFormRefused := coalgebraNormalFormRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC65Target

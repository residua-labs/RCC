import RCCTests.TheoryAdapter

/-! RCC-76 candidate: theory-import firewall and theorem-scope refusals. -/

namespace Residua.RCC.RCC76Target

open Residua.RCC.TheoryAdapter
open Residua.RCC.TheoryAdapter.Tests

def lawfulTransfer := lawful_grade_A_transfer_imports_theorem
def gradeARequired := imported_result_requires_grade_A
def groundedTemplate := grade_B_uses_only_RCC_native_reproof
def interpretiveOnly := interpretive_lineage_remains_non_authoritative
def analogyRefused := analogy_as_proof_is_refused
def missingBridgeRefused := missing_bridge_is_refused
def assumptionsRefused := unmet_borrowed_assumptions_are_refused
def newmanScopeRefused := newman_without_local_confluence_is_refused
def coalgebraScopeRefused := coalgebra_finality_cannot_prove_normal_form

structure Certificate where
  lawfulTransfer :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .ready =
      TheoryDependencyResult.imported .scheduleIndependent
  groundedTemplate :
    deriveTheoryDependency
        groundednessTemplateAdapter .proofDependency .ready =
      TheoryDependencyResult.locallyProved .nativeGroundedness
  interpretiveOnly :
    deriveTheoryDependency
        autopoiesisAnalogyAdapter .interpretiveCitation .ready =
      TheoryDependencyResult.interpretiveOnly
  missingBridgeRefused :
    deriveTheoryDependency missingBridgeAdapter .proofDependency .ready =
      TheoryDependencyResult.refuse .theoremTransferAdapterMissing
  assumptionsRefused :
    deriveTheoryDependency
        lawfulNewmanAdapter .proofDependency .incomplete =
      TheoryDependencyResult.refuse .borrowedTheoremAssumptionsUnmet
  newmanScopeRefused :
    deriveTheoryDependency
        newmanWithoutLocalConfluence .proofDependency .ready =
      TheoryDependencyResult.refuse .newmanWithoutLocalConfluence
  coalgebraScopeRefused :
    deriveTheoryDependency
        coalgebraAsNormalForm .proofDependency .ready =
      TheoryDependencyResult.refuse .coalgebraFinalityMisusedAsNormalForm

def certificate : Certificate where
  lawfulTransfer := lawfulTransfer
  groundedTemplate := groundedTemplate
  interpretiveOnly := interpretiveOnly
  missingBridgeRefused := missingBridgeRefused
  assumptionsRefused := assumptionsRefused
  newmanScopeRefused := newmanScopeRefused
  coalgebraScopeRefused := coalgebraScopeRefused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC76Target

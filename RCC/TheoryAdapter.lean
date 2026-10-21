import Init

/-!
# RCC TA-1 theory-import firewall

Similarity to a mature theory is not a proof.  Every theory collision is
sealed into exactly one grade:

* Grade A transfers a theorem through explicit object, assumption, and theorem
  bridges;
* Grade B reuses only a proof template and therefore requires an RCC-native
  proof; and
* Grade C is interpretive lineage and cannot enter proof dependencies.

The common derivation below consumes proof objects rather than citation
labels.  It also names the two load-bearing scope errors called out by the RCC
ADR: Newman without local confluence, and coalgebraic finality used as a
canonical-normal-form theorem.

Prelude-only Lean 4.14; no Mathlib or proof placeholders.
-/

namespace Residua.RCC.TheoryAdapter

universe u

/-- The exhaustive and non-overlapping theory-collision grades. -/
inductive TheoryAdapterGrade
  | theoremTransfer
  | proofTemplate
  | interpretiveAnalogy
  deriving DecidableEq, Repr

/-- The borrowed theorem family whose scope must be preserved. -/
inductive BorrowedTheoremFamily
  | generic
  | newmanConfluence
  | coalgebraFinality
  deriving DecidableEq, Repr

/-- The RCC role for which the source theorem is proposed. -/
inductive RCCTheoremRole
  | generic
  | internalAdvancedConfluence
  | canonicalNormalForm
  | outerLineageBisimulation
  deriving DecidableEq, Repr

/-- Whether the caller asks for a proof dependency or only a citation. -/
inductive TheoryUse
  | proofDependency
  | interpretiveCitation
  deriving DecidableEq, Repr

/-- Stable names for the source and RCC sides of one adapter. -/
structure TheoryAdapterCoordinates where
  facetQ : String
  sourceTheoryQ : String
  sourceObjectsQ : String
  rccObjectsQ : String
  mismatchResidue : String
  deriving DecidableEq, Repr

/-- Named refusal paths of the fixed theory-import decision tree. -/
inductive TheoryAdapterResidue
  | theoryAnalogyPresentedAsProof
  | theoremTransferAdapterMissing
  | borrowedTheoremAssumptionsUnmet
  | proofTemplateNotReprovedInRCC
  | newmanWithoutTermination
  | newmanWithoutLocalConfluence
  | newmanScopeOverstated
  | coalgebraFinalityMisusedAsNormalForm
  | coalgebraScopeOverstated
  deriving DecidableEq, Repr

/--
Raw evidence coordinates for one theory collision.

The grade is data, but it cannot discharge anything by itself.  Grade A needs
all four executable/proof bridges; Grade B needs `rccReproof`; Grade C carries
only an explanatory note.
-/
structure TheoryCollisionAdapter
    (SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u) where
  coordinates : TheoryAdapterCoordinates
  grade : TheoryAdapterGrade
  family : BorrowedTheoremFamily
  targetRole : RCCTheoremRole

  objectTranslationQ : Option String
  objectTranslation : Option (SourceObject → RCCObject)

  assumptionTranslationQ : Option String
  assumptionTranslation :
    Option (RCCAssumptions → Option SourceAssumptions)

  borrowedTheoremQ : Option String
  borrowedTheorem :
    Option (SourceAssumptions → SourceTheorem)

  bridgeTheoremQ : Option String
  theoremBridge : Option (SourceTheorem → RCCTheorem)

  rccReproofQ : Option String
  rccReproof : Option (RCCAssumptions → RCCTheorem)

  terminationEvidence : Option TerminationCertificate
  localConfluenceEvidence : Option LocalConfluenceCertificate
  interpretation : Option String

/--
Successful proof dependencies record whether the theorem was transferred or
proved on RCC objects.  Interpretive lineage has no theorem payload.
-/
inductive TheoryDependencyResult
    (RCCTheorem : Type u)
  | imported (proof : RCCTheorem)
  | locallyProved (proof : RCCTheorem)
  | interpretiveOnly
  | refuse (residue : TheoryAdapterResidue)

/-- Scope checks that must precede consumption of a Grade-A bridge. -/
def assessTransferScope
    {SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u}
    (adapter :
      TheoryCollisionAdapter
        SourceObject RCCObject SourceAssumptions RCCAssumptions
        SourceTheorem RCCTheorem TerminationCertificate
        LocalConfluenceCertificate) :
    Option TheoryAdapterResidue :=
  match adapter.family, adapter.targetRole with
  | .newmanConfluence, .internalAdvancedConfluence =>
      match adapter.terminationEvidence with
      | none => some .newmanWithoutTermination
      | some _ =>
          match adapter.localConfluenceEvidence with
          | none => some .newmanWithoutLocalConfluence
          | some _ => none
  | .newmanConfluence, _ =>
      some .newmanScopeOverstated
  | .coalgebraFinality, .canonicalNormalForm =>
      some .coalgebraFinalityMisusedAsNormalForm
  | .coalgebraFinality, .outerLineageBisimulation =>
      none
  | .coalgebraFinality, _ =>
      some .coalgebraScopeOverstated
  | .generic, _ =>
      none

/--
Grade-A theorem transfer.

Names alone are insufficient: the source/RCC object translation, assumption
translation, borrowed theorem, and bridge theorem must each have both a sealed
identifier and an actual inhabitant.
-/
def deriveTransferredTheorem
    {SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u}
    (adapter :
      TheoryCollisionAdapter
        SourceObject RCCObject SourceAssumptions RCCAssumptions
        SourceTheorem RCCTheorem TerminationCertificate
        LocalConfluenceCertificate)
    (assumptions : RCCAssumptions) :
    TheoryDependencyResult RCCTheorem :=
  match assessTransferScope adapter with
  | some residue => .refuse residue
  | none =>
      match
          adapter.objectTranslationQ,
          adapter.objectTranslation,
          adapter.assumptionTranslationQ,
          adapter.assumptionTranslation,
          adapter.borrowedTheoremQ,
          adapter.borrowedTheorem,
          adapter.bridgeTheoremQ,
          adapter.theoremBridge with
      | some _, some _, some _, some translateAssumptions,
          some _, some borrowed, some _, some bridge =>
          match translateAssumptions assumptions with
          | none =>
              .refuse .borrowedTheoremAssumptionsUnmet
          | some sourceAssumptions =>
              .imported (bridge (borrowed sourceAssumptions))
      | _, _, _, _, _, _, _, _ =>
          .refuse .theoremTransferAdapterMissing

/--
The only public decision tree.

An interpretive citation never yields a theorem.  A Grade-B proof dependency
comes only from `rccReproof`, never from the borrowed theorem fields.
-/
def deriveTheoryDependency
    {SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u}
    (adapter :
      TheoryCollisionAdapter
        SourceObject RCCObject SourceAssumptions RCCAssumptions
        SourceTheorem RCCTheorem TerminationCertificate
        LocalConfluenceCertificate)
    (use : TheoryUse)
    (assumptions : RCCAssumptions) :
    TheoryDependencyResult RCCTheorem :=
  match use with
  | .interpretiveCitation =>
      .interpretiveOnly
  | .proofDependency =>
      match adapter.grade with
      | .theoremTransfer =>
          deriveTransferredTheorem adapter assumptions
      | .proofTemplate =>
          match adapter.rccReproofQ, adapter.rccReproof with
          | some _, some reprove =>
              .locallyProved (reprove assumptions)
          | _, _ =>
              .refuse .proofTemplateNotReprovedInRCC
      | .interpretiveAnalogy =>
          .refuse .theoryAnalogyPresentedAsProof

/-- Erase proof payloads while retaining their authority provenance. -/
inductive TheoryDependencyTag
  | imported
  | locallyProved
  | interpretiveOnly
  | refused
  deriving DecidableEq, Repr

def TheoryDependencyResult.tag :
    TheoryDependencyResult RCCTheorem → TheoryDependencyTag
  | .imported _ => .imported
  | .locallyProved _ => .locallyProved
  | .interpretiveOnly => .interpretiveOnly
  | .refuse _ => .refused

/-- An imported proof can be derived only from a sealed Grade-A adapter. -/
theorem imported_dependency_requires_grade_A
    {SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u}
    (adapter :
      TheoryCollisionAdapter
        SourceObject RCCObject SourceAssumptions RCCAssumptions
        SourceTheorem RCCTheorem TerminationCertificate
        LocalConfluenceCertificate)
    (assumptions : RCCAssumptions)
    (imported :
      (deriveTheoryDependency
        adapter .proofDependency assumptions).tag =
          TheoryDependencyTag.imported) :
    adapter.grade = TheoryAdapterGrade.theoremTransfer := by
  cases grade : adapter.grade with
  | theoremTransfer =>
      rfl
  | proofTemplate =>
      cases reproofQ : adapter.rccReproofQ <;>
        cases reproof : adapter.rccReproof <;>
        simp [deriveTheoryDependency, grade, reproofQ, reproof,
          TheoryDependencyResult.tag] at imported
  | interpretiveAnalogy =>
      simp [deriveTheoryDependency, grade,
        TheoryDependencyResult.tag] at imported

/-- Grade C can be cited, but can never inhabit a proof dependency. -/
theorem interpretive_analogy_never_enters_proof_dependencies
    {SourceObject RCCObject SourceAssumptions RCCAssumptions
      SourceTheorem RCCTheorem TerminationCertificate
      LocalConfluenceCertificate : Type u}
    (adapter :
      TheoryCollisionAdapter
        SourceObject RCCObject SourceAssumptions RCCAssumptions
        SourceTheorem RCCTheorem TerminationCertificate
        LocalConfluenceCertificate)
    (grade :
      adapter.grade = TheoryAdapterGrade.interpretiveAnalogy)
    (assumptions : RCCAssumptions) :
    deriveTheoryDependency adapter .proofDependency assumptions =
      TheoryDependencyResult.refuse
        TheoryAdapterResidue.theoryAnalogyPresentedAsProof := by
  simp [deriveTheoryDependency, grade]

end Residua.RCC.TheoryAdapter

import RCC.SeamWriterAdapter
import RCCTests.SeamExactness

namespace Residua.RCC.SeamWriterAdapter.Tests

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.SeamExactness
open Residua.RCC.SeamWriterAdapter

abbrev World := SeamExactness.Tests.Identity.world
abbrev Owner := SeamExactness.Tests.Identity.Owner

def writerSpec :
    FencedWriterSpec World.EffectSlot World.HistoryHead where
  slotParent := fun _ => World.sourceHead

def judgmentEquivalence : JudgmentEquivalence Bool where
  Equivalent := Eq
  refl := fun _judgment => rfl
  symm := Eq.symm
  trans := Eq.trans
  decide := fun first second =>
    inferInstanceAs (Decidable (first = second))

def linearizer :
    AdmissionLinearizer
      World.EffectSlot
      World.HistoryHead
      Bool
      World.EffectOwner
      Unit
      writerSpec
      judgmentEquivalence where
  Precedes := fun _ _ => True
  precedesRefl := fun _version => trivial
  precedesTrans := fun _first _second => trivial
  comparable := fun _first _second => Or.inl trivial
  activeGeneration := fun _ _ => .writer
  canonicalDecision := fun _ _ _ => none
  decisionPreserved := by
    intro first second head slot judgment precedes decided
    cases decided

def sourceState :
    FencedWriterState
      World.EffectSlot
      World.HistoryHead
      Bool
      World.EffectOwner where
  generation := .writer
  canonicalHead := World.sourceHead
  decisions := fun _ => none

def targetState :
    FencedWriterState
      World.EffectSlot
      World.HistoryHead
      Bool
      World.EffectOwner where
  generation := .writer
  canonicalHead := World.targetHead
  decisions := fun _ => none

def sourceSnapshot :
    CanonicalWriterSnapshot linearizer () sourceState where
  generationBound := rfl
  decisionBound := fun _slot => rfl

def targetSnapshot :
    CanonicalWriterSnapshot linearizer () targetState where
  generationBound := rfl
  decisionBound := fun _slot => rfl

def writerSeam :
    CanonicalWriterSeamAt
      World linearizer () sourceState targetState where
  boundary :=
    SeamExactness.Tests.Identity.exactSeam.toSeamBoundaryExactAt
  sourceSnapshot := sourceSnapshot
  targetSnapshot := targetSnapshot
  sourceHeadBound := rfl
  targetHeadBound := rfl
  sourceAuthorityBound := by
    intro _slot owner authority
    exact authority.symm
  targetAuthorityBound := by
    intro _slot owner authority
    exact authority.symm

theorem canonical_writer_generations_agree :
    sourceState.generation = targetState.generation :=
  writerSeam.generationAgreement

theorem canonical_writer_derives_full_seam_exactness :
    ExactSeamAt World :=
  writerSeam.toExactSeam

inductive RogueOwner
  | canonical
  | rogue
  deriving DecidableEq, Repr

def rogueLinearizer :
    AdmissionLinearizer
      Unit Nat Bool RogueOwner Unit
      { slotParent := fun _ => 13 }
      judgmentEquivalence where
  Precedes := fun _ _ => True
  precedesRefl := fun version => trivial
  precedesTrans := fun first second => trivial
  comparable := fun first second => Or.inl trivial
  activeGeneration := fun _ _ => .canonical
  canonicalDecision := fun _ _ _ => none
  decisionPreserved := by
    intro first second head slot judgment precedes decided
    cases decided

def rogueState :
    FencedWriterState Unit Nat Bool RogueOwner where
  generation := .rogue
  canonicalHead := 13
  decisions := fun _ => none

/-- A receiver with a rogue generation cannot claim canonical writer status. -/
theorem rogue_generation_cannot_form_canonical_snapshot :
    ¬ CanonicalWriterSnapshot rogueLinearizer () rogueState := by
  intro snapshot
  cases snapshot.generationBound

end Residua.RCC.SeamWriterAdapter.Tests

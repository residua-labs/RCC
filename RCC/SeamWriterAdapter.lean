import RCC.AdmissionLinearizer
import RCC.SeamExactness

/-!
# C2 seam fenced-writer adapter

An abstract statement that both endpoints name the same owner does not prove
that they are projections of one canonical decision-writer surface.  This
adapter derives seam effect-owner coherence from two concrete
`CanonicalWriterSnapshot`s of one `AdmissionLinearizer` version.

The component endpoints must bind every local write authority to the active
generation of their respective writer snapshot.  Equal seam history heads
then let the existing no-generation-overlap theorem identify both
generations.

This module does not prove runtime process measurement or enumerate every
effect slot.  It closes the single-writer realization only for the supplied
canonical writer surface.
-/

namespace Residua.RCC.SeamWriterAdapter

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.SeamExactness

universe u

/--
One seam boundary realized by two snapshots of the same canonical writer.

The writer generation is the seam's effect-owner carrier.  Authority evidence
is therefore bound to the active fenced generation rather than a display
name.
-/
structure CanonicalWriterSeamAt
    (world : SeamWorld)
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    (linearizer :
      AdmissionLinearizer
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner
        Version
        writerSpec
        equivalence)
    (version : Version)
    (sourceState targetState :
      FencedWriterState
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner) : Prop where
  boundary : SeamBoundaryExactAt world
  sourceSnapshot :
    CanonicalWriterSnapshot linearizer version sourceState
  targetSnapshot :
    CanonicalWriterSnapshot linearizer version targetState
  sourceHeadBound :
    sourceState.canonicalHead = world.sourceHead
  targetHeadBound :
    targetState.canonicalHead = world.targetHead
  sourceAuthorityBound :
    ∀ {slot owner},
      world.sourceMayWrite slot owner →
      sourceState.generation = owner
  targetAuthorityBound :
    ∀ {slot owner},
      world.targetMayWrite slot owner →
      targetState.generation = owner

/--
The two endpoint writer states have the same active generation because they
are canonical projections at one version and one seam-bound history head.
-/
theorem CanonicalWriterSeamAt.generationAgreement
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      AdmissionLinearizer
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner
        Version
        writerSpec
        equivalence}
    {version : Version}
    {sourceState targetState :
      FencedWriterState
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner}
    (writer : CanonicalWriterSeamAt
      world linearizer version sourceState targetState) :
    sourceState.generation = targetState.generation := by
  apply canonical_snapshots_no_generation_overlap
    writer.sourceSnapshot writer.targetSnapshot
  calc
    sourceState.canonicalHead = world.sourceHead :=
      writer.sourceHeadBound
    _ = world.targetHead :=
      writer.boundary.historyHeadAgreement
    _ = targetState.canonicalHead :=
      writer.targetHeadBound.symm

/--
The concrete canonical writer discharges the final effect-owner law and
upgrades boundary exactness to full seam exactness.
-/
def CanonicalWriterSeamAt.toExactSeam
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      AdmissionLinearizer
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner
        Version
        writerSpec
        equivalence}
    {version : Version}
    {sourceState targetState :
      FencedWriterState
        world.EffectSlot
        world.HistoryHead
        Judgment
        world.EffectOwner}
    (writer : CanonicalWriterSeamAt
      world linearizer version sourceState targetState) :
    ExactSeamAt world where
  toSeamBoundaryExactAt := writer.boundary
  effectOwnerCoherent := by
    intro slot sourceOwner targetOwner sourceAuthority targetAuthority
    calc
      sourceOwner = sourceState.generation :=
        (writer.sourceAuthorityBound sourceAuthority).symm
      _ = targetState.generation :=
        writer.generationAgreement
      _ = targetOwner :=
        writer.targetAuthorityBound targetAuthority

end Residua.RCC.SeamWriterAdapter

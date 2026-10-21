import RCC.SeamAssumptionAdapter
import RCC.SeamComponentAdapter
import RCC.SeamWriterAdapter

/-!
# C2 integrated seam adapter

The component, assumption, and canonical-writer adapters must describe one
and the same `SeamWorld`.  Proving those facets independently for unrelated
worlds would not establish an exact component boundary.

This adapter takes the canonical writer realization as the source of full
seam exactness, then combines it with component transition/closure laws and
assumption activity/dependency laws over that same world.  It mechanically
constructs the existing component and assumption certificates.

The structure remains local to one supplied seam.  It does not enumerate the
production seam universe, prove runtime process measurement, or establish
global intent coverage.
-/

namespace Residua.RCC.SeamIntegratedAdapter

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.SeamAssumptionAdapter
open Residua.RCC.SeamComponentAdapter
open Residua.RCC.SeamExactness
open Residua.RCC.SeamWriterAdapter

universe u

/--
One seam certificate whose component, assumption, and writer facets share
the same `SeamWorld`.

Full `ExactSeamAt` evidence is deliberately derived from `writer`; callers
cannot provide a second unrelated exactness witness for the other facets.
-/
structure IntegratedSeamCertificateAt
    (world : SeamWorld)
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    (linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
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
        world.EffectOwner)
    (component : ComponentRelationBinding world)
    (assumptions : AssumptionSeamBinding world) : Prop where
  writer :
    CanonicalWriterSeamAt
      world linearizer version sourceState targetState
  stepPreserved :
    ∀ {source target},
      component.sourceStep source target →
      component.targetStep
        (world.encode source)
        (world.encode target)
  closedPreserved :
    ∀ {source},
      component.sourceClosed source →
      component.targetClosed (world.encode source)
  activeExact :
    ∀ assumption,
      assumptions.sourceActive
          world.sourceAssumptionRoot assumption ↔
        assumptions.targetActive
          world.targetAssumptionRoot assumption
  dependenciesExact :
    ∀ source assumption,
      assumption ∈ assumptions.sourceDependencies source ↔
        assumption ∈
          assumptions.targetDependencies (world.encode source)

/-- The canonical writer facet supplies the unique local seam exactness. -/
def IntegratedSeamCertificateAt.toExactSeam
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
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
    {component : ComponentRelationBinding world}
    {assumptions : AssumptionSeamBinding world}
    (integrated :
      IntegratedSeamCertificateAt
        world linearizer version sourceState targetState
        component assumptions) :
    ExactSeamAt world :=
  integrated.writer.toExactSeam

/-- The integrated certificate constructs the component-level seam. -/
def IntegratedSeamCertificateAt.toComponentSeam
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
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
    {component : ComponentRelationBinding world}
    {assumptions : AssumptionSeamBinding world}
    (integrated :
      IntegratedSeamCertificateAt
        world linearizer version sourceState targetState
        component assumptions) :
    ExactComponentSeamAt world component where
  exact := integrated.toExactSeam
  stepPreserved := integrated.stepPreserved
  closedPreserved := integrated.closedPreserved

/-- The integrated certificate constructs the assumption-level seam. -/
def IntegratedSeamCertificateAt.toAssumptionSeam
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
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
    {component : ComponentRelationBinding world}
    {assumptions : AssumptionSeamBinding world}
    (integrated :
      IntegratedSeamCertificateAt
        world linearizer version sourceState targetState
        component assumptions) :
    ExactAssumptionSeamAt world assumptions where
  exact := integrated.toExactSeam
  activeExact := integrated.activeExact
  dependenciesExact := integrated.dependenciesExact

/-- The existing formal component seam is a derived projection. -/
def IntegratedSeamCertificateAt.toFormalSeam
    {world : SeamWorld}
    {Judgment Version : Type u}
    {writerSpec :
      FencedWriterSpec world.EffectSlot world.HistoryHead}
    {equivalence : JudgmentEquivalence Judgment}
    {linearizer :
      Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
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
    {component : ComponentRelationBinding world}
    {assumptions : AssumptionSeamBinding world}
    (integrated :
      IntegratedSeamCertificateAt
        world linearizer version sourceState targetState
        component assumptions) :
    Residua.RCC.Seam component.sourceRel component.targetRel :=
  integrated.toComponentSeam.toFormalSeam

end Residua.RCC.SeamIntegratedAdapter

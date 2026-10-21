import RCC.SeamFamily
import RCC.SeamIntegratedAdapter

/-!
# C2 sealed integrated seam family

The local integrated adapter establishes that one component boundary shares
one semantic world, one canonical writer realization, one component
relation, and one assumption interpretation.  C2 additionally needs every
declared in-scope seam to carry such a realization.

This module packages the dependent realization data for each seam, seals the
declared seam enumeration, and mechanically derives the existing
`ExactSeamFamily`.  It does not prove that the instance-supplied `InScope`
predicate is the complete production component graph; that remains a
separate scope-adequacy obligation.
-/

namespace Residua.RCC.SeamIntegratedFamily

open Residua.RCC.AdmissionLinearizer
open Residua.RCC.SeamAssumptionAdapter
open Residua.RCC.SeamComponentAdapter
open Residua.RCC.SeamExactness
open Residua.RCC.SeamFamily
open Residua.RCC.SeamIntegratedAdapter

universe u

/--
All dependent realization data for one integrated seam.

Every field is indexed by the same `world`; a family cannot combine local
certificates belonging to detached seam worlds.
-/
structure IntegratedSeamRealization (world : SeamWorld.{u}) where
  Judgment : Type u
  Version : Type u
  writerSpec :
    FencedWriterSpec world.EffectSlot world.HistoryHead
  equivalence : JudgmentEquivalence Judgment
  linearizer :
    Residua.RCC.AdmissionLinearizer.AdmissionLinearizer
      world.EffectSlot
      world.HistoryHead
      Judgment
      world.EffectOwner
      Version
      writerSpec
      equivalence
  version : Version
  sourceState :
    FencedWriterState
      world.EffectSlot
      world.HistoryHead
      Judgment
      world.EffectOwner
  targetState :
    FencedWriterState
      world.EffectSlot
      world.HistoryHead
      Judgment
      world.EffectOwner
  component : ComponentRelationBinding world
  assumptions : AssumptionSeamBinding.{u, u} world
  certificate :
    IntegratedSeamCertificateAt.{u, u, u}
      world
      linearizer
      version
      sourceState
      targetState
      component
      assumptions

/-- The full local exactness derived from one integrated realization. -/
def IntegratedSeamRealization.toExactSeam
    {world : SeamWorld}
    (realization : IntegratedSeamRealization world) :
    ExactSeamAt world :=
  realization.certificate.toExactSeam

/--
A closed declared seam universe in which every listed boundary has one
integrated realization.
-/
structure SealedIntegratedSeamFamily (scope : SeamScope) where
  sealed : SealedSeamUniverse scope
  realization :
    ∀ seam,
      seam ∈ scope.enumeration →
      IntegratedSeamRealization (scope.world seam)

/-- Forget realization detail and recover the existing exact seam family. -/
def SealedIntegratedSeamFamily.toExactFamily
    {scope : SeamScope}
    (family : SealedIntegratedSeamFamily scope) :
    ExactSeamFamily scope where
  sealed := family.sealed
  exact := by
    intro seam listed
    exact (family.realization seam listed).toExactSeam

/-- Every declared in-scope seam has writer-derived local exactness. -/
theorem SealedIntegratedSeamFamily.inScopeExact
    {scope : SeamScope}
    (family : SealedIntegratedSeamFamily scope)
    (seam : scope.Seam)
    (inScope : scope.InScope seam) :
    ExactSeamAt (scope.world seam) :=
  family.toExactFamily.inScopeExact seam inScope

end Residua.RCC.SeamIntegratedFamily

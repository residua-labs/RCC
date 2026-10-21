import RCCTests.SeamFamily
import RCCTests.SeamIntegratedAdapter
import RCC.SeamIntegratedFamily

namespace Residua.RCC.SeamIntegratedFamily.Tests

open Residua.RCC.SeamFamily
open Residua.RCC.SeamIntegratedFamily

namespace Positive

abbrev Scope := SeamFamily.Tests.Positive.scope

def realization :
    IntegratedSeamRealization
      (Scope.world SeamFamily.Tests.Positive.Seam.identity) where
  Judgment := Bool
  Version := Unit
  writerSpec := SeamWriterAdapter.Tests.writerSpec
  equivalence := SeamWriterAdapter.Tests.judgmentEquivalence
  linearizer := SeamWriterAdapter.Tests.linearizer
  version := ()
  sourceState := SeamWriterAdapter.Tests.sourceState
  targetState := SeamWriterAdapter.Tests.targetState
  component := SeamComponentAdapter.Tests.Positive.binding
  assumptions := SeamAssumptionAdapter.Tests.Positive.binding
  certificate := SeamIntegratedAdapter.Tests.Positive.integrated

def family : SealedIntegratedSeamFamily Scope where
  sealed := SeamFamily.Tests.Positive.family.sealed
  realization := by
    intro seam listed
    cases seam
    exact realization

end Positive

theorem sealed_integrated_family_derives_exact_family :
    ExactSeamFamily Positive.Scope :=
  Positive.family.toExactFamily

theorem sealed_integrated_family_closes_declared_identity_seam :
    Residua.RCC.SeamExactness.ExactSeamAt
      (Positive.Scope.world SeamFamily.Tests.Positive.Seam.identity) :=
  Positive.family.inScopeExact .identity rfl

/-- Empty enumeration cannot hide a nonempty integrated seam universe. -/
theorem empty_enumeration_blocks_integrated_family :
    SealedIntegratedSeamFamily
        SeamFamily.Tests.EmptyEnumeration.scope →
      False := by
  intro family
  exact
    SeamFamily.Tests.empty_enumeration_cannot_hide_in_scope_seam
      family.sealed

/-- A listed dual-owner seam has no integrated family realization. -/
theorem dual_owner_seam_blocks_integrated_family :
    SealedIntegratedSeamFamily
        SeamFamily.Tests.BadSeam.scope →
      False := by
  intro family
  exact
    SeamFamily.Tests.dual_owner_seam_prevents_exact_family
      family.toExactFamily

end Residua.RCC.SeamIntegratedFamily.Tests

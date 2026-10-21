import RCC.SeamExactness

/-!
# C2 sealed seam family

One exact seam does not establish that every in-scope component boundary is
exact.  C2 therefore seals the seam universe before consuming local
certificates.

The scope supplies only an enumeration and membership predicate.  A separate
coverage proof establishes that the enumeration is sound and complete, and
an exact family supplies an `ExactSeamAt` certificate for every listed seam.
Empty-list absence is never interpreted as seam completeness by itself.

This family layer does not synthesize local seam certificates.  Production
instances must obtain them through the component, assumption, address, and
writer realization adapters.  It also does not prove that the chosen
`InScope` predicate is sufficient for a global intent; that is a separate
composition-coverage theorem.
-/

namespace Residua.RCC.SeamFamily

open Residua.RCC.SeamExactness

universe u

/-- The raw declared universe of component seams. -/
structure SeamScope where
  Seam : Type u
  world : Seam → SeamWorld
  InScope : Seam → Prop
  enumeration : List Seam

/-- Closed-world coverage for the declared seam enumeration. -/
structure SealedSeamUniverse (scope : SeamScope) : Prop where
  sound :
    ∀ seam,
      seam ∈ scope.enumeration →
      scope.InScope seam
  complete :
    ∀ seam,
      scope.InScope seam →
      seam ∈ scope.enumeration

/-- Every seam in one sealed enumeration carries local exactness evidence. -/
structure ExactSeamFamily (scope : SeamScope) : Prop where
  sealed : SealedSeamUniverse scope
  exact :
    ∀ seam,
      seam ∈ scope.enumeration →
      ExactSeamAt (scope.world seam)

/-- C2 family headline: every in-scope seam has an exact local certificate. -/
theorem ExactSeamFamily.inScopeExact
    {scope : SeamScope}
    (family : ExactSeamFamily scope)
    (seam : scope.Seam)
    (inScope : scope.InScope seam) :
    ExactSeamAt (scope.world seam) :=
  family.exact seam (family.sealed.complete seam inScope)

/-- The declared seam enumeration contains only in-scope boundaries. -/
theorem ExactSeamFamily.listedInScope
    {scope : SeamScope}
    (family : ExactSeamFamily scope)
    (seam : scope.Seam)
    (listed : seam ∈ scope.enumeration) :
    scope.InScope seam :=
  family.sealed.sound seam listed

end Residua.RCC.SeamFamily

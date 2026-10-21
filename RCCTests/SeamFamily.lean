import RCC.SeamFamily
import RCCTests.SeamExactness

namespace Residua.RCC.SeamFamily.Tests

open Residua.RCC.SeamExactness
open Residua.RCC.SeamFamily

namespace Positive

inductive Seam
  | identity
  deriving DecidableEq, Repr

def scope : SeamScope where
  Seam := Seam
  world := fun _ => SeamExactness.Tests.Identity.world
  InScope := fun seam => seam = .identity
  enumeration := [.identity]

def family : ExactSeamFamily scope where
  sealed :=
    { sound := by
        intro seam listed
        cases seam
        rfl
      complete := by
        intro seam inScope
        cases seam
        exact List.Mem.head [] }
  exact := by
    intro seam listed
    cases seam
    exact SeamExactness.Tests.Identity.exactSeam

end Positive

theorem listed_identity_seam_is_exact :
    ExactSeamAt
      (Positive.scope.world Positive.Seam.identity) :=
  Positive.family.inScopeExact .identity rfl

namespace EmptyEnumeration

def scope : SeamScope where
  Seam := Unit
  world := fun _ => SeamExactness.Tests.Identity.world
  InScope := fun _ => True
  enumeration := []

end EmptyEnumeration

/-- An empty list cannot seal a nonempty seam universe. -/
theorem empty_enumeration_cannot_hide_in_scope_seam :
    ¬ SealedSeamUniverse EmptyEnumeration.scope := by
  intro sealed
  have listed :=
    sealed.complete () trivial
  cases listed

namespace BadSeam

def scope : SeamScope where
  Seam := Unit
  world := fun _ => SeamExactness.Tests.DualOwner.world
  InScope := fun _ => True
  enumeration := [()]

end BadSeam

/-- A covered but locally inexact seam prevents family exactness. -/
theorem dual_owner_seam_prevents_exact_family :
    ¬ ExactSeamFamily BadSeam.scope := by
  intro family
  have exact :=
    family.exact () (List.Mem.head [])
  exact
    SeamExactness.Tests.dual_effect_owner_is_refused exact

end Residua.RCC.SeamFamily.Tests

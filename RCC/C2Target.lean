import RCCTests.SeamExactness

/-! C2 candidate: a seam is exact only when quotient, typed address, snapshot,
    assumption, and effect-owner boundary laws all agree. -/

namespace Residua.RCC.C2Target

open Residua.RCC.SeamExactness
open Residua.RCC.SeamExactness.Tests

structure Certificate where
  identityExact :
    ∀ left right : Bool,
      Identity.world.targetEquivalent
          (Identity.world.encode left) (Identity.world.encode right) ↔
        Identity.world.sourceEquivalent left right
  collapsedQuotientRejected :
    ¬ ExactSeamAt Collapse.world
  kindMismatchRejected :
    ¬ ExactSeamAt KindMismatch.world
  assumptionRootMismatchRejected :
    ¬ ExactSeamAt RootMismatch.world
  dualEffectOwnerRejected :
    ¬ ExactSeamAt DualOwner.world

def certificate : Certificate where
  identityExact := identity_seam_is_semantically_exact
  collapsedQuotientRejected := collapsing_target_quotient_is_refused
  kindMismatchRejected := address_kind_mismatch_is_refused
  assumptionRootMismatchRejected := assumption_root_mismatch_is_refused
  dualEffectOwnerRejected := dual_effect_owner_is_refused

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.C2Target

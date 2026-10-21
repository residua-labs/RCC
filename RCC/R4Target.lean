import RCCTests.AssumptionRelativeSoundness

/-! RCC-R4 candidate: an accepted Goal certificate becomes a semantic
    judgment only when its assumption root and every declared dependency are
    active on the same sealed snapshot.

    *Sufficiency* is carried by the five positive fields on
    `currentBinding.sound`: an accepted certificate whose root and every
    declared dependency are active at the current snapshot yields the
    assumption-relative judgment.

    *Necessity* is carried by the refusal field `mutants`.  A stale-rooted
    certificate (`staleAccepted`) and a certificate naming an inactive
    dependency (`inactiveDependencyAccepted`) cannot obtain an
    `AssumptionRelativeJudgmentAt` at the current snapshot — even though R2
    alone accepts their raw Goal claim (`r2_alone_accepts_stale_root`).  Any
    such judgment would project to a binding, contradicting the binding
    refusals `stale_root_cannot_bind` and
    `inactive_listed_dependency_cannot_bind`. -/

namespace Residua.RCC.R4Target

open Residua.RCC.AssumptionRelativeSoundness
open Residua.RCC.AssumptionRelativeSoundness.Tests

/-- A stale-rooted certificate cannot become a relative judgment: any such
    judgment would project (via its three binding fields) to a binding,
    contradicting `stale_root_cannot_bind`. -/
theorem staleRootJudgmentRefused :
    ¬ AssumptionRelativeJudgmentAt kernel snapshot carrier staleAccepted := by
  intro judgment
  exact
    stale_root_cannot_bind
      ⟨judgment.certificateRootBound,
        judgment.rootActive,
        judgment.dependenciesActive⟩

/-- A certificate naming an inactive dependency cannot become a relative
    judgment: any such judgment would project (via its three binding fields)
    to a binding, contradicting `inactive_listed_dependency_cannot_bind`. -/
theorem inactiveDependencyJudgmentRefused :
    ¬ AssumptionRelativeJudgmentAt
        inactiveDependencyKernel snapshot carrier inactiveDependencyAccepted := by
  intro judgment
  exact
    inactive_listed_dependency_cannot_bind
      ⟨judgment.certificateRootBound,
        judgment.rootActive,
        judgment.dependenciesActive⟩

/-- The necessity half of R4: an inactive root or an inactive declared
    dependency blocks the assumption-relative judgment. -/
structure MutantRefusal : Prop where
  staleRootRefused :
    ¬ AssumptionRelativeJudgmentAt kernel snapshot carrier staleAccepted
  inactiveDependencyRefused :
    ¬ AssumptionRelativeJudgmentAt
        inactiveDependencyKernel snapshot carrier inactiveDependencyAccepted

structure Certificate where
  currentJudgment :
    AssumptionRelativeJudgmentAt
      kernel snapshot carrier currentAccepted
  rootBound :
    kernel.certificateRoot currentAccepted.certificate =
      snapshot.coordinates.assumptionRoot
  rootActive :
    kernel.RootActiveAt carrier.value snapshot.coordinates.assumptionRoot
  dependenciesActive :
    ∀ assumption,
      assumption ∈ kernel.certificateDependencies currentAccepted.certificate →
        kernel.AssumptionActiveAt
          carrier.value snapshot.coordinates.assumptionRoot assumption
  indexedClaim :
    kernel.ClaimUnder
      snapshot.coordinates.assumptionRoot
      (kernel.historyAt carrier.value)
  mutants : MutantRefusal

def certificate : Certificate where
  currentJudgment := currentBinding.sound
  rootBound := currentBinding.sound.certificateRootBound
  rootActive := currentBinding.sound.rootActive
  dependenciesActive := by
    intro assumption member
    exact currentBinding.sound.dependenciesActive assumption member
  indexedClaim := currentBinding.sound.claim
  mutants :=
    { staleRootRefused := staleRootJudgmentRefused
      inactiveDependencyRefused := inactiveDependencyJudgmentRefused }

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.R4Target

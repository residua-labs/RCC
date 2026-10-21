import RCC.RCC21SurfaceTarget
import RCCTests.FormalCoreInvalidationClosure

/-! RCC-21 target package: sealed actual-influence terminal resolution. -/

namespace Residua.RCC.RCC21Target

open Residua.RCC
open Residua.RCC.InvalidationClosureTests

structure Certificate : Prop where
  terminalResolution :
    ∀ {S : InvalidationSystem.{0,0,0,0,0}}
      (complete : DependencyExtractionComplete S)
      (surface : SealedActualInfluenceSurface S)
      (snapshot : InvalidationSnapshot S)
      (newHead : S.Head) (edit : S.Edit)
      (plan :
        InvalidationPlan S snapshot edit
          (.certified (DependencyExtractionComplete.withSealedInfluence
            complete surface)) newHead)
      (node : S.Node) (judgment : S.Judgment)
      (terminal : snapshot.terminal judgment = true)
      (influence : S.actualInfluence node judgment)
      (writes : S.writes edit node),
        InvalidatedTerminalResolution
          S snapshot newHead edit
            (.certified (DependencyExtractionComplete.withSealedInfluence
              complete surface)) plan judgment
  directOnlyMutantRefused :
    ¬ DirectInvalidated .sourceEdit .staleGreen

def certificate : Certificate where
  terminalResolution := by
    intro S complete surface snapshot newHead edit plan node judgment terminal influence writes
    exact Residua.RCC.RCC21SurfaceTarget.sealed_actual_influence_terminal_lawfully_resolved
      complete surface snapshot newHead edit plan node judgment terminal influence writes
  directOnlyMutantRefused := direct_only_mutant_misses_transitive_source

theorem certificate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC21Target

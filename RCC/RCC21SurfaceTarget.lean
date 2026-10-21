import RCC.InvalidationSurface

/-!
# RCC-21A bounded target: sealed influence to terminal resolution

This target is deliberately narrower than the live repository/runtime
extractor obligation RCC-21.  It composes a sealed actual-influence surface
with the existing terminal-resolution theorem.  The surface remains an
instance certificate; this file does not claim that an arbitrary extractor
has complete transitive I/O coverage.
-/

namespace Residua.RCC.RCC21SurfaceTarget

open Residua.RCC

theorem sealed_actual_influence_terminal_lawfully_resolved
    {S : InvalidationSystem}
    (complete : DependencyExtractionComplete S)
    (surface : SealedActualInfluenceSurface S)
    (snapshot : InvalidationSnapshot S)
    (newHead : S.Head) (edit : S.Edit)
    (plan :
      InvalidationPlan S snapshot edit
        (.certified (DependencyExtractionComplete.withSealedInfluence
          complete surface)) newHead)
    (node : S.Node) (judgment : S.Judgment)
    (hterminal : snapshot.terminal judgment = true)
    (hinfluence : S.actualInfluence node judgment)
    (hwrites : S.writes edit node) :
    InvalidatedTerminalResolution
      S snapshot newHead edit
        (.certified (DependencyExtractionComplete.withSealedInfluence
          complete surface)) plan judgment := by
  exact actual_influence_terminal_lawfully_resolved
    S snapshot newHead edit
      (DependencyExtractionComplete.withSealedInfluence complete surface)
      plan node judgment hterminal hinfluence hwrites

end Residua.RCC.RCC21SurfaceTarget

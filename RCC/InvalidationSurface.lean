import RCC.InvalidationClosure

/-!
# RCC-21 Sealed Actual-Influence Surface

The invalidation kernel intentionally separates extractor exactness from the
claim that the supplied `actualInfluence` relation is complete.  This module
packages that latter claim as a finite, sealed evidence surface.  It is an
instance certificate, not a theorem that an arbitrary repository extractor is
complete.

Prelude-only Lean 4.14; all obligations are explicit and kernel-checked.
-/

namespace Residua.RCC

universe u v w x y

structure SealedActualInfluenceSurface (S : InvalidationSystem) where
  entries : List (S.Node × S.Judgment)
  entriesComplete :
    ∀ node judgment,
      S.actualInfluence node judgment →
        (node, judgment) ∈ entries
  entriesReachDependency :
    ∀ node judgment,
      (node, judgment) ∈ entries →
        DependencyClosure S.directDepends (S.judgmentNode judgment) node

theorem SealedActualInfluenceSurface.covers
    {S : InvalidationSystem}
    (surface : SealedActualInfluenceSurface S) :
    ∀ node judgment,
      S.actualInfluence node judgment →
        DependencyClosure S.directDepends (S.judgmentNode judgment) node := by
  intro node judgment hinfluence
  exact surface.entriesReachDependency node judgment
    (surface.entriesComplete node judgment hinfluence)

/-- Replace only the parametric `covers` premise with a sealed surface. -/
def DependencyExtractionComplete.withSealedInfluence
    {S : InvalidationSystem}
    (complete : DependencyExtractionComplete S)
    (surface : SealedActualInfluenceSurface S) :
    DependencyExtractionComplete S :=
  { complete with
    covers := surface.covers }

theorem withSealedInfluence_detectedExact
    {S : InvalidationSystem}
    (complete : DependencyExtractionComplete S)
    (surface : SealedActualInfluenceSurface S)
    (edit : S.Edit) (judgment : S.Judgment) :
    (DependencyExtractionComplete.withSealedInfluence complete surface).detected
        edit judgment = true ↔
      Invalidated S edit judgment :=
  complete.detectedExact edit judgment

theorem withSealedInfluence_actual_influence_write_invalidates
    {S : InvalidationSystem}
    (surface : SealedActualInfluenceSurface S)
    (edit : S.Edit) (node : S.Node) (judgment : S.Judgment)
    (hinfluence : S.actualInfluence node judgment)
    (hwrites : S.writes edit node) :
    Invalidated S edit judgment := by
  exact ⟨node, hwrites, surface.covers node judgment hinfluence⟩

end Residua.RCC

import RCC.InvalidationSurface
import RCCTests.FormalCoreInvalidationClosure

/-!
# RCC-62 target package

This candidate instantiates the sealed actual-influence surface on the finite
three-node invalidation fixture.  It proves that the sealed surface supplies
the dependency-closure coverage consumed by the exact detector.  The fixture
is deliberately not the repository/runtime extractor; RCC-21 remains open at
that live boundary.
-/

namespace Residua.RCC.RCC62Target

open Residua.RCC
open Residua.RCC.InvalidationClosureTests

def sealedDemoInfluence : SealedActualInfluenceSurface demoSystem where
  entries := [(.source, .staleGreen)]
  entriesComplete := by
    intro node judgment influence
    have h : node = .source ∧ judgment = .staleGreen := by
      cases node <;> cases judgment <;>
        simp [demoSystem, demoActualInfluence] at influence ⊢
    rcases h with ⟨rfl, rfl⟩
    simp
  entriesReachDependency := by
    intro node judgment member
    simp only [List.mem_singleton] at member
    have hnode : node = .source := congrArg Prod.fst member
    have hjudgment : judgment = .staleGreen := congrArg Prod.snd member
    cases hnode
    cases hjudgment
    exact staleDependsTransitivelyOnSource

theorem sealed_surface_covers_actual_influence :
    ∀ node judgment,
      demoSystem.actualInfluence node judgment →
        DependencyClosure demoSystem.directDepends
          (demoSystem.judgmentNode judgment) node := by
  exact sealedDemoInfluence.covers

def sealedComplete : DependencyExtractionComplete demoSystem :=
  DependencyExtractionComplete.withSealedInfluence
    demoExtractionComplete sealedDemoInfluence

theorem sealed_detector_remains_exact (edit : DemoEdit) (judgment : DemoJudgment) :
    sealedComplete.detected edit judgment = true ↔
      Invalidated demoSystem edit judgment := by
  exact sealedComplete.detectedExact edit judgment

structure Certificate where
  influenceCoverage :
    ∀ node judgment,
      demoSystem.actualInfluence node judgment →
        DependencyClosure demoSystem.directDepends
          (demoSystem.judgmentNode judgment) node
  detectorExactness :
    ∀ (edit : DemoEdit) (judgment : DemoJudgment),
      sealedComplete.detected edit judgment = true ↔
        Invalidated demoSystem edit judgment
  directOnlyMissesTransitiveSource :
    ¬ DirectInvalidated .sourceEdit .staleGreen
  directOnlyLeavesStaleGreenUsable :
    directOnlyMutant.currentState .staleGreen = .usable
  fullClosureRefusesDirectOnlyMutant :
    invalidatedSnapshot.currentState .staleGreen ≠
      directOnlyMutant.currentState .staleGreen

def certificate : Certificate where
  influenceCoverage := sealed_surface_covers_actual_influence
  detectorExactness := sealed_detector_remains_exact
  directOnlyMissesTransitiveSource := direct_only_mutant_misses_transitive_source
  directOnlyLeavesStaleGreenUsable := direct_only_mutant_leaves_stale_green_usable
  fullClosureRefusesDirectOnlyMutant := full_closure_refuses_direct_only_mutant

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RCC62Target

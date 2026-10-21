import RCC.RCC21SurfaceTarget
import RCCTests.FormalCoreInvalidationClosure

/-!
# RCC-21A bounded target witnesses

This is a finite positive control for the sealed-surface bridge.  It does not
claim that the repository/runtime extractor is complete; that remains the
open live RCC-21 boundary.
-/

open Residua.RCC

namespace Residua.RCC.RCC21SurfaceTargetTests

open Residua.RCC.InvalidationClosureTests
open Residua.RCC.RCC21SurfaceTarget

def sealedDemoSurface : SealedActualInfluenceSurface demoSystem where
  entries := [(.source, .staleGreen)]
  entriesComplete := by
    intro node judgment hinfluence
    have h : node = .source ∧ judgment = .staleGreen := by
      cases node <;> cases judgment <;>
        simp [demoSystem, demoActualInfluence] at hinfluence ⊢
    rcases h with ⟨rfl, rfl⟩
    simp
  entriesReachDependency := by
    intro node judgment hentry
    have hentry' : node = .source ∧ judgment = .staleGreen := by
      simpa using hentry
    rcases hentry' with ⟨rfl, rfl⟩
    exact staleDependsTransitivelyOnSource

def sealedComplete : DependencyExtractionComplete demoSystem :=
  DependencyExtractionComplete.withSealedInfluence
    demoExtractionComplete sealedDemoSurface

def sealedMode : InvalidationMode demoSystem := .certified sealedComplete

def sealedPlan :
    InvalidationPlan demoSystem initialSnapshot .sourceEdit sealedMode .new where
  resolve := fun judgment _ => by
    cases judgment with
    | staleGreen => exact .reopened
    | unrelatedGreen => exact .revalidated (by simp [demoSystem])

theorem sealed_surface_terminal_resolution :
    InvalidatedTerminalResolution
      demoSystem initialSnapshot .new .sourceEdit sealedMode sealedPlan
        .staleGreen := by
  exact sealed_actual_influence_terminal_lawfully_resolved
    demoExtractionComplete sealedDemoSurface initialSnapshot .new .sourceEdit
      sealedPlan .source .staleGreen
      (by simp [initialSnapshot])
      (by simp [demoSystem, demoActualInfluence])
      (by simp [demoSystem, demoWrites])

theorem sealed_surface_reopens_transitive_stale_green :
    (applyInvalidation demoSystem initialSnapshot .new .sourceEdit
      sealedMode sealedPlan).currentState .staleGreen = .reopened := by
  simp [applyInvalidation, invalidatedPostState, sealedMode, sealedComplete,
    DependencyExtractionComplete.withSealedInfluence, demoExtractionComplete,
    sealedPlan, needsResolution, demoDetected, InvalidationResolution.state,
    initialSnapshot, demoSystem]

theorem direct_only_surface_is_rejected :
    ¬ DirectInvalidated .sourceEdit .staleGreen :=
  direct_only_mutant_misses_transitive_source

end Residua.RCC.RCC21SurfaceTargetTests

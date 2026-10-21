import RCC.GlobalIntentCoverage

/-! RCC-R3 candidate: mandatory local component/seam claims require an explicit
    one-way coverage theorem before they can establish a global intent.

    *Sufficiency* is carried by the positive field `localClaimsSuffice`, which
    invokes the `coversGlobalIntent` theorem: complete local closure evidence
    plus a one-way `CompositionIntentContract` yields the declared global
    intent.

    *Necessity* is carried by the refusal field `coverageTheoremNecessary`.
    A fixture world `demoWorld` supplies complete local closure evidence and
    makes every declared local claim true, yet for an unsupported global
    intent (`demoGlobalIntent = False`) no `CompositionIntentContract` can
    exist: its load-bearing `localClaimsSuffice` field would have to derive
    `False` from `True`, which is impossible.  Local claims therefore do not
    pin down a global intent on their own; the explicit one-way coverage
    theorem is the necessary bridge. -/

namespace Residua.RCC.R3Target

open Residua.RCC.FacetCoherence
open Residua.RCC.GlobalIntentCoverage

/-! A minimal coherence world: one trivially-closed component and no seams.
    `globalClosed` is `False`; only an explicit coverage theorem could ever
    establish a global intent here, and for `GlobalIntent = False` none can. -/

def demoWorld : CoherenceWorld.{0} where
  State := Unit
  Address := Unit
  stateEquivalent := fun _ _ => True
  stateAddress := fun _ => ()
  reduces := fun _ _ => False
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => False
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 0
  artifactLevel := fun _ => 0
  verifies := fun _ _ => False
  migrates := fun _ _ => False
  terminalAt := fun _ _ => True
  carries := fun _ _ => False
  RuntimeState := Unit
  runtimeStep := fun _ _ => False
  abstractState := fun _ => ()
  Component := Unit
  Seam := Empty
  components := [()]
  seams := []
  componentClosed := fun _ => True
  seamExact := fun _ => True
  globalClosed := False

abbrev demoComponentIntent : demoWorld.Component → Prop := fun _ => True
abbrev demoSeamIntent : demoWorld.Seam → Prop := fun _ => True
abbrev demoGlobalIntent : Prop := False

/-- Complete local closure evidence for the demo world. -/
def demoClosureEvidence : CompositionClosureEvidence demoWorld where
  componentsClosed := fun _ _ => trivial
  seamsExact := fun _ member => nomatch member

/--
No contract can establish an unsupported global intent.  With every local
claim true and `GlobalIntent = False`, the `localClaimsSuffice` field of a
`CompositionIntentContract` would have to derive `False` from `True` —
impossible.  The one-way coverage theorem is therefore load-bearing.
-/
theorem noContractForUnsupportedGlobalIntent :
    ¬ CompositionIntentContract
        demoWorld demoComponentIntent demoSeamIntent demoGlobalIntent := by
  intro contract
  exact
    contract.localClaimsSuffice
      (fun _ _ => trivial)
      (fun _ member => nomatch member)

structure Certificate where
  localClaimsSuffice :
    ∀ {world : CoherenceWorld.{0}}
      {ComponentIntent : world.Component → Prop}
      {SeamIntent : world.Seam → Prop}
      {GlobalIntent : Prop},
      CompositionClosureEvidence world →
      CompositionIntentContract
        world ComponentIntent SeamIntent GlobalIntent →
      GlobalIntent
  /--
  Necessity half of R3: complete local closure evidence plus every local
  claim can still coexist with a global intent that no coverage theorem can
  reach.  The one-way coverage theorem (`localClaimsSuffice` on the
  contract) is exactly the missing bridge. -/
  coverageTheoremNecessary :
    CompositionClosureEvidence demoWorld ∧
      (∀ component,
        component ∈ demoWorld.components →
          demoComponentIntent component) ∧
      (∀ seam, seam ∈ demoWorld.seams → demoSeamIntent seam) ∧
      ¬ CompositionIntentContract
          demoWorld demoComponentIntent demoSeamIntent demoGlobalIntent

def certificate : Certificate where
  localClaimsSuffice := by
    intro world ComponentIntent SeamIntent GlobalIntent evidence contract
    exact evidence.coversGlobalIntent contract
  coverageTheoremNecessary := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact demoClosureEvidence
    · exact fun _ _ => trivial
    · exact fun _ member => nomatch member
    · exact noContractForUnsupportedGlobalIntent

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.R3Target

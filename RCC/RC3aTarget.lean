import RCC.FacetCoherence

/-!
# RC-3a target: RCC self-check is stratified

RC-3a is the discharged half of the RC-3 split ("RCC self-check is stratified
and may govern only a successor epoch"): an RCC self-check may only be
accepted when the verifying stratum is strictly above the artifact it checks.

The law itself is not manufactured here.  It already exists, for an
independent reason, in `RCC.FacetCoherence` — the FC-2
reflection-stratification bridge serving the CM-SELF discipline:

* `ReflectionVerificationLaw.verifierAboveArtifact`, exposed as the theorem
  `acceptedVerificationIsStratified` (every accepted verification is strictly
  stratified); and
* the `ReflectionFacetSurface.verificationStratified` field (every
  `VerificationToken` forces `artifactLevel < verifierLevel`).

This Target only connects that content to the obligation: the two positive
certificate fields restate those theorems parametrically, by import.

The refusal half is a NEW minimal harness fixture, flagged for audit.  The
CM-SELF-01 open spec obligation (`same_level_self_ready`: "RCC authorizes its
own soundness at the same reflection level") names the stance to refuse, but
no Lean fixture for it existed.  `harnessWorld` below is the smallest
`CoherenceWorld` whose `verifies` is exactly strict level increase: one unit
verifier at level 1, and a two-element artifact universe at levels 0 and 1.
In it the strictly-lower artifact is accepted (non-vacuity), while the
same-level artifact is refused at witnessed equal levels.  In the
`CoherenceWorld` vocabulary verifier and artifact live in distinct types, so
the expressible form of self-verification is same-level verification.

Scope honesty: nothing here certifies a production RCC self-check pipeline,
and the successor-epoch governance half of RC-3 remains outside this Target.
The parametric fields are the FacetCoherence theorems themselves; the fixture
exists only to give those theorems a non-vacuous, refusing instance.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.RC3aTarget

open Residua.RCC.FacetCoherence

/-! ## New minimal harness fixture (flagged for audit) -/

/-- The single verifier stratum of the harness: level 1. -/
def harnessVerifierLevel : Unit → Nat :=
  fun _ => 1

/-- The two-element artifact universe: level 0 and level 1. -/
def harnessArtifactLevel : Bool → Nat :=
  fun artifact =>
    match artifact with
    | true => 1
    | false => 0

/-- The smallest world the tooth needs: `verifies` is *exactly* strict level
increase, and every other bridge vocabulary is trivial. -/
def harnessWorld : CoherenceWorld.{0} where
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
  Artifact := Bool
  verifierLevel := harnessVerifierLevel
  artifactLevel := harnessArtifactLevel
  verifies := fun verifier artifact =>
    harnessArtifactLevel artifact < harnessVerifierLevel verifier
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
  globalClosed := True

/-- The harness world is a legitimate instance of the imported law: its
`verifies` already is the strict increase, so the bridge holds definitionally. -/
def harnessLaw : ReflectionVerificationLaw harnessWorld where
  verifierAboveArtifact := fun _ _ accepted => accepted

/-- Non-vacuity tooth: the strictly-lower artifact is accepted. -/
theorem belowAccepted : harnessWorld.verifies () false := by
  show (0 : Nat) < 1
  decide

/-- The imported universal theorem, instantiated at the harness, certifies the
accepted point. -/
theorem belowStratifiedViaImportedLaw :
    harnessWorld.artifactLevel false < harnessWorld.verifierLevel () :=
  acceptedVerificationIsStratified harnessLaw belowAccepted

/-- The refusal is genuinely at equal levels. -/
theorem sameLevelLevelsEqual :
    harnessWorld.verifierLevel () = harnessWorld.artifactLevel true := by
  show (1 : Nat) = 1
  rfl

/-- Same-level verification is refused: strict stratification leaves no room
for the CM-SELF-01 `same_level_self_ready` stance. -/
theorem sameLevelNotAccepted : ¬ harnessWorld.verifies () true := by
  show ¬ ((1 : Nat) < 1)
  decide

/-! ## The certificate -/

structure Certificate : Prop where
  /-- Connects existing content: the FacetCoherence theorem
      `acceptedVerificationIsStratified`, restated parametrically over every
      world and every law instance. -/
  acceptedVerificationStratified :
    ∀ {world : CoherenceWorld.{0}}
      (_law : ReflectionVerificationLaw world)
      {verifier : world.Verifier}
      {artifact : world.Artifact}
      (_accepted : world.verifies verifier artifact),
      world.artifactLevel artifact < world.verifierLevel verifier
  /-- Connects existing content: the `ReflectionFacetSurface` field law
      `verificationStratified`, restated parametrically over every index,
      carrier, and decoded surface. -/
  verificationSurfaceStratified :
    ∀ {Carrier : Type}
      {index : FacetSemanticIndex Carrier}
      {carrier : Carrier}
      (_surface : ReflectionFacetSurface index carrier)
      (verifier : (index.world carrier).Verifier)
      (artifact : (index.world carrier).Artifact)
      (_token : index.VerificationToken carrier verifier artifact),
      (index.world carrier).artifactLevel artifact <
        (index.world carrier).verifierLevel verifier
  /-- New minimal harness tooth (flagged for audit), bilateral: the
      strictly-lower artifact is accepted (an always-refusing `verifies`
      cannot fake stratification), the same-level artifact is refused, and
      the refusal is witnessed at equal levels. -/
  sameLevelRefused :
    harnessWorld.verifies () false ∧
      harnessWorld.verifierLevel () = harnessWorld.artifactLevel true ∧
      ¬ harnessWorld.verifies () true

def certificate : Certificate where
  acceptedVerificationStratified := by
    intro _world law _verifier _artifact accepted
    exact acceptedVerificationIsStratified law accepted
  verificationSurfaceStratified := by
    intro _Carrier _index _carrier surface verifier artifact token
    exact surface.verificationStratified verifier artifact token
  sameLevelRefused :=
    ⟨belowAccepted, sameLevelLevelsEqual, sameLevelNotAccepted⟩

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.RC3aTarget

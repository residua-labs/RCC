/-!
# RCC-30 Actuation Binding

An admitted artifact is not yet a live product path.  This kernel models the
ordered closure grades as proof-carrying extensions: every later certificate
contains the complete earlier certificate, while actuation, observation,
authority retirement, and rollback settlement add their own witnesses.

`LiveIntentClosed` deliberately does not imply deployment liveness or external
observation authenticity.  Those remain separately named world assumptions.
The kernel proves only that the admitted evidence binds one exact artifact and
target through activation and live observation.

Prelude-only Lean 4.14; no Mathlib, no `sorry`, no custom axioms (some theorems use the standard `propext`).
-/

namespace Residua.RCC.ActuationBinding

universe u v w x y z

/-! ## Ordered closure grades -/

/-- The frozen seven-grade artifact-to-live closure ladder from ADR §21.6. -/
inductive ClosureGrade where
  | specified
  | proved
  | built
  | admitted
  | activated
  | observedConformant
  | rollbackSettled
  deriving DecidableEq, Repr

namespace ClosureGrade

/-- Numerical presentation of the frozen grade order. -/
def rank : ClosureGrade → Nat
  | .specified => 0
  | .proved => 1
  | .built => 2
  | .admitted => 3
  | .activated => 4
  | .observedConformant => 5
  | .rollbackSettled => 6

/-- Earlier-or-equal in the artifact-to-live closure ladder. -/
def Precedes (earlier later : ClosureGrade) : Prop :=
  rank earlier ≤ rank later

instance (earlier later : ClosureGrade) : Decidable (Precedes earlier later) :=
  inferInstanceAs (Decidable (rank earlier ≤ rank later))

theorem total (left right : ClosureGrade) :
    Precedes left right ∨ Precedes right left :=
  Nat.le_total (rank left) (rank right)

theorem trans {first second third : ClosureGrade}
    (firstSecond : Precedes first second)
    (secondThird : Precedes second third) :
    Precedes first third :=
  Nat.le_trans firstSecond secondThird

end ClosureGrade

/-! ## Domain evidence supplied by one actuation instance -/

/--
Domain relations and projections used by actuation certificates.

`deploymentEventuallyOccurs` and `observationAuthentic` are deliberately
separate external-world propositions.  They do not participate in
`LiveIntentClosed`, so this kernel never manufactures either claim.

`priorLiveAuthority` is the instance-supplied inventory relation consumed by
this kernel.  `priorAuthorityInventoryAdequate` is the corresponding
instance/world certificate that the declared inventory is sufficient for this
artifact and target.  RCC-30 requires that certificate and proves retirement
for every authority the relation declares; deriving the certificate from a
repository/runtime remains a separate extraction obligation.
-/
structure ActuationSystem where
  Artifact : Type u
  DeploymentTarget : Type v
  ActivationEvent : Type w
  LiveObservation : Type x
  Authority : Type y
  Rollback : Type z

  specified : Artifact → Prop
  proved : Artifact → Prop
  built : Artifact → Prop
  codeMerged : Artifact → Prop
  ciGreen : Artifact → Prop
  artifactAdmitted : Artifact → Prop

  deploymentTargetBound : Artifact → DeploymentTarget → Prop
  activationEventAdmitted : ActivationEvent → Prop
  activationArtifact : ActivationEvent → Artifact
  activationTarget : ActivationEvent → DeploymentTarget

  liveObservationAdmitted : LiveObservation → Prop
  observedArtifact : LiveObservation → Artifact
  observedTarget : LiveObservation → DeploymentTarget

  priorLiveAuthority : Authority → Artifact → DeploymentTarget → Prop
  priorAuthorityInventoryAdequate : Artifact → DeploymentTarget → Prop
  oldAuthorityRetired : Authority → DeploymentTarget → Prop
  rollbackSettled : Rollback → Artifact → DeploymentTarget → Prop

  /-- Explicit nonclaim: eventual deployment is an external liveness proposition. -/
  deploymentEventuallyOccurs : Artifact → DeploymentTarget → Prop
  /-- Explicit nonclaim: observation authenticity is supplied by a world-interface layer. -/
  observationAuthentic : LiveObservation → Prop

/-! ## Proof-carrying grade certificates -/

structure Specified (system : ActuationSystem) (artifact : system.Artifact) : Prop where
  specificationAccepted : system.specified artifact

structure Proved (system : ActuationSystem) (artifact : system.Artifact) : Prop where
  toSpecified : Specified system artifact
  proofAccepted : system.proved artifact

structure Built (system : ActuationSystem) (artifact : system.Artifact) : Prop where
  toProved : Proved system artifact
  buildAvailable : system.built artifact

structure Admitted (system : ActuationSystem) (artifact : system.Artifact) : Prop where
  toBuilt : Built system artifact
  admissionAccepted : system.artifactAdmitted artifact

/--
Activation is tied to both the exact admitted artifact and the exact deployment
target.  A shadow deployment cannot inhabit this certificate for the live path.
-/
structure Activated (system : ActuationSystem) (artifact : system.Artifact)
    (target : system.DeploymentTarget) : Prop where
  toAdmitted : Admitted system artifact
  targetBound : system.deploymentTargetBound artifact target
  activationEvidence :
    ∃ activation,
      system.activationEventAdmitted activation ∧
        system.activationArtifact activation = artifact ∧
        system.activationTarget activation = target

/--
The live observation is admitted and names the same artifact and target as the
activation certificate.  Authenticity of the external observation source is
intentionally outside this certificate.
-/
structure ObservedConformant (system : ActuationSystem) (artifact : system.Artifact)
    (target : system.DeploymentTarget) : Prop where
  toActivated : Activated system artifact target
  observationEvidence :
    ∃ observation,
      system.liveObservationAdmitted observation ∧
        system.observedArtifact observation = artifact ∧
        system.observedTarget observation = target

/--
Final actuation closure additionally retires the old authority and settles the
rollback path.  Neither a merged artifact nor a green CI result supplies these
fields.  Retirement ranges over every authority declared by the supplied
prior-authority inventory; retiring an unrelated decoy cannot satisfy it.
-/
structure RollbackSettled (system : ActuationSystem) (artifact : system.Artifact)
    (target : system.DeploymentTarget) : Prop where
  toObservedConformant : ObservedConformant system artifact target
  inventoryAdequate :
    system.priorAuthorityInventoryAdequate artifact target
  authorityRetirement :
    ∀ oldAuthority,
      system.priorLiveAuthority oldAuthority artifact target →
        system.oldAuthorityRetired oldAuthority target
  rollbackSettlement :
    ∃ rollback, system.rollbackSettled rollback artifact target

/-- The final live-behavior closure certificate. -/
abbrev LiveIntentClosed (system : ActuationSystem) (artifact : system.Artifact)
    (target : system.DeploymentTarget) : Prop :=
  RollbackSettled system artifact target

/--
Artifact-only closure records merged, green, admitted code.  It intentionally
contains no target, activation, live observation, authority-retirement, or
rollback evidence.
-/
structure ArtifactClosed (system : ActuationSystem) (artifact : system.Artifact) :
    Prop where
  admittedArtifact : Admitted system artifact
  codeMerged : system.codeMerged artifact
  ciGreen : system.ciGreen artifact

/-! ## RCC-30 headline and grade projections -/

theorem live_intent_closed_implies_activated
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    Activated system artifact target :=
  closed.toObservedConformant.toActivated

theorem live_intent_closed_implies_observed_conformant
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    ObservedConformant system artifact target :=
  closed.toObservedConformant

/-- RCC-30: live closure contains both activation and exact-artifact observation. -/
theorem live_intent_closed_implies_activated_and_observed_conformant
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    Activated system artifact target ∧
      ObservedConformant system artifact target :=
  ⟨live_intent_closed_implies_activated closed,
    live_intent_closed_implies_observed_conformant closed⟩

theorem live_intent_closed_implies_artifact_admitted
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    Admitted system artifact :=
  closed.toObservedConformant.toActivated.toAdmitted

/--
Live closure carries the instance/world certificate that the supplied prior
authority inventory is adequate for this artifact and target.
-/
theorem live_intent_closed_implies_prior_authority_inventory_adequate
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target) :
    system.priorAuthorityInventoryAdequate artifact target :=
  closed.inventoryAdequate

/-- Every authority declared prior-live for the target is retired at closure. -/
theorem live_intent_closed_retires_every_declared_prior_authority
    {system : ActuationSystem} {artifact : system.Artifact}
    {target : system.DeploymentTarget}
    (closed : LiveIntentClosed system artifact target)
    (authority : system.Authority)
    (prior : system.priorLiveAuthority authority artifact target) :
    system.oldAuthorityRetired authority target :=
  closed.authorityRetirement authority prior

end Residua.RCC.ActuationBinding

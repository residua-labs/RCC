import RCC.ActuationBinding
import RCC.EffectSettlement

/-!
# WI-5 Actuation soundness

Artifact evidence and live actuation are different proof surfaces.  A proved,
built, merged, or even admitted artifact does not by itself authorize an
external effect.  This kernel admits an actuation only when one exact packet is
bound to:

* an admitted activation of the exact artifact and deployment target;
* the sealed snapshot head and declared effect occurrence;
* a pre-state authority check;
* the measured runtime;
* the declared semantic effect.

The head and occurrence coordinates reuse RCC-31's effect-settlement types.
`EffectSnapshot.head` is only the declared head of that sealed snapshot here;
canonicality and finality require their separate RCC history certificates.
Settlement is a later obligation: WI-5 proves only that an admitted invocation
produces the declared `EffectRelation`.  It does not claim that the effect was
eventually delivered, durably recorded, or observed authentically.

Prelude-only Lean 4.14; no Mathlib, proof placeholders, or custom assumptions.
-/

namespace Residua.RCC.ActuationSoundness

open ActuationBinding EffectSettlement

/--
The domain bridge from an exact runtime invocation to a semantic effect.

The three boolean procedures are executable admission checks.  Their soundness
fields are the only way their results enter the proof of `EffectRelation`.
-/
structure WorldActuationSystem
    (binding : ActuationSystem)
    (Epoch Head EffectSlot Generation Occurrence FailureName : Type) where
  World : Type
  Runtime : Type
  Actuator : Type
  Effect : Type

  AuthorityAllows :
    EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName →
      World → binding.Authority → binding.Artifact →
      binding.DeploymentTarget → Actuator → Prop
  RuntimeRealizes :
    Runtime → binding.Artifact → binding.DeploymentTarget → Prop
  DeclaresEffect :
    binding.Artifact → binding.DeploymentTarget →
      ExternalEffect Occurrence Head EffectSlot → Effect → Prop

  verifyAuthority :
    EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName →
      World → binding.Authority → binding.Artifact →
      binding.DeploymentTarget → Actuator → Bool
  verifyRuntime :
    Runtime → binding.Artifact → binding.DeploymentTarget → Bool
  verifyEffect :
    binding.Artifact → binding.DeploymentTarget →
      ExternalEffect Occurrence Head EffectSlot → Effect → Bool

  authoritySound :
    ∀ snapshot pre authority artifact target actuator,
      verifyAuthority
          snapshot pre authority artifact target actuator = true →
        AuthorityAllows
          snapshot pre authority artifact target actuator
  runtimeSound :
    ∀ runtime artifact target,
      verifyRuntime runtime artifact target = true →
        RuntimeRealizes runtime artifact target
  effectSound :
    ∀ (artifact : binding.Artifact)
      (target : binding.DeploymentTarget)
      (external : ExternalEffect Occurrence Head EffectSlot)
      (effect : Effect),
      verifyEffect artifact target external effect = true →
        DeclaresEffect artifact target external effect

  apply : Actuator → Runtime → World → Effect → World
  EffectRelation : World → Effect → World → Prop
  applySound :
    ∀ (snapshot :
        EffectSnapshot
          Epoch Head EffectSlot Generation Occurrence FailureName)
      (authority : binding.Authority)
      (artifact : binding.Artifact)
      (target : binding.DeploymentTarget)
      (external : ExternalEffect Occurrence Head EffectSlot)
      (actuator : Actuator)
      (runtime : Runtime)
      (pre : World)
      (effect : Effect),
      AuthorityAllows
        snapshot pre authority artifact target actuator →
      RuntimeRealizes runtime artifact target →
      DeclaresEffect artifact target external effect →
      EffectRelation pre effect (apply actuator runtime pre effect)

/--
One effect occurrence selected from RCC-31's sealed effect snapshot.
Membership is proof-carrying: a caller cannot manufacture a new occurrence
outside the current effect universe.
-/
structure DeclaredEffectContext
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    where
  effect : ExternalEffect Occurrence Head EffectSlot
  declared : effect ∈ snapshot.externalEffects

/--
Activation evidence is deliberately explicit.  `.absent` represents every
artifact-only state, including a proved, merged, green, or admitted artifact.
-/
inductive ActivationAuthorization
    (binding : ActuationSystem)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget) where
  | absent
  | certified (proof : Activated binding artifact target)

/-- An untrusted request to perform one external effect. -/
structure ActuationAttempt
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    (system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName)
    where
  claimedHead : Head
  claimedOccurrence : Occurrence
  authority : binding.Authority
  actuator : system.Actuator
  runtime : system.Runtime
  effect : system.Effect
  preWorld : system.World

/-- Every failed admission check has a typed, non-mutating residue. -/
inductive ActuationResidue where
  | staleHead
  | staleDeclaredEffectHead
  | occurrenceMismatch
  | artifactNotActivated
  | actuatorUnauthorized
  | runtimeUnbound
  | effectUndeclared
  deriving DecidableEq, Repr

/--
The proof object exported by successful admission.  Its post-world is the
actual domain `apply`, and its final field proves exactly the declared relation.
-/
structure AdmittedActuation
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    (system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName)
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (context : DeclaredEffectContext snapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (attempt : ActuationAttempt system) : Prop where
  activated : Activated binding artifact target
  snapshotHeadBound : attempt.claimedHead = snapshot.head
  declaredEffectHeadBound : context.effect.expectedParent = snapshot.head
  occurrenceBound : attempt.claimedOccurrence = context.effect.occurrence
  authorityAccepted :
    system.AuthorityAllows
      snapshot attempt.preWorld
      attempt.authority artifact target attempt.actuator
  runtimeAccepted :
    system.RuntimeRealizes attempt.runtime artifact target
  effectAccepted :
    system.DeclaresEffect artifact target context.effect attempt.effect
  effectRelation :
    system.EffectRelation
      attempt.preWorld
      attempt.effect
      (system.apply
        attempt.actuator attempt.runtime attempt.preWorld attempt.effect)

inductive AdmissionResult
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    (system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName)
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (context : DeclaredEffectContext snapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (attempt : ActuationAttempt system) where
  | admitted :
      AdmittedActuation system snapshot context artifact target attempt →
      AdmissionResult system snapshot context artifact target attempt
  | refused :
      ActuationResidue →
      AdmissionResult system snapshot context artifact target attempt

/--
The common WI-5 admission tree.  Instances supply facts and sound executable
checks, but cannot supply their own "actuated" status.
-/
def admitActuation
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    [DecidableEq Head] [DecidableEq Occurrence]
    (system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName)
    (snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName)
    (context : DeclaredEffectContext snapshot)
    (artifact : binding.Artifact)
    (target : binding.DeploymentTarget)
    (activation : ActivationAuthorization binding artifact target)
    (attempt : ActuationAttempt system) :
    AdmissionResult system snapshot context artifact target attempt := by
  if snapshotHead : attempt.claimedHead = snapshot.head then
    if effectHead : context.effect.expectedParent = snapshot.head then
      if occurrence :
          attempt.claimedOccurrence = context.effect.occurrence then
        match activation with
        | .absent =>
            exact .refused .artifactNotActivated
        | .certified activated =>
            if authority :
                system.verifyAuthority
                    snapshot attempt.preWorld
                    attempt.authority artifact target attempt.actuator = true then
              if runtime :
                  system.verifyRuntime attempt.runtime artifact target = true then
                if effect :
                    system.verifyEffect
                        artifact target context.effect attempt.effect = true then
                  exact .admitted {
                    activated := activated
                    snapshotHeadBound := snapshotHead
                    declaredEffectHeadBound := effectHead
                    occurrenceBound := occurrence
                    authorityAccepted :=
                      system.authoritySound
                        snapshot attempt.preWorld
                        attempt.authority artifact target attempt.actuator authority
                    runtimeAccepted :=
                      system.runtimeSound attempt.runtime artifact target runtime
                    effectAccepted :=
                      system.effectSound
                        artifact target context.effect attempt.effect effect
                    effectRelation :=
                      system.applySound
                        snapshot attempt.authority artifact target context.effect
                        attempt.actuator attempt.runtime attempt.preWorld
                        attempt.effect
                        (system.authoritySound
                          snapshot attempt.preWorld
                          attempt.authority artifact target attempt.actuator authority)
                        (system.runtimeSound attempt.runtime artifact target runtime)
                        (system.effectSound
                          artifact target context.effect attempt.effect effect)
                  }
                else
                  exact .refused .effectUndeclared
              else
                exact .refused .runtimeUnbound
            else
              exact .refused .actuatorUnauthorized
      else
        exact .refused .occurrenceMismatch
    else
      exact .refused .staleDeclaredEffectHead
  else
    exact .refused .staleHead

/-! ## Headline soundness projections -/

theorem admitted_actuation_only_declared_effect
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {context : DeclaredEffectContext snapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {attempt : ActuationAttempt system}
    (admitted :
      AdmittedActuation system snapshot context artifact target attempt) :
    system.EffectRelation
      attempt.preWorld
      attempt.effect
      (system.apply
        attempt.actuator attempt.runtime attempt.preWorld attempt.effect) :=
  admitted.effectRelation

theorem admitted_actuation_binds_snapshot_head_and_occurrence
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {context : DeclaredEffectContext snapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {attempt : ActuationAttempt system}
    (admitted :
      AdmittedActuation system snapshot context artifact target attempt) :
    attempt.claimedHead = snapshot.head ∧
      context.effect.expectedParent = snapshot.head ∧
      attempt.claimedOccurrence = context.effect.occurrence :=
  ⟨admitted.snapshotHeadBound,
    admitted.declaredEffectHeadBound,
    admitted.occurrenceBound⟩

/--
WI-5 headline: a successful admission binds activation, the sealed head and
occurrence, pre-state authority, measured runtime, declared effect, and the
resulting semantic effect relation in one proof object.
-/
theorem AdmittedActuation.sound
    {binding : ActuationSystem}
    {Epoch Head EffectSlot Generation Occurrence FailureName : Type}
    {system :
      WorldActuationSystem
        binding Epoch Head EffectSlot Generation Occurrence FailureName}
    {snapshot :
      EffectSnapshot Epoch Head EffectSlot Generation Occurrence FailureName}
    {context : DeclaredEffectContext snapshot}
    {artifact : binding.Artifact}
    {target : binding.DeploymentTarget}
    {attempt : ActuationAttempt system}
    (admitted :
      AdmittedActuation system snapshot context artifact target attempt) :
    Activated binding artifact target ∧
      attempt.claimedHead = snapshot.head ∧
      context.effect.expectedParent = snapshot.head ∧
      attempt.claimedOccurrence = context.effect.occurrence ∧
      system.AuthorityAllows
        snapshot attempt.preWorld
        attempt.authority artifact target attempt.actuator ∧
      system.RuntimeRealizes attempt.runtime artifact target ∧
      system.DeclaresEffect
        artifact target context.effect attempt.effect ∧
      system.EffectRelation
        attempt.preWorld
        attempt.effect
        (system.apply
          attempt.actuator attempt.runtime attempt.preWorld attempt.effect) :=
  ⟨admitted.activated,
    admitted.snapshotHeadBound,
    admitted.declaredEffectHeadBound,
    admitted.occurrenceBound,
    admitted.authorityAccepted,
    admitted.runtimeAccepted,
    admitted.effectAccepted,
    admitted.effectRelation⟩

end Residua.RCC.ActuationSoundness

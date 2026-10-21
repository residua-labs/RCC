import RCC.AssumptionRelativeSoundness

namespace Residua.RCC.AssumptionRelativeSoundness.Tests

open Residua.RCC
open Residua.RCC.FacetSnapshot

inductive Root
  | current
  | stale
  deriving DecidableEq, Repr

inductive Assumption
  | trusted
  | revoked
  deriving DecidableEq, Repr

structure Certificate where
  root : Root
  dependencies : List Assumption
  payload : Bool

def goal : GoalContract where
  History := Bool
  Certificate := Certificate
  lawful := fun _ => True
  claim := fun history => history = true
  verify := fun history certificate => history && certificate.payload
  mutantVerify := fun _ _ => true

def verifier : SoundGoalVerifier goal where
  acceptedSound := by
    intro history certificate accepted
    cases history <;> simp [goal] at accepted ⊢

abbrev Epoch := Unit
abbrev HistoryHead := Unit
abbrev AddressRegistry := Unit
abbrev SourceWindow := Unit
abbrev FailureModel := Unit
abbrev ProposalWindow := Unit
abbrev ImplementationBundle := Unit

def sealSpec :
    SnapshotSeal
      Epoch HistoryHead Root AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle where
  IsSealed := fun _ => True

def snapshot : SealedSnapshot sealSpec where
  coordinates :=
    { epoch := ()
      historyHead := ()
      assumptionRoot := .current
      addressRegistry := ()
      sourceWindow := ()
      failureModel := ()
      proposalWindow := ()
      implementationBundle := () }
  sealed := trivial

structure Carrier where
  history : Bool
  root : Root

def projection :
    CarrierProjection
      Carrier Epoch HistoryHead Root AddressRegistry SourceWindow FailureModel
        ProposalWindow ImplementationBundle where
  epoch := fun _ => ()
  historyHead := fun _ => ()
  assumptionRoot := Carrier.root
  addressRegistry := fun _ => ()
  sourceWindow := fun _ => ()
  failureModel := fun _ => ()
  proposalWindow := fun _ => ()
  implementationBundle := fun _ => ()

def carrier : SnapshotCarrier projection snapshot where
  value := ⟨true, .current⟩
  epochBound := rfl
  historyHeadBound := rfl
  assumptionRootBound := rfl
  addressRegistryBound := rfl
  sourceWindowBound := rfl
  failureModelBound := rfl
  proposalWindowBound := rfl
  implementationBundleBound := rfl

def kernel : AssumptionRelativeGoalKernel projection goal where
  Assumption := Assumption
  historyAt := Carrier.history
  certificateRoot := Certificate.root
  certificateDependencies := Certificate.dependencies
  RootActiveAt := fun _ root => root = .current
  AssumptionActiveAt := fun _ root assumption =>
    root = .current ∧ assumption = .trusted
  ClaimUnder := fun _ history => history = true
  claimExact := by
    intro observed
    rfl

def currentCertificate : Certificate :=
  ⟨.current, [.trusted], true⟩

def currentAccepted :
    AcceptedGoalCertificate goal verifier (kernel.historyAt carrier.value) where
  certificate := currentCertificate
  accepted := rfl

def currentBinding :
    AssumptionRelativeCertificateBindingAt
      kernel snapshot carrier currentAccepted where
  certificateRootBound := rfl
  rootActive := rfl
  dependenciesActive := by
    intro assumption member
    have same : assumption = .trusted :=
      List.eq_of_mem_singleton member
    exact ⟨rfl, same⟩

theorem current_active_root_proves_relative_claim :
    kernel.ClaimUnder
      snapshot.coordinates.assumptionRoot
      (kernel.historyAt carrier.value) :=
  currentBinding.sound.claim

def staleCertificate : Certificate :=
  ⟨.stale, [.trusted], true⟩

def staleAccepted :
    AcceptedGoalCertificate goal verifier (kernel.historyAt carrier.value) where
  certificate := staleCertificate
  accepted := rfl

/-- R2 alone proves the raw Goal claim even though its certificate root is stale. -/
theorem r2_alone_accepts_stale_root :
    goal.claim (kernel.historyAt carrier.value) :=
  staleAccepted.sound

/-- The R4 root equality blocks that stale certificate from current authority. -/
theorem stale_root_cannot_bind :
    ¬ AssumptionRelativeCertificateBindingAt
      kernel snapshot carrier staleAccepted := by
  intro binding
  cases binding.certificateRootBound

def inactiveKernel : AssumptionRelativeGoalKernel projection goal :=
  { kernel with RootActiveAt := fun _ _ => False }

def inactiveAccepted :
    AcceptedGoalCertificate
      goal verifier (inactiveKernel.historyAt carrier.value) where
  certificate := currentCertificate
  accepted := rfl

/-- Exact root bytes are insufficient when the root is not currently active. -/
theorem inactive_root_cannot_bind :
    ¬ AssumptionRelativeCertificateBindingAt
      inactiveKernel snapshot carrier inactiveAccepted := by
  intro binding
  exact binding.rootActive

def inactiveDependencyKernel : AssumptionRelativeGoalKernel projection goal :=
  { kernel with AssumptionActiveAt := fun _ _ _ => False }

def inactiveDependencyAccepted :
    AcceptedGoalCertificate
      goal verifier (inactiveDependencyKernel.historyAt carrier.value) where
  certificate := currentCertificate
  accepted := rfl

/-- A current active root cannot hide an inactive dependency named by the certificate. -/
theorem inactive_listed_dependency_cannot_bind :
    ¬ AssumptionRelativeCertificateBindingAt
      inactiveDependencyKernel snapshot carrier inactiveDependencyAccepted := by
  intro binding
  exact binding.dependenciesActive .trusted (List.Mem.head [])

end Residua.RCC.AssumptionRelativeSoundness.Tests

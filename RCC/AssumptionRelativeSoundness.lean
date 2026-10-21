import RCC.VerifierSoundness
import RCC.FacetSnapshot

/-!
# R4 assumption-relative judgment soundness

R2 proves the Goal claim of an accepted certificate. R4 additionally binds
that exact certificate to the sealed snapshot's assumption root and requires
every explicitly named dependency to be active on the same carrier.

This kernel does not discover actual dependencies, prove dependency-extraction
completeness, process retraction, or bind a production verifier.
-/

namespace Residua.RCC.AssumptionRelativeSoundness

open Residua.RCC
open Residua.RCC.FacetSnapshot

universe u

/-- The root, dependency, and semantic interpretation of one Goal contract. -/
structure AssumptionRelativeGoalKernel
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    (projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle)
    (goal : GoalContract.{u, u}) where
  Assumption : Type u
  historyAt : Carrier → goal.History
  certificateRoot : goal.Certificate → AssumptionRoot
  certificateDependencies : goal.Certificate → List Assumption
  RootActiveAt : Carrier → AssumptionRoot → Prop
  AssumptionActiveAt : Carrier → AssumptionRoot → Assumption → Prop
  ClaimUnder : AssumptionRoot → goal.History → Prop
  claimExact :
    ∀ carrier,
      goal.claim (historyAt carrier) ↔
        ClaimUnder (projection.assumptionRoot carrier) (historyAt carrier)

/--
The exact accepted certificate is bound to the current sealed root, whose
root and every certificate-declared dependency are active.
-/
structure AssumptionRelativeCertificateBindingAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {goal : GoalContract.{u, u}}
    (K : AssumptionRelativeGoalKernel projection goal)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    {verifier : SoundGoalVerifier goal}
    (accepted :
      AcceptedGoalCertificate goal verifier (K.historyAt carrier.value)) :
    Prop where
  certificateRootBound :
    K.certificateRoot accepted.certificate =
      snapshot.coordinates.assumptionRoot
  rootActive :
    K.RootActiveAt carrier.value snapshot.coordinates.assumptionRoot
  dependenciesActive :
    ∀ assumption,
      assumption ∈ K.certificateDependencies accepted.certificate →
        K.AssumptionActiveAt
          carrier.value snapshot.coordinates.assumptionRoot assumption

/-- The proof-carrying semantic judgment produced by the R4 bridge. -/
structure AssumptionRelativeJudgmentAt
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {goal : GoalContract.{u, u}}
    (K : AssumptionRelativeGoalKernel projection goal)
    (snapshot : SealedSnapshot sealSpec)
    (carrier : SnapshotCarrier projection snapshot)
    {verifier : SoundGoalVerifier goal}
    (accepted :
      AcceptedGoalCertificate goal verifier (K.historyAt carrier.value)) :
    Prop where
  certificateRootBound :
    K.certificateRoot accepted.certificate =
      snapshot.coordinates.assumptionRoot
  rootActive :
    K.RootActiveAt carrier.value snapshot.coordinates.assumptionRoot
  dependenciesActive :
    ∀ assumption,
      assumption ∈ K.certificateDependencies accepted.certificate →
        K.AssumptionActiveAt
          carrier.value snapshot.coordinates.assumptionRoot assumption
  claim :
    K.ClaimUnder
      snapshot.coordinates.assumptionRoot
      (K.historyAt carrier.value)

/--
R4 headline: R2 soundness plus exact active-root/dependency binding yields the
claim indexed by the sealed assumption root.
-/
theorem AssumptionRelativeCertificateBindingAt.sound
    {Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
      FailureModel ProposalWindow ImplementationBundle : Type u}
    {sealSpec :
      SnapshotSeal
        Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow FailureModel
          ProposalWindow ImplementationBundle}
    {projection :
      CarrierProjection
        Carrier Epoch HistoryHead AssumptionRoot AddressRegistry SourceWindow
          FailureModel ProposalWindow ImplementationBundle}
    {goal : GoalContract.{u, u}}
    {K : AssumptionRelativeGoalKernel projection goal}
    {snapshot : SealedSnapshot sealSpec}
    {carrier : SnapshotCarrier projection snapshot}
    {verifier : SoundGoalVerifier goal}
    {accepted :
      AcceptedGoalCertificate goal verifier (K.historyAt carrier.value)}
    (binding :
      AssumptionRelativeCertificateBindingAt K snapshot carrier accepted) :
    AssumptionRelativeJudgmentAt K snapshot carrier accepted := by
  refine
    { certificateRootBound := binding.certificateRootBound
      rootActive := binding.rootActive
      dependenciesActive := binding.dependenciesActive
      claim := ?_ }
  rw [← carrier.assumptionRootBound]
  exact (K.claimExact carrier.value).mp accepted.sound

end Residua.RCC.AssumptionRelativeSoundness

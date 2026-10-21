import RCC.GlobalInvariant
import RCCTests.GlobalSerializability

/-!
# RCC-51 Global-Invariant Countermodels

The positive fixture uses two actual RCC-42/RCC-45 finalized events, seals
their RCC-48 invariant footprints, orders them in one RCC-49 global history,
and derives the declared global intent.

The load-bearing mutants show that:

* a mandatory invariant coordinate cannot be omitted from its sealed universe;
* a step touching an omitted invariant cannot enter the checked execution;
* a partition-local serial history cannot bind the complete finalized cut; and
* the caller predicate `True` cannot imply a stronger declared intent.
-/

namespace Residua.RCC.GlobalInvariant.Tests

open Residua.RCC.AuthorizationFinality
open Residua.RCC.ConflictSerializability
open Residua.RCC.FinalizedHeadWindow
open Residua.RCC.GlobalInvariant
open Residua.RCC.GlobalSerializability
open Residua.RCC.TransactionFootprint
open Residua.RCC.GlobalSerializability.Tests
open Residua.RCC.GlobalSerializability.Tests.Concrete

def invariantSurface :
    TransactionSurface
      Head Slot Head Judgment OperationId
        ReadDomain WriteDomain EffectDomain InvariantDomain :=
  { concreteSurface with
    InvariantDomains := fun _ _ domain => domain = .balance }

def singletonUniverse {Domain : Type}
    (coordinate : Domain) :
    SealedDomainUniverse Domain where
  InUniverse := fun domain => domain = coordinate
  coordinates := [coordinate]
  coverage := {
    sound := by
      intro domain member
      simpa using member
    complete := by
      intro domain inUniverse
      simp [inUniverse]
  }

def emptyUniverse (Domain : Type) :
    SealedDomainUniverse Domain where
  InUniverse := fun _ => False
  coordinates := []
  coverage := {
    sound := by
      intro _ impossible
      cases impossible
    complete := by
      intro _ impossible
      cases impossible
  }

def transactionUniverses :
    TransactionUniverses
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := singletonUniverse .source
  writes := singletonUniverse .target
  effects := singletonUniverse .store
  invariantDomains := singletonUniverse .balance

def invariantFootprint :
    TransactionFootprint
      ReadDomain WriteDomain EffectDomain InvariantDomain where
  reads := []
  writes := []
  effects := []
  invariantDomains := [.balance]

def transactionFootprintSeal (state : Head) (event : EventQ) :
    UniverseCompleteFootprint
      invariantSurface state (proposalOf event)
        transactionUniverses invariantFootprint where
  reads := {
    semanticInUniverse := by
      intro _ impossible
      cases impossible
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro _ _
      constructor <;> intro impossible <;> cases impossible
  }
  writes := {
    semanticInUniverse := by
      intro _ impossible
      cases impossible
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro _ _
      constructor <;> intro impossible <;> cases impossible
  }
  effects := {
    semanticInUniverse := by
      intro _ impossible
      cases impossible
    claimedCovered := by
      intro _ impossible
      cases impossible
    classifiedAtCoordinate := by
      intro _ _
      constructor <;> intro impossible <;> cases impossible
  }
  invariantDomains := {
    semanticInUniverse := by
      intro _ semantic
      exact semantic
    claimedCovered := by
      intro _ claimed
      exact claimed
    classifiedAtCoordinate := by
      intro domain _
      simp [invariantFootprint, invariantSurface]
  }

def certifiedStep (event : EventQ) :
    CertifiedFinalizedStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      invariantSurface (parentOf event) where
  finalized := finalizedEvent event
  footprint := invariantFootprint
  footprintComplete := (transactionFootprintSeal (parentOf event) event).toCompleteFootprint
  basis := by
    cases event <;>
      exact {
        basisRootBound := rfl
        postRootBound := rfl
      }

def sealedStep (event : EventQ) :
    RCC48CertifiedStep
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      (history := finalizedHistory)
      (ConfigLawful := configLawful)
      invariantSurface (parentOf event) where
  step := certifiedStep event
  universes := transactionUniverses
  footprintSeal := transactionFootprintSeal (parentOf event) event

def Mandatory (domain : InvariantDomain) : Prop :=
  domain = .balance

def Claim (_domain : InvariantDomain) (state : Head) : Prop :=
  state = .root0 ∨ state = .afterSet ∨ state = .setThenIncrement

def GlobalIntent (state : Head) : Prop :=
  state = .root0 ∨ state = .afterSet ∨ state = .setThenIncrement

def mandatoryUniverse : SealedDomainUniverse InvariantDomain :=
  singletonUniverse .balance

def mandatoryBinding :
    MandatoryInvariantUniverse mandatoryUniverse Mandatory where
  exact := by
    intro domain
    rfl

def intentContract :
    InvariantIntentContract Mandatory Claim GlobalIntent where
  mandatoryClaimsSuffice := by
    intro state claims
    exact claims .balance rfl

def checkedExecution :
    InvariantPreservingExecution
      AuthorityEvidence Generation Epoch EffectSlot FailureName
      invariantSurface finalizedHistory configLawful mandatoryUniverse Claim
      Head.root0 [Occurrence.setAtRoot0, Occurrence.incrementAfterSet]
        Head.setThenIncrement :=
  InvariantPreservingExecution.cons (sealedStep .setAtRoot0)
    (by
      intro domain footprintMember
      exact footprintMember)
    (by
      intro _domain _enumerated _initial
      exact Or.inr (Or.inl rfl))
    (InvariantPreservingExecution.cons (sealedStep .incrementAfterSet)
      (by
        intro domain footprintMember
        exact footprintMember)
      (by
        intro _domain _enumerated _afterSet
        exact Or.inr (Or.inr rfl))
      (InvariantPreservingExecution.nil _)
      (by decide))
    (by decide)

abbrev ConcreteFinalizedEvent :=
  FinalizedEvent
    (Judgment := Judgment)
    (AuthorityEvidence := AuthorityEvidence)
    (Generation := Generation)
    (Epoch := Epoch)
    (EffectSlot := EffectSlot)
    (OccurrenceId := Occurrence)
    (FailureName := FailureName)
    finalizedHistory configLawful

def firstEvent : ConcreteFinalizedEvent :=
  finalizedEvent .setAtRoot0

def secondEvent : ConcreteFinalizedEvent :=
  finalizedEvent .incrementAfterSet

def globalEventUniverse :
    FinalizedEventUniverse ConcreteFinalizedEvent where
  InUniverse := fun event => event = firstEvent ∨ event = secondEvent
  enumeration := [firstEvent, secondEvent]
  sound := by
    intro event member
    cases member with
    | head => exact Or.inl rfl
    | tail _ member =>
        cases member with
        | head => exact Or.inr rfl
        | tail _ impossible => cases impossible
  complete := by
    intro event included
    cases included with
    | inl first =>
        cases first
        exact List.Mem.head _
    | inr second =>
        cases second
        exact List.Mem.tail _ (List.Mem.head _)

def globalSerial :
    ConflictSerializableHistory
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      invariantSurface finalizedHistory configLawful .root0 where
  eventUniverse := globalEventUniverse
  occurrences := [.setAtRoot0, .incrementAfterSet]
  finalState := .setThenIncrement
  execution := checkedExecution.toSerialExecution
  enumeratedOccurrenceComplete := by
    intro event member
    cases member with
    | head => exact List.Mem.head _
    | tail _ member =>
        cases member with
        | head => exact List.Mem.tail _ (List.Mem.head _)
        | tail _ impossible => cases impossible
  occurrenceSound := by
    intro occurrence member
    cases member with
    | head => exact ⟨firstEvent, Or.inl rfl, rfl⟩
    | tail _ member =>
        cases member with
        | head => exact ⟨secondEvent, Or.inr rfl, rfl⟩
        | tail _ impossible => cases impossible
  occurrenceFaithful := by
    intro left right leftIncluded rightIncluded sameOccurrence
    rcases leftIncluded with leftFirst | leftSecond
    · rcases rightIncluded with rightFirst | rightSecond
      · cases leftFirst
        cases rightFirst
        rfl
      · cases leftFirst
        cases rightSecond
        cases sameOccurrence
    · rcases rightIncluded with rightFirst | rightSecond
      · cases leftSecond
        cases rightFirst
        cases sameOccurrence
      · cases leftSecond
        cases rightSecond
        rfl

def globalCut : SealedDomainUniverse ConcreteFinalizedEvent where
  InUniverse := globalEventUniverse.InUniverse
  coordinates := globalEventUniverse.enumeration
  coverage := {
    sound := globalEventUniverse.sound
    complete := globalEventUniverse.complete
  }

def globalCutBinding : FinalizedCutBinding globalSerial globalCut where
  exact := by
    intro event
    rfl

def globalInvariantCertificate :
    GlobalInvariantCertificate
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      invariantSurface finalizedHistory configLawful Head.root0
        Mandatory Claim GlobalIntent where
  serial := globalSerial
  finalizedCut := globalCut
  cutBinding := globalCutBinding
  mandatoryUniverse := mandatoryUniverse
  mandatoryBinding := mandatoryBinding
  intent := intentContract
  checkedExecution := checkedExecution
  executionBound := rfl
  initialClaims := by
    intro _domain _enumerated
    exact Or.inl rfl

theorem actual_global_finalized_cut_satisfies_intent :
    GlobalIntent globalSerial.finalState :=
  global_finalized_cut_satisfies_intent globalInvariantCertificate

theorem actual_certificate_consumes_rcc48_and_rcc49 :
    globalInvariantCertificate.checkedExecution.toSerialExecution =
        globalInvariantCertificate.serial.execution ∧
      globalInvariantCertificate.serial.eventUniverse.InUniverse firstEvent := by
  have cutIn :
      globalInvariantCertificate.finalizedCut.InUniverse firstEvent :=
    Or.inl rfl
  exact
    ⟨globalInvariantCertificate.executionBound,
      (globalInvariantCertificate.cutBinding.exact firstEvent).mpr cutIn⟩

/-! ## Missing mandatory invariant coordinate -/

theorem empty_universe_cannot_represent_mandatory_invariant :
    ¬ Nonempty
      (MandatoryInvariantUniverse
        (emptyUniverse InvariantDomain) Mandatory) := by
  rintro ⟨binding⟩
  exact (binding.exact .balance).mpr rfl

theorem step_touching_omitted_invariant_cannot_enter_checked_execution :
    ¬ Nonempty
      (InvariantPreservingExecution
        AuthorityEvidence Generation Epoch EffectSlot FailureName
        invariantSurface finalizedHistory configLawful
          (emptyUniverse InvariantDomain) Claim
        Head.root0 [Occurrence.setAtRoot0] Head.afterSet) := by
  rintro ⟨execution⟩
  obtain ⟨step, _occurrenceBound, footprintMandatory⟩ :=
    execution.headFootprintMandatory
  have semanticMember :
      InvariantDomain.balance ∈ step.step.footprint.invariantDomains :=
    semantic_invariant_is_in_footprint step.footprintSeal rfl
  have impossible :
      InvariantDomain.balance ∈
        (emptyUniverse InvariantDomain).coordinates :=
    footprintMandatory .balance semanticMember
  simp [emptyUniverse] at impossible

/-! ## Partition-local history cannot stand for the finalized cut -/

def localCheckedExecution :
    InvariantPreservingExecution
      AuthorityEvidence Generation Epoch EffectSlot FailureName
      invariantSurface finalizedHistory configLawful mandatoryUniverse Claim
      Head.root0 [Occurrence.setAtRoot0] Head.afterSet :=
  InvariantPreservingExecution.cons (sealedStep .setAtRoot0)
    (by
      intro domain footprintMember
      exact footprintMember)
    (by
      intro _domain _enumerated _initial
      exact Or.inr (Or.inl rfl))
    (InvariantPreservingExecution.nil _)
    (by decide)

def localEventUniverse :
    FinalizedEventUniverse ConcreteFinalizedEvent where
  InUniverse := fun event => event = firstEvent
  enumeration := [firstEvent]
  sound := by
    intro event member
    cases member with
    | head => rfl
    | tail _ impossible => cases impossible
  complete := by
    intro event included
    cases included
    exact List.Mem.head _

def localSerial :
    ConflictSerializableHistory
      (AuthorityEvidence := AuthorityEvidence)
      (Generation := Generation)
      (Epoch := Epoch)
      (EffectSlot := EffectSlot)
      (OccurrenceId := Occurrence)
      (FailureName := FailureName)
      invariantSurface finalizedHistory configLawful .root0 where
  eventUniverse := localEventUniverse
  occurrences := [.setAtRoot0]
  finalState := .afterSet
  execution := localCheckedExecution.toSerialExecution
  enumeratedOccurrenceComplete := by
    intro event member
    cases member with
    | head => exact List.Mem.head _
    | tail _ impossible => cases impossible
  occurrenceSound := by
    intro occurrence member
    cases member with
    | head => exact ⟨firstEvent, rfl, rfl⟩
    | tail _ impossible => cases impossible
  occurrenceFaithful := by
    intro left right leftIncluded rightIncluded _sameOccurrence
    cases leftIncluded
    cases rightIncluded
    rfl

theorem first_and_second_events_are_distinct :
    firstEvent ≠ secondEvent := by
  intro sameEvent
  have sameOccurrence :
      firstEvent.occurrenceId = secondEvent.occurrenceId :=
    congrArg (fun event : ConcreteFinalizedEvent => event.occurrenceId) sameEvent
  exact (by decide :
    Occurrence.setAtRoot0 ≠ Occurrence.incrementAfterSet) sameOccurrence

theorem partition_local_history_cannot_bind_global_finalized_cut :
    ¬ Nonempty (FinalizedCutBinding localSerial globalCut) := by
  rintro ⟨binding⟩
  have locallyIncluded :
      localSerial.eventUniverse.InUniverse secondEvent :=
    (binding.exact secondEvent).mpr (Or.inr rfl)
  exact first_and_second_events_are_distinct locallyIncluded.symm

/-! ## Caller `True` is not the declared global intent -/

def AlwaysTrueClaim (_ : InvariantDomain) (_ : Head) : Prop :=
  True

def StrictIntent (state : Head) : Prop :=
  state = .setThenIncrement

theorem caller_true_invariant_cannot_prove_strict_intent :
    ¬ Nonempty
      (InvariantIntentContract Mandatory AlwaysTrueClaim StrictIntent) := by
  rintro ⟨contract⟩
  have rootWouldSatisfyStrictIntent : Head.root0 = .setThenIncrement :=
    contract.mandatoryClaimsSuffice .root0
      (by
        intro _domain _mandatory
        exact True.intro)
  exact Head.noConfusion rootWouldSatisfyStrictIntent

#print axioms InvariantPreservingExecution.toSerialExecution
#print axioms InvariantPreservingExecution.preservesAllEnumerated
#print axioms global_finalized_cut_satisfies_intent
#print axioms actual_global_finalized_cut_satisfies_intent
#print axioms empty_universe_cannot_represent_mandatory_invariant
#print axioms step_touching_omitted_invariant_cannot_enter_checked_execution
#print axioms partition_local_history_cannot_bind_global_finalized_cut
#print axioms caller_true_invariant_cannot_prove_strict_intent

end Residua.RCC.GlobalInvariant.Tests

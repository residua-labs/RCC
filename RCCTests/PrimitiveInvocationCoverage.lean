import RCC.PrimitiveInvocationCoverage

namespace Residua.RCC.PrimitiveInvocationCoverage.Tests

open Residua.RCC
open Residua.RCC.ClosurePrerequisites
open Residua.RCC.FacetCoherence

inductive Invocation
  | good
  | bad
  deriving DecidableEq, Repr

def exhausted : ResourceContract where
  fuel := 0
  deadlineTicks := 0
  searchBound := 0
  processTimeoutTicks := 0
  leaseTicks := 0

def policy : ResourcePolicy where
  insufficient := fun _ _ => True
  fullyExhaustedInsufficient := by
    intro primitive contract fullyExhausted
    trivial

def family : PrimitiveFamily where
  Input := fun _ => Unit
  Output := fun _ => Unit
  Wake := Unit
  Residue := Unit
  observe := fun _ _ _ => .ResourceLimit ()

def familyLawful : LawfulPrimitiveFamily policy family where
  resourceBound := by
    intro primitive contract input insufficient
    exact ⟨(), rfl⟩

def actualInvocation : ActualPrimitiveInvocation family where
  primitive := .SourceScan
  contract := exhausted
  input := ()
  observed := .ResourceLimit ()
  result := .ResourceExhausted ()

def actualRefinement : ActualInvocationRefinementAt family where
  invocation := actualInvocation
  observationExact := rfl
  resultExact := rfl

def worldWith
    (runtime : Nat → Nat → Prop) : CoherenceWorld where
  State := Nat
  Address := Nat
  stateEquivalent := Eq
  stateAddress := id
  reduces := fun _ _ => True
  Evidence := Unit
  AdmittedEvent := Unit
  grounded := fun _ => True
  admits := fun _ _ => True
  ResourceToken := Unit
  activeResources := fun _ => []
  Verifier := Unit
  Artifact := Unit
  verifierLevel := fun _ => 1
  artifactLevel := fun _ => 0
  verifies := fun _ _ => True
  migrates := fun _ _ => False
  terminalAt := fun _ _ => True
  carries := fun _ _ => True
  RuntimeState := Nat
  runtimeStep := runtime
  abstractState := id
  Component := Unit
  Seam := Unit
  components := []
  seams := []
  componentClosed := fun _ => True
  seamExact := fun _ => True
  globalClosed := True

def allRuntime (before after : Nat) : Prop :=
  after = before + 1

def onlyGoodRuntime (before after : Nat) : Prop :=
  before = 0 ∧ after = 1

def emptyRuntime (_before _after : Nat) : Prop :=
  False

def allRuntimeWorld : CoherenceWorld :=
  worldWith allRuntime

def onlyGoodRuntimeWorld : CoherenceWorld :=
  worldWith onlyGoodRuntime

def emptyRuntimeWorld : CoherenceWorld :=
  worldWith emptyRuntime

def beforeAt : Invocation → Nat
  | .good => 0
  | .bad => 1

def afterAt : Invocation → Nat
  | .good => 1
  | .bad => 2

def systemWith
    (runtime : Nat → Nat → Prop)
    (declared : List Invocation) : PrimitiveInvocationSystem where
  Snapshot := Unit
  Invocation := Invocation
  invocationDecidableEq := inferInstance
  inScopeAt := fun _ _ => True
  invocationsAt := fun _ => declared
  policyAt := fun _ => policy
  familyAt := fun _ => family
  lawfulAt := fun _ => familyLawful
  actualAt := fun _ _ => actualInvocation
  worldAt := fun _ => worldWith runtime
  runtimeBeforeAt := fun _ invocation => beforeAt invocation
  runtimeAfterAt := fun _ invocation => afterAt invocation
  MeasurementReceipt := Unit
  measuredReceiptAt := fun _ _ => none
  MeasurementBindsAt := fun _ _ _ => False

def fullSystem : PrimitiveInvocationSystem :=
  systemWith allRuntime [.good, .bad]

def onlyGoodRuntimeSystem : PrimitiveInvocationSystem :=
  systemWith onlyGoodRuntime [.good, .bad]

def vacuousRuntimeSystem : PrimitiveInvocationSystem :=
  systemWith emptyRuntime [.good, .bad]

def underdeclaredSystem : PrimitiveInvocationSystem :=
  systemWith allRuntime [.good]

def fullUniverseSeal : InvocationUniverseSeal fullSystem () where
  inScopeExists := ⟨.good, trivial⟩
  sound := by
    intro invocation member
    trivial
  complete := by
    intro invocation inScope
    cases invocation with
    | good => exact List.Mem.head [Invocation.bad]
    | bad => exact List.Mem.tail Invocation.good (List.Mem.head [])

def fullPacket
    (invocation : Invocation) :
    ActualInvocationPacketAt fullSystem () invocation where
  refinement := actualRefinement
  invocationExact := rfl
  runtimeBound := by
    cases invocation <;> rfl
  formalOrMeasured := .formalStep trivial

def fullEvidence : InvocationEvidenceWindowAt fullSystem () where
  packetAt := fun invocation => some (fullPacket invocation)

def fullCoverage :
    ExhaustiveInvocationCoverageAt fullSystem () fullEvidence where
  universeSeal := fullUniverseSeal
  packetComplete := by
    intro invocation inScope
    exact ⟨fullPacket invocation, rfl⟩

theorem positive_every_actual_is_total_refined_runtime_bound
    (invocation : Invocation) :
    ∃ refinement : ActualInvocationRefinementAt family,
      refinement.invocation = actualInvocation ∧
      InvocationReturned refinement.invocation ∧
      allRuntimeWorld.runtimeStep (beforeAt invocation) (afterAt invocation) ∧
      Nonempty (FormalOrMeasuredAt fullSystem () invocation) := by
  exact
    fullCoverage.all_total_refined_runtime_bound invocation trivial

/-! ## Load-bearing mutants -/

def oneGoodOnlyEvidence :
    InvocationEvidenceWindowAt fullSystem () where
  packetAt := fun
    | .good => some (fullPacket .good)
    | .bad => none

theorem one_good_hides_bad_second :
    ¬ Nonempty
      (ExhaustiveInvocationCoverageAt
        fullSystem () oneGoodOnlyEvidence) := by
  rintro ⟨coverage⟩
  rcases coverage.packetComplete .bad trivial with
    ⟨packet, found⟩
  cases found

theorem actual_not_runtimeStep :
    ¬ Nonempty
      (ActualInvocationPacketAt onlyGoodRuntimeSystem () .bad) := by
  rintro ⟨packet⟩
  have bound := packet.runtimeBound
  exact nomatch bound.1

theorem vacuous_runtime_relation :
    ¬ Nonempty
      (ActualInvocationPacketAt vacuousRuntimeSystem () .good) := by
  rintro ⟨packet⟩
  exact packet.runtimeBound

theorem underdeclared_universe :
    ¬ InvocationUniverseSeal underdeclaredSystem () := by
  intro sealProof
  have badDeclared := sealProof.complete .bad trivial
  exact nomatch badDeclared

end Residua.RCC.PrimitiveInvocationCoverage.Tests

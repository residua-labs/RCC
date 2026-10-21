import RCC.SeamExactness

namespace Residua.RCC.SeamExactness.Tests

open Residua.RCC.SeamExactness

namespace Identity

inductive Owner
  | writer
  deriving DecidableEq, Repr

def address (value : Bool) :
    SeamAddress Unit Unit Unit Bool Bool where
  kind := ()
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def world : SeamWorld where
  SourceOutput := Bool
  TargetInput := Bool
  sourceEquivalent := Eq
  targetEquivalent := Eq
  targetInScope := fun _ => True
  encode := id
  Snapshot := Nat
  sourceSnapshot := 11
  targetSnapshot := 11
  HistoryHead := Nat
  sourceHead := 13
  targetHead := 13
  SourceWindow := Nat
  sourceWindow := 17
  targetWindow := 17
  AssumptionRoot := Nat
  sourceAssumptionRoot := 19
  targetAssumptionRoot := 19
  AddressKind := Unit
  AddressDomain := Unit
  AddressSchema := Unit
  CanonicalBytes := Bool
  Digest := Bool
  sourceAddress := address
  targetAddress := address
  EffectSlot := Unit
  EffectOwner := Owner
  sourceMayWrite := fun _ owner => owner = .writer
  targetMayWrite := fun _ owner => owner = .writer

def exactSeam : ExactSeamAt world where
  sourceEquivalentRefl := fun source => rfl
  sourceEquivalentSymm := Eq.symm
  sourceEquivalentTrans := Eq.trans
  targetEquivalentRefl := fun target => rfl
  targetEquivalentSymm := Eq.symm
  targetEquivalentTrans := Eq.trans
  bindingSound := fun equivalent => equivalent
  bindingPrecise := fun equivalent => equivalent
  targetCovered := by
    intro target inScope
    exact ⟨target, rfl⟩
  sourceAddressSound := by
    intro left right sameAddress
    exact congrArg SeamAddress.canonicalBytes sameAddress
  targetAddressSound := by
    intro left right sameAddress
    exact congrArg SeamAddress.canonicalBytes sameAddress
  addressCompatible := fun source => rfl
  snapshotAgreement := rfl
  historyHeadAgreement := rfl
  sourceWindowAgreement := rfl
  assumptionRootAgreement := rfl
  effectOwnerCoherent := by
    intro slot sourceOwner targetOwner sourceAuthority targetAuthority
    exact sourceAuthority.trans targetAuthority.symm

end Identity

theorem identity_seam_is_semantically_exact
    (left right : Bool) :
    Identity.world.targetEquivalent
        (Identity.world.encode left)
        (Identity.world.encode right) ↔
      Identity.world.sourceEquivalent left right :=
  Identity.exactSeam.bindingExact

namespace Collapse

def addressSource (value : Bool) :
    SeamAddress Unit Unit Unit Bool Bool where
  kind := ()
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def addressTarget (value : Bool) :
    SeamAddress Unit Unit Unit Bool Bool where
  kind := ()
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def world : SeamWorld where
  SourceOutput := Bool
  TargetInput := Bool
  sourceEquivalent := Eq
  targetEquivalent := fun _ _ => True
  targetInScope := fun _ => True
  encode := id
  Snapshot := Unit
  sourceSnapshot := ()
  targetSnapshot := ()
  HistoryHead := Unit
  sourceHead := ()
  targetHead := ()
  SourceWindow := Unit
  sourceWindow := ()
  targetWindow := ()
  AssumptionRoot := Unit
  sourceAssumptionRoot := ()
  targetAssumptionRoot := ()
  AddressKind := Unit
  AddressDomain := Unit
  AddressSchema := Unit
  CanonicalBytes := Bool
  Digest := Bool
  sourceAddress := addressSource
  targetAddress := addressTarget
  EffectSlot := Unit
  EffectOwner := Unit
  sourceMayWrite := fun _ _ => False
  targetMayWrite := fun _ _ => False

end Collapse

/-- A target quotient collapsing distinct source classes cannot be exact. -/
theorem collapsing_target_quotient_is_refused :
    ¬ ExactSeamAt Collapse.world := by
  intro seam
  have collapsed :
      Collapse.world.targetEquivalent
        (Collapse.world.encode true)
        (Collapse.world.encode false) :=
    trivial
  have impossible :
      Collapse.world.sourceEquivalent true false :=
    seam.bindingPrecise collapsed
  cases impossible

namespace KindMismatch

def sourceAddress (value : Bool) :
    SeamAddress Bool Unit Unit Bool Bool where
  kind := true
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def targetAddress (value : Bool) :
    SeamAddress Bool Unit Unit Bool Bool where
  kind := false
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def world : SeamWorld where
  SourceOutput := Bool
  TargetInput := Bool
  sourceEquivalent := Eq
  targetEquivalent := Eq
  targetInScope := fun _ => True
  encode := id
  Snapshot := Unit
  sourceSnapshot := ()
  targetSnapshot := ()
  HistoryHead := Unit
  sourceHead := ()
  targetHead := ()
  SourceWindow := Unit
  sourceWindow := ()
  targetWindow := ()
  AssumptionRoot := Unit
  sourceAssumptionRoot := ()
  targetAssumptionRoot := ()
  AddressKind := Bool
  AddressDomain := Unit
  AddressSchema := Unit
  CanonicalBytes := Bool
  Digest := Bool
  sourceAddress := sourceAddress
  targetAddress := targetAddress
  EffectSlot := Unit
  EffectOwner := Unit
  sourceMayWrite := fun _ _ => False
  targetMayWrite := fun _ _ => False

end KindMismatch

/-- Each endpoint address remains sound; only their address kinds disagree. -/
theorem kind_mismatch_endpoints_are_individually_address_sound :
    (∀ {left right : Bool},
      KindMismatch.world.sourceAddress left =
        KindMismatch.world.sourceAddress right →
      left = right) ∧
    (∀ {left right : Bool},
      KindMismatch.world.targetAddress left =
        KindMismatch.world.targetAddress right →
      left = right) :=
  ⟨fun sameAddress =>
      congrArg SeamAddress.canonicalBytes sameAddress,
    fun sameAddress =>
      congrArg SeamAddress.canonicalBytes sameAddress⟩

/-- A cross-kind address cannot satisfy typed seam compatibility. -/
theorem address_kind_mismatch_is_refused :
    ¬ ExactSeamAt KindMismatch.world := by
  intro seam
  have sameAddress := seam.addressCompatible true
  have sameKind := congrArg SeamAddress.kind sameAddress
  cases sameKind

namespace RootMismatch

def address (value : Bool) :
    SeamAddress Unit Unit Unit Bool Bool where
  kind := ()
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def world : SeamWorld where
  SourceOutput := Bool
  TargetInput := Bool
  sourceEquivalent := Eq
  targetEquivalent := Eq
  targetInScope := fun _ => True
  encode := id
  Snapshot := Unit
  sourceSnapshot := ()
  targetSnapshot := ()
  HistoryHead := Unit
  sourceHead := ()
  targetHead := ()
  SourceWindow := Unit
  sourceWindow := ()
  targetWindow := ()
  AssumptionRoot := Bool
  sourceAssumptionRoot := true
  targetAssumptionRoot := false
  AddressKind := Unit
  AddressDomain := Unit
  AddressSchema := Unit
  CanonicalBytes := Bool
  Digest := Bool
  sourceAddress := address
  targetAddress := address
  EffectSlot := Unit
  EffectOwner := Unit
  sourceMayWrite := fun _ _ => False
  targetMayWrite := fun _ _ => False

end RootMismatch

/-- Different active assumption roots cannot form one exact seam. -/
theorem assumption_root_mismatch_is_refused :
    ¬ ExactSeamAt RootMismatch.world := by
  intro seam
  cases seam.assumptionRootAgreement

namespace DualOwner

inductive Owner
  | source
  | target
  deriving DecidableEq, Repr

def address (value : Bool) :
    SeamAddress Unit Unit Unit Bool Bool where
  kind := ()
  domain := ()
  schema := ()
  canonicalBytes := value
  digest := value

def world : SeamWorld where
  SourceOutput := Bool
  TargetInput := Bool
  sourceEquivalent := Eq
  targetEquivalent := Eq
  targetInScope := fun _ => True
  encode := id
  Snapshot := Unit
  sourceSnapshot := ()
  targetSnapshot := ()
  HistoryHead := Unit
  sourceHead := ()
  targetHead := ()
  SourceWindow := Unit
  sourceWindow := ()
  targetWindow := ()
  AssumptionRoot := Unit
  sourceAssumptionRoot := ()
  targetAssumptionRoot := ()
  AddressKind := Unit
  AddressDomain := Unit
  AddressSchema := Unit
  CanonicalBytes := Bool
  Digest := Bool
  sourceAddress := address
  targetAddress := address
  EffectSlot := Unit
  EffectOwner := Owner
  sourceMayWrite := fun _ owner => owner = .source
  targetMayWrite := fun _ owner => owner = .target

end DualOwner

/-- Two distinct writers for one shared effect slot refuse seam exactness. -/
theorem dual_effect_owner_is_refused :
    ¬ ExactSeamAt DualOwner.world := by
  intro seam
  have sameOwner :
      DualOwner.Owner.source = DualOwner.Owner.target :=
    seam.effectOwnerCoherent (slot := ()) rfl rfl
  cases sameOwner

end Residua.RCC.SeamExactness.Tests

/-!
# C2 seam exactness

A seam is not exact merely because a caller supplies an opaque proposition
named `seamExact`.  C2 instead uses a concrete carrier whose fields expose the
load-bearing boundary laws:

* source equivalence is preserved and reflected by the seam encoding;
* every declared in-scope target input is represented by a source output;
* source and encoded target addresses are identical typed commitments;
* each endpoint address is sound for its declared equivalence;
* snapshot, history head, observation window, and assumption root agree; and
* two endpoints authorized for one effect slot identify the same owner.

The theorem is local to one seam.  It does not enumerate all components or
seams and does not imply global closure.  A complete C2 realization must
still bind this kernel to the component relation, active assumption
dependencies, the concrete fenced writer, and the composition seam family.
-/

namespace Residua.RCC.SeamExactness

universe u

/--
An address commitment retains its typed envelope and canonical bytes.

`digest` is carried for realization, but equality of this structure also
checks canonical bytes.  A bare digest therefore cannot establish seam
compatibility.
-/
structure SeamAddress
    (Kind Domain Schema Bytes Digest : Type u) where
  kind : Kind
  domain : Domain
  schema : Schema
  canonicalBytes : Bytes
  digest : Digest

/-- The concrete vocabulary of one directed component seam. -/
structure SeamWorld where
  SourceOutput : Type u
  TargetInput : Type u
  sourceEquivalent : SourceOutput → SourceOutput → Prop
  targetEquivalent : TargetInput → TargetInput → Prop
  targetInScope : TargetInput → Prop
  encode : SourceOutput → TargetInput

  Snapshot : Type u
  sourceSnapshot : Snapshot
  targetSnapshot : Snapshot

  HistoryHead : Type u
  sourceHead : HistoryHead
  targetHead : HistoryHead

  SourceWindow : Type u
  sourceWindow : SourceWindow
  targetWindow : SourceWindow

  AssumptionRoot : Type u
  sourceAssumptionRoot : AssumptionRoot
  targetAssumptionRoot : AssumptionRoot

  AddressKind : Type u
  AddressDomain : Type u
  AddressSchema : Type u
  CanonicalBytes : Type u
  Digest : Type u
  sourceAddress :
    SourceOutput →
      SeamAddress
        AddressKind AddressDomain AddressSchema CanonicalBytes Digest
  targetAddress :
    TargetInput →
      SeamAddress
        AddressKind AddressDomain AddressSchema CanonicalBytes Digest

  EffectSlot : Type u
  EffectOwner : Type u
  sourceMayWrite : EffectSlot → EffectOwner → Prop
  targetMayWrite : EffectSlot → EffectOwner → Prop

/--
The proof-carrying exactness certificate for one concrete seam.

`targetCovered` is scoped by `targetInScope`; a component may possess other
inputs without pretending that they cross this seam.
-/
structure SeamBoundaryExactAt (world : SeamWorld) : Prop where
  sourceEquivalentRefl :
    ∀ source,
      world.sourceEquivalent source source
  sourceEquivalentSymm :
    ∀ {left right},
      world.sourceEquivalent left right →
      world.sourceEquivalent right left
  sourceEquivalentTrans :
    ∀ {left middle right},
      world.sourceEquivalent left middle →
      world.sourceEquivalent middle right →
      world.sourceEquivalent left right

  targetEquivalentRefl :
    ∀ target,
      world.targetEquivalent target target
  targetEquivalentSymm :
    ∀ {left right},
      world.targetEquivalent left right →
      world.targetEquivalent right left
  targetEquivalentTrans :
    ∀ {left middle right},
      world.targetEquivalent left middle →
      world.targetEquivalent middle right →
      world.targetEquivalent left right

  bindingSound :
    ∀ {left right},
      world.sourceEquivalent left right →
      world.targetEquivalent (world.encode left) (world.encode right)
  bindingPrecise :
    ∀ {left right},
      world.targetEquivalent (world.encode left) (world.encode right) →
      world.sourceEquivalent left right
  targetCovered :
    ∀ target,
      world.targetInScope target →
      ∃ source,
        world.targetEquivalent target (world.encode source)

  sourceAddressSound :
    ∀ {left right},
      world.sourceAddress left = world.sourceAddress right →
      world.sourceEquivalent left right
  targetAddressSound :
    ∀ {left right},
      world.targetAddress left = world.targetAddress right →
      world.targetEquivalent left right
  addressCompatible :
    ∀ source,
      world.sourceAddress source =
        world.targetAddress (world.encode source)

  snapshotAgreement :
    world.sourceSnapshot = world.targetSnapshot
  historyHeadAgreement :
    world.sourceHead = world.targetHead
  sourceWindowAgreement :
    world.sourceWindow = world.targetWindow
  assumptionRootAgreement :
    world.sourceAssumptionRoot = world.targetAssumptionRoot

/--
Full seam exactness adds shared effect-owner coherence to the boundary laws.
The split lets a concrete fenced-writer adapter derive this final law from a
canonical writer state instead of accepting it as an opaque claim.
-/
structure ExactSeamAt
    (world : SeamWorld)
    extends SeamBoundaryExactAt world : Prop where
  effectOwnerCoherent :
    ∀ {slot sourceOwner targetOwner},
      world.sourceMayWrite slot sourceOwner →
      world.targetMayWrite slot targetOwner →
      sourceOwner = targetOwner

/-- C2 semantic headline: the seam encoding is exact on source classes. -/
theorem ExactSeamAt.bindingExact
    {world : SeamWorld}
    (seam : ExactSeamAt world)
    {left right : world.SourceOutput} :
    world.targetEquivalent (world.encode left) (world.encode right) ↔
      world.sourceEquivalent left right :=
  ⟨seam.bindingPrecise, seam.bindingSound⟩

/-- An exact seam exposes the same typed address on both endpoints. -/
theorem ExactSeamAt.encodedAddressAgrees
    {world : SeamWorld}
    (seam : ExactSeamAt world)
    (source : world.SourceOutput) :
    world.sourceAddress source =
      world.targetAddress (world.encode source) :=
  seam.addressCompatible source

/-- Shared effect authority cannot name two different owners. -/
theorem ExactSeamAt.sharedWriterUnique
    {world : SeamWorld}
    (seam : ExactSeamAt world)
    {slot : world.EffectSlot}
    {sourceOwner targetOwner : world.EffectOwner}
    (sourceAuthority : world.sourceMayWrite slot sourceOwner)
    (targetAuthority : world.targetMayWrite slot targetOwner) :
    sourceOwner = targetOwner :=
  seam.effectOwnerCoherent sourceAuthority targetAuthority

end Residua.RCC.SeamExactness

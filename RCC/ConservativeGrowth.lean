/-!
# RCC-24 Conservative Theory Growth

`TheoryGrowth` is not a generic name for every epoch change.  It preserves the
old semantic domain, transports unaffected judgments and addresses, restricts
the successor projection to the old projection, and closes the obstruction
that justified growth.  A change to old semantics is a revision, amendment, or
kernel upgrade and must not inhabit `TheoryGrowthCert`.

This is a parametric certificate kernel.  Domain instances still owe concrete
observations, judgment dependency analysis, address transport, and projection
restriction.  In particular, this layer treats `transportJudgment` and
`transportObstruction` as supplied functions; their claim/origin exactness is
a separate instance bridge.
-/

namespace Residua.RCC.ConservativeGrowth

universe u v w x y z p q r

/-- Epoch-change kinds remain distinct; only `theoryGrowth` is conservative. -/
inductive ReepochKind
  | observationAdvance
  | policyAmendment
  | kernelUpgrade
  | theoryGrowth
  | theoryRevision
  deriving DecidableEq, Repr

/--
The old and successor semantic surfaces used by the conservative-growth
certificate.
-/
structure GrowthSystem where
  OldObject : Type u
  NewObject : Type v
  Observation : Type w
  OldJudgment : Type x
  NewJudgment : Type y
  Address : Type z
  OldProjection : Type p
  NewProjection : Type q
  Obstruction : Type r
  embed : OldObject → NewObject
  embedInjective :
    ∀ ⦃left right⦄, embed left = embed right → left = right
  oldObserve : OldObject → Observation
  newObserve : NewObject → Observation
  transportJudgment : OldJudgment → NewJudgment
  oldValid : OldJudgment → Prop
  newValid : NewJudgment → Prop
  dependsOnChangedRoot : OldJudgment → Prop
  oldAddress : OldObject → Address
  newAddress : NewObject → Address
  addressMigrationValid : (old : OldObject) → Address → Address → Prop
  oldProjection : OldProjection
  newProjection : NewProjection
  restrictProjection : NewProjection → OldProjection
  transportObstruction : Obstruction → Obstruction
  unresolvedOld : Obstruction → Prop
  unresolvedNew : Obstruction → Prop

/--
An explicit old-to-new address migration.  Equality is not required, but both
ends and the transported old object are pinned.
-/
structure AddressMigration (S : GrowthSystem) (old : S.OldObject) where
  oldAddress : S.Address
  newAddress : S.Address
  oldAddressPinned : oldAddress = S.oldAddress old
  newAddressPinned : newAddress = S.newAddress (S.embed old)
  valid : S.addressMigrationValid old oldAddress newAddress

/-- Every old object either keeps its address or carries explicit transport. -/
inductive AddressTransport (S : GrowthSystem) (old : S.OldObject) : Prop
  | unchanged :
      S.newAddress (S.embed old) = S.oldAddress old →
      AddressTransport S old
  | migrated : AddressMigration S old → AddressTransport S old

/--
Proof-carrying conservative growth.  The triggering obstruction is indexed so
the post-growth closure cannot silently target an unrelated obstruction.
-/
structure TheoryGrowthCert (S : GrowthSystem) (trigger : S.Obstruction) : Prop where
  semanticConservative :
    ∀ old, S.newObserve (S.embed old) = S.oldObserve old
  judgmentTransport :
    ∀ judgment,
      ¬ S.dependsOnChangedRoot judgment →
      S.oldValid judgment →
      S.newValid (S.transportJudgment judgment)
  addressTransport :
    ∀ old, AddressTransport S old
  projectionRestriction :
    S.restrictProjection S.newProjection = S.oldProjection
  obstructionWasUnresolved :
    S.unresolvedOld trigger
  obstructionClosed :
    ¬ S.unresolvedNew (S.transportObstruction trigger)

/-- The kind carried by a conservative-growth certificate is definitionally fixed. -/
def GrowthKind {S : GrowthSystem} {trigger : S.Obstruction}
    (_ : TheoryGrowthCert S trigger) : ReepochKind :=
  .theoryGrowth

/-- A raw migration proposal, before the appropriate certificate is supplied. -/
structure GrowthProposal (S : GrowthSystem) (trigger : S.Obstruction) where
  kind : ReepochKind

/-- A raw label check.  This alone never admits growth. -/
def HasTheoryGrowthLabel {S : GrowthSystem} {trigger : S.Obstruction}
    (proposal : GrowthProposal S trigger) : Prop :=
  proposal.kind = .theoryGrowth

/--
The admission boundary pairs the exact growth label with the conservative
certificate.  A caller cannot promote a raw `theoryGrowth` tag without the
proof-carrying semantic obligations.
-/
structure AdmittedTheoryGrowth (S : GrowthSystem) (trigger : S.Obstruction) where
  proposal : GrowthProposal S trigger
  kindExact : HasTheoryGrowthLabel proposal
  certificate : TheoryGrowthCert S trigger

theorem theory_growth_preserves_old_semantics
    {S : GrowthSystem} {trigger : S.Obstruction}
    (cert : TheoryGrowthCert S trigger) :
    ∀ old, S.newObserve (S.embed old) = S.oldObserve old :=
  cert.semanticConservative

theorem theory_growth_transports_unaffected_judgment
    {S : GrowthSystem} {trigger : S.Obstruction}
    (cert : TheoryGrowthCert S trigger)
    (judgment : S.OldJudgment)
    (independent : ¬ S.dependsOnChangedRoot judgment)
    (valid : S.oldValid judgment) :
    S.newValid (S.transportJudgment judgment) :=
  cert.judgmentTransport judgment independent valid

theorem theory_growth_preserves_projection
    {S : GrowthSystem} {trigger : S.Obstruction}
    (cert : TheoryGrowthCert S trigger) :
    S.restrictProjection S.newProjection = S.oldProjection :=
  cert.projectionRestriction

theorem theory_growth_closes_obstruction
    {S : GrowthSystem} {trigger : S.Obstruction}
    (cert : TheoryGrowthCert S trigger) :
    S.unresolvedOld trigger ∧
      ¬ S.unresolvedNew (S.transportObstruction trigger) :=
  ⟨cert.obstructionWasUnresolved, cert.obstructionClosed⟩

/--
RCC-24 headline: admitted theory growth has the exact growth label, preserves
every old observation, applies the supplied transport to every unaffected
valid judgment and every old address, restricts to the old projection, and
closes the supplied transported obstruction.
-/
theorem AdmittedTheoryGrowth.sound
    {S : GrowthSystem} {trigger : S.Obstruction}
    (admitted : AdmittedTheoryGrowth S trigger) :
    admitted.proposal.kind = .theoryGrowth ∧
      (∀ old, S.newObserve (S.embed old) = S.oldObserve old) ∧
      (∀ judgment,
        ¬ S.dependsOnChangedRoot judgment →
        S.oldValid judgment →
        S.newValid (S.transportJudgment judgment)) ∧
      (∀ old, AddressTransport S old) ∧
      S.restrictProjection S.newProjection = S.oldProjection ∧
      S.unresolvedOld trigger ∧
      ¬ S.unresolvedNew (S.transportObstruction trigger) :=
  ⟨admitted.kindExact,
    admitted.certificate.semanticConservative,
    admitted.certificate.judgmentTransport,
    admitted.certificate.addressTransport,
    admitted.certificate.projectionRestriction,
    admitted.certificate.obstructionWasUnresolved,
    admitted.certificate.obstructionClosed⟩

/--
If an old observation changes under the embedding, no conservative-growth
certificate exists for that same system and trigger.
-/
theorem old_semantic_change_is_not_growth
    {S : GrowthSystem} {trigger : S.Obstruction}
    (old : S.OldObject)
    (changed : S.newObserve (S.embed old) ≠ S.oldObserve old) :
    ¬ TheoryGrowthCert S trigger := by
  intro cert
  exact changed (cert.semanticConservative old)

theorem old_semantic_change_is_not_admitted_growth
    {S : GrowthSystem} {trigger : S.Obstruction}
    (old : S.OldObject)
    (changed : S.newObserve (S.embed old) ≠ S.oldObserve old) :
    AdmittedTheoryGrowth S trigger → False := by
  intro admitted
  exact old_semantic_change_is_not_growth old changed admitted.certificate

/--
Failure to restrict the successor projection likewise rules out conservative
growth.
-/
theorem projection_change_is_not_growth
    {S : GrowthSystem} {trigger : S.Obstruction}
    (changed : S.restrictProjection S.newProjection ≠ S.oldProjection) :
    ¬ TheoryGrowthCert S trigger := by
  intro cert
  exact changed cert.projectionRestriction

end Residua.RCC.ConservativeGrowth


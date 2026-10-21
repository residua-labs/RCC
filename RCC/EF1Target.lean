import RCC.EffectClassification

/-!
# EF-1 candidate: effects are classified into exactly one of five classes

EF-1's obligation is that every effect is classified as exactly one of
`Pure`, `PrepareCommit`, `ExactlyReversible`, `Compensatable`, or
`Irreversible`, with no priority order silently choosing among overlapping
claims.

The content lives in the Prelude module
`RCC.EffectClassification` (proved for independent reasons):
the proof-carrying `CertifiedEffectClass` with per-constructor exclusions
(`selected`, `excludes`), the total mechanical classifier `deriveEffectClass`
with named refusals, and the coverage theorem
`effect_classification_exact_of_coverage`.  This Target only connects that
content to the obligation: the parametric laws are restated as certificate
fields by import; non-vacuity is pinned on a finite five-effect fixture that
derives one exclusive classification; and the two refusal modes are pinned on
fixture packets (two supported classes; a complete packet refuting every
class) that the classifier refuses as `inconsistentEvidence`, plus the
Prelude's parametric unknown-evidence refusal.

Scope honesty: EF-2 compensation correctness and EF-3 actuation gates are
separate obligations, matching the Prelude's own nonclaims.  The fixtures are
finite evidence packets, not production effect systems.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.EF1Target

open Residua.RCC.EffectClassification

/-! ## Fixture: a finite five-effect world with one derived class each -/

private inductive DemoEffect where
  | pure
  | prepare
  | reverse
  | compensate
  | irreversible
  deriving DecidableEq, Repr

private def demoSemantics : EffectClassSemantics where
  Effect := DemoEffect
  Context := Unit
  Pure := fun _ effect => effect = .pure
  PrepareCommit := fun _ effect => effect = .prepare
  ExactlyReversible := fun _ effect => effect = .reverse
  Compensatable := fun _ effect => effect = .compensate
  Irreversible := fun _ effect => effect = .irreversible

/-- A complete evidence packet for the compensatable fixture effect. -/
private def demoFacts :
    EffectClassFacts demoSemantics () DemoEffect.compensate where
  pure := .refuted (by intro h; cases h)
  prepareCommit := .refuted (by intro h; cases h)
  exactlyReversible := .refuted (by intro h; cases h)
  compensatable := .supported rfl
  irreversible := .refuted (by intro h; cases h)

private def demoClassification :
    CertifiedEffectClass demoSemantics () DemoEffect.compensate :=
  .compensatable (by intro h; cases h) (by intro h; cases h) (by intro h; cases h)
    rfl (by intro h; cases h)

/-- Non-vacuity: the mechanical derivation produces the exclusive
compensatable certificate from the fixture packet. -/
private def demoDerived : DerivedEffectClassification demoFacts where
  classification := demoClassification
  derived := rfl

/-- Overlap packet: two classes genuinely supported at one effect. -/
private inductive OverlapEffect where
  | both
  deriving DecidableEq

private def overlapSemantics : EffectClassSemantics where
  Effect := OverlapEffect
  Context := Unit
  Pure := fun _ _ => True
  PrepareCommit := fun _ _ => False
  ExactlyReversible := fun _ _ => False
  Compensatable := fun _ _ => True
  Irreversible := fun _ _ => False

private def overlapFacts :
    EffectClassFacts overlapSemantics () OverlapEffect.both where
  pure := .supported trivial
  prepareCommit := .refuted (fun h => h)
  exactlyReversible := .refuted (fun h => h)
  compensatable := .supported trivial
  irreversible := .refuted (fun h => h)

/-- Empty packet: a complete packet refuting every class. -/
private inductive GhostEffect where
  | ghost
  deriving DecidableEq

private def ghostSemantics : EffectClassSemantics where
  Effect := GhostEffect
  Context := Unit
  Pure := fun _ _ => False
  PrepareCommit := fun _ _ => False
  ExactlyReversible := fun _ _ => False
  Compensatable := fun _ _ => False
  Irreversible := fun _ _ => False

private def ghostFacts :
    EffectClassFacts ghostSemantics () GhostEffect.ghost where
  pure := .refuted (fun h => h)
  prepareCommit := .refuted (fun h => h)
  exactlyReversible := .refuted (fun h => h)
  compensatable := .refuted (fun h => h)
  irreversible := .refuted (fun h => h)

/-! ## The certificate -/

structure Certificate : Prop where
  /-- Prelude `CertifiedEffectClass.selected` (parametric): the selected tag
  is supported by the certificate carried in the class. -/
  selectedClassHolds :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context} {effect : K.Effect}
      (classification : CertifiedEffectClass K context effect),
      K.ClassHolds context effect classification.tag
  /-- Prelude `CertifiedEffectClass.excludes` (parametric): every different
  tag is explicitly refuted by the same certificate. -/
  otherClassesRefuted :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context} {effect : K.Effect}
      (classification : CertifiedEffectClass K context effect)
      (other : EffectClassTag)
      (_different : other ≠ classification.tag),
      ¬ K.ClassHolds context effect other
  /-- Prelude `DerivedEffectClassification.selected` (parametric): a derived
  classification supports exactly its selected membership. -/
  derivedSelectedHolds :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context} {effect : K.Effect}
      {facts : EffectClassFacts K context effect}
      (derived : DerivedEffectClassification facts),
      K.ClassHolds context effect derived.classification.tag
  /-- Prelude `effect_classification_exact_of_coverage` (parametric): given
  evidence packets and derivations for every effect, each effect holds exactly
  one class. -/
  completeCoverageIsExact :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context}
      (factsFor : ∀ effect, EffectClassFacts K context effect)
      (_covered :
        ∀ effect, DerivedEffectClassification (factsFor effect)),
      ∀ effect,
        ∃ tag,
          K.ClassHolds context effect tag ∧
            ∀ other, K.ClassHolds context effect other → other = tag
  /-- Prelude `classified_effect_has_selected_evidence` (parametric):
  successful classification proves the selected class predicate. -/
  classifiedCarriesSelectedEvidence :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context} {effect : K.Effect}
      {facts : EffectClassFacts K context effect}
      {classification : CertifiedEffectClass K context effect}
      (_derived : deriveEffectClass facts = .classified classification),
      K.ClassHolds context effect classification.tag
  /-- Fixture: the five-effect world derives one exclusive compensatable
  classification through the common mechanical classifier. -/
  fixtureDerivesOneClass :
    Nonempty (DerivedEffectClassification demoFacts) ∧
      demoDerived.classification.tag = EffectClassTag.compensatable
  /-- Refusal (Prelude `unknown_effect_evidence_is_ambiguous`, parametric):
  unknown evidence is never silently promoted to a class. -/
  unknownEvidenceRefused :
    ∀ {K : EffectClassSemantics.{0, 0}}
      {context : K.Context} {effect : K.Effect}
      (facts : EffectClassFacts K context effect)
      (_unknown : facts.hasUnknown = true),
      facts.supportCount ≤ 1 →
        deriveEffectClass facts = .refuse .ambiguousEvidence
  /-- Refusal (fixture): a packet supporting two classes is refused as
  inconsistent; no priority order chooses between them. -/
  doubleSupportRefused :
    deriveEffectClass overlapFacts = .refuse .inconsistentEvidence
  /-- Refusal (fixture): a complete packet refuting every class is refused
  as inconsistent; it does not default to `Pure`. -/
  totalRefutationRefused :
    deriveEffectClass ghostFacts = .refuse .inconsistentEvidence

def certificate : Certificate where
  selectedClassHolds := CertifiedEffectClass.selected
  otherClassesRefuted := CertifiedEffectClass.excludes
  derivedSelectedHolds := DerivedEffectClassification.selected
  completeCoverageIsExact := effect_classification_exact_of_coverage
  classifiedCarriesSelectedEvidence :=
    classified_effect_has_selected_evidence
  fixtureDerivesOneClass := ⟨⟨demoDerived⟩, rfl⟩
  unknownEvidenceRefused := unknown_effect_evidence_is_ambiguous
  doubleSupportRefused := rfl
  totalRefutationRefused := rfl

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.EF1Target

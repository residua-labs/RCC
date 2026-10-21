import Init

/-!
# RCC EF-1 Effects are classified as Pure, PrepareCommit, ExactlyReversible,
# Compensatable, or Irreversible

EF-1 classifies every effect as exactly one of:

* `Pure`;
* `PrepareCommit`;
* `ExactlyReversible`;
* `Compensatable`; or
* `Irreversible`.

The instance does not supply an enum or status.  It supplies one evidence slot
for each class predicate.  A slot is either supported by a proof, refuted by a
proof, or explicitly unknown.  The common classifier admits a class only when
one slot is supported and all other slots are refuted.

Unknown evidence yields `ambiguousEvidence`.  Multiple supported classes, or a
complete packet refuting every class, yields `inconsistentEvidence`.  No
priority order silently chooses among overlapping claims.

This file does not prove EF-2 compensation correctness, EF-3 irreversible
actuation gates, WI-6 post-effect re-observation, or effect liveness.

Prelude-only Lean 4.14; no Mathlib, no custom axioms, and no proof
placeholders.
-/

namespace Residua.RCC.EffectClassification

universe u v

/--
Domain meanings for the five frozen EF-1 effect classes at an exact context.

These predicates are exclusive classification-membership judgments, not broad
capabilities.  In particular, `Compensatable` means the selected non-exact
compensation class; the compensation goal and its proof belong to EF-2.
Likewise, `PrepareCommit` names the selected protocol class rather than merely
asserting that some prepare operation exists.
-/
structure EffectClassSemantics where
  Effect : Type u
  Context : Type v
  Pure : Context → Effect → Prop
  PrepareCommit : Context → Effect → Prop
  ExactlyReversible : Context → Effect → Prop
  Compensatable : Context → Effect → Prop
  Irreversible : Context → Effect → Prop

/--
One proof-carrying classification fact.

`unknown` is not negation.  Only `refuted` may exclude a class.
-/
inductive EvidenceState (proposition : Prop)
  | supported (proof : proposition)
  | refuted (proof : ¬ proposition)
  | unknown

namespace EvidenceState

/-- Executable projection used only to detect an incomplete evidence packet. -/
def isUnknown {proposition : Prop} :
    EvidenceState proposition → Bool
  | .unknown => true
  | .supported _ => false
  | .refuted _ => false

/-- Erase the proof only to count competing positive class evidence. -/
def isSupported {proposition : Prop} :
    EvidenceState proposition → Bool
  | .supported _ => true
  | .refuted _ => false
  | .unknown => false

end EvidenceState

/-- Complete EF-1 evidence coordinates for one effect. -/
structure EffectClassFacts
    (K : EffectClassSemantics)
    (context : K.Context)
    (effect : K.Effect) where
  pure : EvidenceState (K.Pure context effect)
  prepareCommit : EvidenceState (K.PrepareCommit context effect)
  exactlyReversible : EvidenceState (K.ExactlyReversible context effect)
  compensatable : EvidenceState (K.Compensatable context effect)
  irreversible : EvidenceState (K.Irreversible context effect)

/-- At least one class coordinate lacks proof or refutation. -/
def EffectClassFacts.hasUnknown
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (facts : EffectClassFacts K context effect) : Bool :=
  facts.pure.isUnknown ||
    facts.prepareCommit.isUnknown ||
    facts.exactlyReversible.isUnknown ||
    facts.compensatable.isUnknown ||
    facts.irreversible.isUnknown

/-- Number of classes positively supported by the current evidence packet. -/
def EffectClassFacts.supportCount
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (facts : EffectClassFacts K context effect) : Nat :=
  (if facts.pure.isSupported then 1 else 0) +
    (if facts.prepareCommit.isSupported then 1 else 0) +
    (if facts.exactlyReversible.isSupported then 1 else 0) +
    (if facts.compensatable.isSupported then 1 else 0) +
    (if facts.irreversible.isSupported then 1 else 0)

/--
Exclusive proof object for the derived class.

Every constructor carries the selected class proof and explicit refutations of
all four alternatives.  No caller-supplied enum appears in this structure.
-/
inductive CertifiedEffectClass
    (K : EffectClassSemantics)
    (context : K.Context)
    (effect : K.Effect)
  | pure
      (supported : K.Pure context effect)
      (notPrepareCommit : ¬ K.PrepareCommit context effect)
      (notExactlyReversible : ¬ K.ExactlyReversible context effect)
      (notCompensatable : ¬ K.Compensatable context effect)
      (notIrreversible : ¬ K.Irreversible context effect)
  | prepareCommit
      (notPure : ¬ K.Pure context effect)
      (supported : K.PrepareCommit context effect)
      (notExactlyReversible : ¬ K.ExactlyReversible context effect)
      (notCompensatable : ¬ K.Compensatable context effect)
      (notIrreversible : ¬ K.Irreversible context effect)
  | exactlyReversible
      (notPure : ¬ K.Pure context effect)
      (notPrepareCommit : ¬ K.PrepareCommit context effect)
      (supported : K.ExactlyReversible context effect)
      (notCompensatable : ¬ K.Compensatable context effect)
      (notIrreversible : ¬ K.Irreversible context effect)
  | compensatable
      (notPure : ¬ K.Pure context effect)
      (notPrepareCommit : ¬ K.PrepareCommit context effect)
      (notExactlyReversible : ¬ K.ExactlyReversible context effect)
      (supported : K.Compensatable context effect)
      (notIrreversible : ¬ K.Irreversible context effect)
  | irreversible
      (notPure : ¬ K.Pure context effect)
      (notPrepareCommit : ¬ K.PrepareCommit context effect)
      (notExactlyReversible : ¬ K.ExactlyReversible context effect)
      (notCompensatable : ¬ K.Compensatable context effect)
      (supported : K.Irreversible context effect)

/-- Erased class tag for projections and tests. -/
inductive EffectClassTag
  | pure
  | prepareCommit
  | exactlyReversible
  | compensatable
  | irreversible
  deriving DecidableEq, Repr

/-- Erase proofs only after exclusive classification has been constructed. -/
def CertifiedEffectClass.tag
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect} :
    CertifiedEffectClass K context effect → EffectClassTag
  | .pure _ _ _ _ _ => .pure
  | .prepareCommit _ _ _ _ _ => .prepareCommit
  | .exactlyReversible _ _ _ _ _ => .exactlyReversible
  | .compensatable _ _ _ _ _ => .compensatable
  | .irreversible _ _ _ _ _ => .irreversible

/-- Interpret an erased tag back into the domain's class proposition. -/
def EffectClassSemantics.ClassHolds
    (K : EffectClassSemantics)
    (context : K.Context)
    (effect : K.Effect) : EffectClassTag → Prop
  | .pure => K.Pure context effect
  | .prepareCommit => K.PrepareCommit context effect
  | .exactlyReversible => K.ExactlyReversible context effect
  | .compensatable => K.Compensatable context effect
  | .irreversible => K.Irreversible context effect

/-- The selected tag is supported by the certificate carried in the class. -/
theorem CertifiedEffectClass.selected
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (classification : CertifiedEffectClass K context effect) :
    K.ClassHolds context effect classification.tag := by
  cases classification with
  | pure supported _ _ _ _ => exact supported
  | prepareCommit _ supported _ _ _ => exact supported
  | exactlyReversible _ _ supported _ _ => exact supported
  | compensatable _ _ _ supported _ => exact supported
  | irreversible _ _ _ _ supported => exact supported

/-- Every different tag is explicitly refuted by the same certificate. -/
theorem CertifiedEffectClass.excludes
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (classification : CertifiedEffectClass K context effect)
    (other : EffectClassTag)
    (different : other ≠ classification.tag) :
    ¬ K.ClassHolds context effect other := by
  cases classification with
  | pure _ notPrepareCommit notExactlyReversible
      notCompensatable notIrreversible =>
      cases other with
      | pure => exact (different rfl).elim
      | prepareCommit => exact notPrepareCommit
      | exactlyReversible => exact notExactlyReversible
      | compensatable => exact notCompensatable
      | irreversible => exact notIrreversible
  | prepareCommit notPure _ notExactlyReversible
      notCompensatable notIrreversible =>
      cases other with
      | pure => exact notPure
      | prepareCommit => exact (different rfl).elim
      | exactlyReversible => exact notExactlyReversible
      | compensatable => exact notCompensatable
      | irreversible => exact notIrreversible
  | exactlyReversible notPure notPrepareCommit _
      notCompensatable notIrreversible =>
      cases other with
      | pure => exact notPure
      | prepareCommit => exact notPrepareCommit
      | exactlyReversible => exact (different rfl).elim
      | compensatable => exact notCompensatable
      | irreversible => exact notIrreversible
  | compensatable notPure notPrepareCommit notExactlyReversible _
      notIrreversible =>
      cases other with
      | pure => exact notPure
      | prepareCommit => exact notPrepareCommit
      | exactlyReversible => exact notExactlyReversible
      | compensatable => exact (different rfl).elim
      | irreversible => exact notIrreversible
  | irreversible notPure notPrepareCommit notExactlyReversible
      notCompensatable _ =>
      cases other with
      | pure => exact notPure
      | prepareCommit => exact notPrepareCommit
      | exactlyReversible => exact notExactlyReversible
      | compensatable => exact notCompensatable
      | irreversible => exact (different rfl).elim

/-- EF-1 named evidence failures. -/
inductive EffectClassificationResidue
  | ambiguousEvidence
  | inconsistentEvidence
  deriving DecidableEq, Repr

/-- Total EF-1 classification outcome. -/
inductive EffectClassificationResult
    (K : EffectClassSemantics)
    (context : K.Context)
    (effect : K.Effect)
  | classified (classification : CertifiedEffectClass K context effect)
  | refuse (residue : EffectClassificationResidue)

/--
Mechanically derive the unique effect class.

The exact five successful patterns are exhaustive.  An unknown coordinate
prevents exclusion of another class and is therefore ambiguous.  Any complete
packet not matching one of the five exclusive patterns is inconsistent.
-/
def deriveEffectClass
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (facts : EffectClassFacts K context effect) :
    EffectClassificationResult K context effect :=
  if 1 < facts.supportCount then
    .refuse .inconsistentEvidence
  else if facts.hasUnknown then
    .refuse .ambiguousEvidence
  else
    match facts.pure,
        facts.prepareCommit,
        facts.exactlyReversible,
        facts.compensatable,
        facts.irreversible with
    | .supported pure,
        .refuted notPrepareCommit,
        .refuted notExactlyReversible,
        .refuted notCompensatable,
        .refuted notIrreversible =>
      .classified
        (.pure pure notPrepareCommit notExactlyReversible
          notCompensatable notIrreversible)
    | .refuted notPure,
        .supported prepareCommit,
        .refuted notExactlyReversible,
        .refuted notCompensatable,
        .refuted notIrreversible =>
      .classified
        (.prepareCommit notPure prepareCommit notExactlyReversible
          notCompensatable notIrreversible)
    | .refuted notPure,
        .refuted notPrepareCommit,
        .supported exactlyReversible,
        .refuted notCompensatable,
        .refuted notIrreversible =>
      .classified
        (.exactlyReversible notPure notPrepareCommit exactlyReversible
          notCompensatable notIrreversible)
    | .refuted notPure,
        .refuted notPrepareCommit,
        .refuted notExactlyReversible,
        .supported compensatable,
        .refuted notIrreversible =>
      .classified
        (.compensatable notPure notPrepareCommit notExactlyReversible
          compensatable notIrreversible)
    | .refuted notPure,
        .refuted notPrepareCommit,
        .refuted notExactlyReversible,
        .refuted notCompensatable,
        .supported irreversible =>
      .classified
        (.irreversible notPure notPrepareCommit notExactlyReversible
          notCompensatable irreversible)
    | _, _, _, _, _ =>
      .refuse .inconsistentEvidence

/--
Downstream proof that a class came through the common mechanical derivation.

Consumers should require this wrapper (or its `derived` equation), rather than
accepting a naked `CertifiedEffectClass`.
-/
structure DerivedEffectClassification
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (facts : EffectClassFacts K context effect) where
  classification : CertifiedEffectClass K context effect
  derived :
    deriveEffectClass facts = .classified classification

/-- A derived classification supports exactly its selected membership. -/
theorem DerivedEffectClassification.selected
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    {facts : EffectClassFacts K context effect}
    (derived : DerivedEffectClassification facts) :
    K.ClassHolds context effect derived.classification.tag :=
  derived.classification.selected

/--
Complete derived coverage gives exactly one semantic class for every effect.

The instance supplies evidence coordinates and a mechanical derivation for
each effect. The unique tag is then forced by the selected proof and the four
explicit exclusions carried by that same derived certificate.
-/
theorem effect_classification_exact_of_coverage
    {K : EffectClassSemantics}
    {context : K.Context}
    (factsFor : ∀ effect, EffectClassFacts K context effect)
    (covered :
      ∀ effect, DerivedEffectClassification (factsFor effect)) :
    ∀ effect,
      ∃ tag,
        K.ClassHolds context effect tag ∧
          ∀ other, K.ClassHolds context effect other → other = tag := by
  intro effect
  let derived := covered effect
  refine ⟨derived.classification.tag, derived.selected, ?_⟩
  intro other holds
  cases decEq other derived.classification.tag with
  | isTrue equal => exact equal
  | isFalse different =>
      exact ((derived.classification.excludes other different) holds).elim

/-- Successful classification proves the selected class predicate. -/
theorem classified_effect_has_selected_evidence
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    {facts : EffectClassFacts K context effect}
    {classification : CertifiedEffectClass K context effect}
    (_derived :
      deriveEffectClass facts = .classified classification) :
    K.ClassHolds context effect classification.tag :=
  classification.selected

/-- Unknown evidence can never be silently promoted to a class. -/
theorem unknown_effect_evidence_is_ambiguous
    {K : EffectClassSemantics}
    {context : K.Context}
    {effect : K.Effect}
    (facts : EffectClassFacts K context effect)
    (unknown : facts.hasUnknown = true) :
    facts.supportCount ≤ 1 →
    deriveEffectClass facts =
      .refuse .ambiguousEvidence := by
  intro compatible
  simp [deriveEffectClass, unknown, Nat.not_lt.mpr compatible]

end Residua.RCC.EffectClassification

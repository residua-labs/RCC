import RCC.DefeqFragment

/-!
# RCC defeq normalizer on the supported subtype

This file establishes DQ-2 for the recursively closed `num`/`add` fragment.
The normalization kernel accepts only the proof-carrying `NumAddTerm`
subtype.  Consequently:

* normalization is total on its declared domain;
* its result is a canonical normal form, not `Option` or `Unsupported`;
* unsupported production terms can be reported only by the DQ-1 classifier
  at the ingress boundary;
* recursive `add` nodes are all consumed by structural recursion over the
  fragment-membership proof.

Semantic preservation, fuel irrelevance, defeq exactness, and normal-form
encoding are later DQ obligations and are deliberately not claimed here.
-/

namespace Residua.RCC.DefeqNormalizer

open Residua.RCC.DefeqFragment

/-! ## Canonical result domain -/

/-- The canonical normal forms of the current `num`/`add` fragment.  Keeping
this as a dedicated type, rather than identifying it with `Int`, leaves the
codec and typed-address boundary explicit for DQ-6 and DQ-7. -/
inductive NumAddNormalForm
  | int : Int → NumAddNormalForm
  deriving DecidableEq, Repr

/-- Read the integer represented by a canonical normal form. -/
def NumAddNormalForm.value : NumAddNormalForm → Int
  | .int value => value

/-! ## Total proof-directed normalization -/

private theorem add_left_supported
    {left right : Term}
    (supported : InNumAddFragment (.add left right)) :
    InNumAddFragment left := by
  cases supported with
  | add leftSupported _ =>
      exact leftSupported

private theorem add_right_supported
    {left right : Term}
    (supported : InNumAddFragment (.add left right)) :
    InNumAddFragment right := by
  cases supported with
  | add _ rightSupported =>
      exact rightSupported

/-- Normalize by structural recursion over the production term while the
fragment proof supplies membership of recursive children.  There is no
fallback value: every impossible production constructor is eliminated by its
contradictory membership proof. -/
def normalizeProof :
    (term : Term) → InNumAddFragment term → NumAddNormalForm
  | .num value, _ =>
      .int value
  | .add left right, supported =>
      .int
        ((normalizeProof left (add_left_supported supported)).value +
         (normalizeProof right (add_right_supported supported)).value)
  | .var _, supported =>
      False.elim (by cases supported)
  | .sub _ _, supported =>
      False.elim (by cases supported)
  | .mul _ _, supported =>
      False.elim (by cases supported)
  | .div _ _, supported =>
      False.elim (by cases supported)
  | .ifE _ _ _, supported =>
      False.elim (by cases supported)
  | .neg _, supported =>
      False.elim (by cases supported)
  | .lt _ _, supported =>
      False.elim (by cases supported)
  | .eq _ _, supported =>
      False.elim (by cases supported)
  | .let_ _ _ _, supported =>
      False.elim (by cases supported)
  | .call _ _, supported =>
      False.elim (by cases supported)

/-- The public DQ-2 normalizer.  Its input type proves fragment membership and
its codomain contains neither failure nor unsupported constructors. -/
def normalize (term : NumAddTerm) : NumAddNormalForm :=
  normalizeProof term.1 term.property

/-- Normalizing a numeric leaf is definitionally total. -/
@[simp]
theorem normalize_num (value : Int) :
    normalize ⟨.num value, .num value⟩ = .int value := by
  rfl

/-- Normalization consumes both recursive children of every supported `add`
node. -/
@[simp]
theorem normalize_add
    {left right : Term}
    (leftSupported : InNumAddFragment left)
    (rightSupported : InNumAddFragment right) :
    normalize ⟨.add left right, .add leftSupported rightSupported⟩ =
      .int
        ((normalize ⟨left, leftSupported⟩).value +
         (normalize ⟨right, rightSupported⟩).value) := by
  rfl

/-- Constructive totality: every supported input computes a canonical normal
form.  The witness is the normalizer result itself; no choice or search is
used. -/
theorem normalize_total (term : NumAddTerm) :
    ∃ normalForm : NumAddNormalForm, normalize term = normalForm := by
  exact ⟨normalize term, rfl⟩

/-! ## The only raw-term ingress boundary -/

/-- Boundary output for callers that still hold a raw production `Term`.
Unsupported is a classifier result here, not a result of `normalize`. -/
inductive NormalizationIngress (term : Term)
  | normalized : NumAddNormalForm → NormalizationIngress term
  | unsupported :
      UnsupportedFragmentCert term →
      NormalizationIngress term

/-- Classify a raw term before invoking the total supported-domain
normalizer. -/
def normalizeAtBoundary (term : Term) : NormalizationIngress term :=
  match classifyToSubtype term with
  | .inl supported =>
      .normalized (normalize supported)
  | .inr unsupported =>
      .unsupported unsupported

/-- A supported classifier result necessarily crosses the boundary as a
canonical normal form. -/
theorem boundary_normalizes_supported
    (term : Term)
    (supported : NumAddTerm)
    (classified : classifyToSubtype term = .inl supported) :
    normalizeAtBoundary term = .normalized (normalize supported) := by
  rw [normalizeAtBoundary, classified]

/-- An unsupported classifier result is preserved exactly at the boundary;
the total normalizer is never called on it. -/
theorem boundary_preserves_unsupported
    (term : Term)
    (unsupported : UnsupportedFragmentCert term)
    (classified : classifyToSubtype term = .inr unsupported) :
    normalizeAtBoundary term = .unsupported unsupported := by
  rw [normalizeAtBoundary, classified]

/-- Converse boundary law: every reported unsupported result is exactly a
DQ-1 classifier result.  The normalizer itself has no constructor capable of
producing it. -/
theorem boundary_unsupported_origin
    (term : Term)
    (unsupported : UnsupportedFragmentCert term)
    (reported :
      normalizeAtBoundary term = .unsupported unsupported) :
    classifyToSubtype term = .inr unsupported := by
  cases classified : classifyToSubtype term with
  | inl supported =>
      rw [normalizeAtBoundary, classified] at reported
      cases reported
  | inr sourceUnsupported =>
      rw [normalizeAtBoundary, classified] at reported
      cases reported
      rfl

end Residua.RCC.DefeqNormalizer

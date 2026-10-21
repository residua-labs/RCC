import RCCTests.DefeqNormalizer

/-!
# DQ-2 candidate: the normalizer is total on the supported subtype

DQ-2's obligation is that defeq normalization is total on the proof-carrying
`NumAddTerm` subtype: its codomain contains neither failure nor `Unsupported`,
and the only raw-term ingress is the DQ-1 classifier boundary.

The content lives in the Prelude module
`RCC.DefeqNormalizer` (totality proved for the subtype on its
own account) with discriminating mutants in
`RCCTests.DefeqNormalizer`.  This Target only connects that
content to the obligation: the totality and boundary laws are restated as
certificate fields by import, and the three mutant exposure theorems are
recited as the refusal sites (a partial raw-domain normalizer, a fallback that
collapses unsupported input into a normal form, and a recursion that omits one
`add` child).

Scope honesty: semantic preservation, fuel irrelevance, and defeq exactness
are later DQ obligations and are deliberately not claimed here, matching the
Prelude's own nonclaims.

Prelude-only Lean 4.14; no Mathlib, custom axioms, or proof placeholders.
-/

namespace Residua.RCC.DQ2Target

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqNormalizer.Tests

/-! ## The certificate -/

structure Certificate : Prop where
  /-- Prelude `normalize_total` (parametric): every supported input computes a
  canonical normal form, with the result itself as witness. -/
  normalizeTotalOnSubtype :
    ∀ term : NumAddTerm,
      ∃ normalForm : NumAddNormalForm, normalize term = normalForm
  /-- Prelude `normalize_num` (parametric): numeric leaves normalize
  definitionally. -/
  numericLeafNormalizes :
    ∀ value : Int,
      normalize ⟨.num value, .num value⟩ = .int value
  /-- Prelude `normalize_add` (parametric): normalization consumes both
  recursive children of every supported `add` node. -/
  addConsumesBothChildren :
    ∀ {left right : Term}
      (leftSupported : InNumAddFragment left)
      (rightSupported : InNumAddFragment right),
      normalize ⟨.add left right, .add leftSupported rightSupported⟩ =
        .int
          ((normalize ⟨left, leftSupported⟩).value +
            (normalize ⟨right, rightSupported⟩).value)
  /-- Prelude `boundary_normalizes_supported` (parametric): a supported
  classifier result necessarily crosses the boundary as a normal form. -/
  supportedCrossesBoundary :
    ∀ (term : Term)
      (supported : NumAddTerm)
      (_classified : classifyToSubtype term = .inl supported),
      normalizeAtBoundary term = .normalized (normalize supported)
  /-- Fixture (Tests `supportedNested`): arbitrary recursive `add` nesting
  computes.  Carried by `rfl`, not by a new lemma. -/
  nestedFixtureNormalizes :
    normalize (Tests.supportedNested : NumAddTerm) = .int 6
  /-- Refusal (Tests `raw_partial_normalizer_mutant_exposed`): a partial
  normalizer over the raw `Term` domain returns `none` on unsupported input,
  while the proof-carrying boundary refuses it. -/
  partialRawDomainRefused :
    rawPartialNormalizer unsupportedVariable = none ∧
      ∃ cert,
        normalizeAtBoundary unsupportedVariable = .unsupported cert
  /-- Refusal (Tests `fallback_collapse_mutant_exposed`): unsupported input
  cannot be collapsed into a legitimate normal form. -/
  fallbackCollapseRefused :
    fallbackCollapseNormalizer unsupportedVariable =
        fallbackCollapseNormalizer (supportedZero : NumAddTerm).1 ∧
      normalizeAtBoundary unsupportedVariable ≠
        .normalized (normalize (supportedZero : NumAddTerm))
  /-- Refusal (Tests `recursive_add_omission_mutant_exposed`): a recursion
  that omits the right `add` child is discriminated from the real
  normalizer on the nested fixture. -/
  recursiveOmissionRefused :
    omitRightAdd (supportedNested : NumAddTerm) = .int 1 ∧
      normalize (supportedNested : NumAddTerm) = .int 6 ∧
      omitRightAdd (supportedNested : NumAddTerm) ≠
        normalize (supportedNested : NumAddTerm)
  /-- Refusal (Prelude `boundary_unsupported_origin`, parametric): every
  reported unsupported result originates exactly at the DQ-1 classifier; the
  total normalizer has no constructor that could produce it. -/
  unsupportedOriginIsClassifierOnly :
    ∀ (term : Term)
      (unsupported : UnsupportedFragmentCert term)
      (_reported : normalizeAtBoundary term = .unsupported unsupported),
      classifyToSubtype term = .inr unsupported

def certificate : Certificate where
  normalizeTotalOnSubtype := normalize_total
  numericLeafNormalizes := normalize_num
  addConsumesBothChildren := normalize_add
  supportedCrossesBoundary := boundary_normalizes_supported
  nestedFixtureNormalizes := rfl
  partialRawDomainRefused := raw_partial_normalizer_mutant_exposed
  fallbackCollapseRefused := fallback_collapse_mutant_exposed
  recursiveOmissionRefused := recursive_add_omission_mutant_exposed
  unsupportedOriginIsClassifierOnly := boundary_unsupported_origin

theorem candidate_is_nonempty : Nonempty Certificate :=
  ⟨certificate⟩

end Residua.RCC.DQ2Target

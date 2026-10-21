import RCC.DefeqFuelIrrelevance

/-!
# RCC normal-form uniqueness and exact definitional equality

This file establishes DQ-5 for the recursively closed `num`/`add` fragment.
The equality judgment is defined only on the proof-carrying supported
subtype.  Unsupported production terms remain at the DQ-1 classification
boundary and cannot be represented as `NotEqual`.

The declared relation compares the semantic values of canonical DQ-2 normal
forms.  DQ-3 connects those values to production `evalLF`, while DQ-4 removes
all sufficient-fuel choice from that connection.  DQ-5 proves:

* canonical normal-form equality is exact for the declared relation;
* the relation is reflexive, symmetric, and transitive;
* canonical normal forms representing one supported term are unique;
* the executable verdict is total and proof carrying;
* raw unsupported input never enters the equality-verdict type.

No address, codec, digest, or hash-injectivity claim is made here; those are
the later DQ-6..DQ-8 obligations.
-/

namespace Residua.RCC.DefeqExactness

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqSemanticPreservation
open Residua.RCC.DefeqFuelIrrelevance

/-! ## Semantic relation and canonical normal forms -/

/-- The semantic value denoted by a supported term's canonical normal form. -/
def semanticValue (term : NumAddTerm) : Val :=
  evalNormalForm (normalize term)

/-- The declared definitional-equality relation for the current supported
fragment.  It is a relation on `NumAddTerm`, not on raw production `Term`, so
unsupported input is outside the judgment domain rather than being
misreported as unequal. -/
def DefEq (left right : NumAddTerm) : Prop :=
  semanticValue left = semanticValue right

/-- The relation is constructively decidable on the supported subtype because
canonical normal-form values have decidable equality.  This decision does not
extend to raw unsupported terms. -/
instance instDecidableDefEq (left right : NumAddTerm) :
    Decidable (DefEq left right) :=
  inferInstanceAs
    (Decidable (semanticValue left = semanticValue right))

/-- Canonical normal-form semantics is injective for the current integer
normal-form universe. -/
theorem evalNormalForm_injective
    {left right : NumAddNormalForm}
    (sameValue : evalNormalForm left = evalNormalForm right) :
    left = right := by
  cases left with
  | int leftValue =>
      cases right with
      | int rightValue =>
          cases sameValue
          rfl

/-- DQ-5 exactness: equality of canonical normal forms is equivalent to the
declared semantic definitional-equality relation. -/
theorem normalize_eq_iff_defeq (left right : NumAddTerm) :
    normalize left = normalize right ↔ DefEq left right := by
  constructor
  · intro sameNormalForm
    unfold DefEq semanticValue
    rw [sameNormalForm]
  · intro equivalent
    unfold DefEq semanticValue at equivalent
    apply evalNormalForm_injective
    exact equivalent

/-! ## Relation laws -/

theorem defeq_refl (term : NumAddTerm) :
    DefEq term term := by
  rfl

theorem defeq_symm {left right : NumAddTerm} :
    DefEq left right → DefEq right left := by
  intro equivalent
  exact Eq.symm equivalent

theorem defeq_trans {left middle right : NumAddTerm} :
    DefEq left middle →
    DefEq middle right →
    DefEq left right := by
  intro leftMiddle middleRight
  exact Eq.trans leftMiddle middleRight

/-- The declared DQ-5 relation is an equivalence relation on the supported
subtype. -/
theorem defeq_equivalence : Equivalence DefEq :=
  ⟨defeq_refl, defeq_symm, defeq_trans⟩

/-! ## Normal-form uniqueness -/

/-- A canonical normal form represents a term when both have the same
normal-form semantic value. -/
def Represents (term : NumAddTerm) (normalForm : NumAddNormalForm) : Prop :=
  evalNormalForm normalForm = semanticValue term

theorem normalize_represents (term : NumAddTerm) :
    Represents term (normalize term) := by
  rfl

/-- Two canonical normal forms representing the same supported term are
equal.  This is a uniqueness theorem over the `NumAddNormalForm` carrier,
not merely a statement about one evaluator run. -/
theorem normal_form_unique
    {term : NumAddTerm}
    {left right : NumAddNormalForm}
    (leftRepresents : Represents term left)
    (rightRepresents : Represents term right) :
    left = right := by
  apply evalNormalForm_injective
  exact Eq.trans leftRepresents (Eq.symm rightRepresents)

/-! ## Production-evaluator bridge -/

/-- With independently chosen sufficient fuels, production evaluation agrees
exactly when the declared DQ-5 relation holds.  DQ-3 supplies both semantic
bridges; DQ-4 guarantees that no hidden default-fuel identity is involved. -/
theorem defeq_iff_evalLF_equal
    (left right : NumAddTerm)
    (env : Env)
    (progs : Progs)
    (leftFuel rightFuel : Nat)
    (leftEnough : requiredFuel left.1 ≤ leftFuel)
    (rightEnough : requiredFuel right.1 ≤ rightFuel) :
    DefEq left right ↔
      evalLF leftFuel left.1 env progs =
        evalLF rightFuel right.1 env progs := by
  rw [evalLF_normalize_semantics left env progs leftFuel leftEnough]
  rw [evalLF_normalize_semantics right env progs rightFuel rightEnough]
  constructor
  · intro equivalent
    exact congrArg some equivalent
  · intro sameEvaluation
    exact Option.some.inj sameEvaluation

/-! ## Proof-carrying executable verdict -/

/-- Equality and inequality are the only verdicts on supported inputs.  There
is deliberately no `Unsupported` constructor. -/
inductive DefEqVerdict (left right : NumAddTerm)
  | equal :
      DefEq left right →
      DefEqVerdict left right
  | notEqual :
      ¬ DefEq left right →
      DefEqVerdict left right

/-- Erase a proof-carrying verdict to the DQ-1 supported-only state enum. -/
def DefEqVerdict.state {left right : NumAddTerm} :
    DefEqVerdict left right → SupportedEqualityVerdict
  | .equal _    => .equal
  | .notEqual _ => .notEqual

/-- The total equality decision on supported inputs. -/
def decideDefEq (left right : NumAddTerm) :
    DefEqVerdict left right :=
  if sameNormalForm : normalize left = normalize right then
    .equal ((normalize_eq_iff_defeq left right).mp sameNormalForm)
  else
    .notEqual
      (fun equivalent =>
        sameNormalForm ((normalize_eq_iff_defeq left right).mpr equivalent))

/-- Every proof-carrying verdict reports equality exactly when the declared
relation holds. -/
theorem verdict_equal_iff
    {left right : NumAddTerm}
    (verdict : DefEqVerdict left right) :
    verdict.state = .equal ↔ DefEq left right := by
  cases verdict with
  | equal equivalent =>
      constructor
      · intro _
        exact equivalent
      · intro _
        rfl
  | notEqual notEquivalent =>
      constructor
      · intro impossible
        cases impossible
      · intro equivalent
        exact False.elim (notEquivalent equivalent)

/-- The total decision reports inequality exactly when the declared relation
does not hold. -/
theorem verdict_not_equal_iff
    {left right : NumAddTerm}
    (verdict : DefEqVerdict left right) :
    verdict.state = .notEqual ↔ ¬ DefEq left right := by
  cases verdict with
  | equal equivalent =>
      constructor
      · intro impossible
        cases impossible
      · intro notEquivalent
        exact False.elim (notEquivalent equivalent)
  | notEqual notEquivalent =>
      constructor
      · intro _
        exact notEquivalent
      · intro _
        rfl

/-! ## Raw-term ingress boundary -/

/-- Raw terms are classified before a `DefEqVerdict` can be built.
Unsupported evidence remains a separate boundary result. -/
inductive DefEqBoundaryResult (left right : Term)
  | compared :
      (leftSupported : InNumAddFragment left) →
      (rightSupported : InNumAddFragment right) →
      DefEqVerdict
        ⟨left, leftSupported⟩
        ⟨right, rightSupported⟩ →
      DefEqBoundaryResult left right
  | unsupported :
      ComparisonSide →
      UnsupportedFragmentResidue →
      DefEqBoundaryResult left right

/-- Classify both raw inputs before invoking the supported-only equality
decision. -/
def decideDefEqAtBoundary (left right : Term) :
    DefEqBoundaryResult left right :=
  match prepareComparison left right with
  | .ready leftSupported rightSupported =>
      .compared leftSupported rightSupported
        (decideDefEq
          ⟨left, leftSupported⟩
          ⟨right, rightSupported⟩)
  | .unsupported side residue =>
      .unsupported side residue

/-- A DQ-1 unsupported classification is preserved by the DQ-5 boundary and
cannot become a `NotEqual` verdict. -/
theorem boundary_preserves_unsupported
    (left right : Term)
    (side : ComparisonSide)
    (residue : UnsupportedFragmentResidue)
    (classified :
      prepareComparison left right = .unsupported side residue) :
    decideDefEqAtBoundary left right = .unsupported side residue := by
  rw [decideDefEqAtBoundary, classified]

end Residua.RCC.DefeqExactness

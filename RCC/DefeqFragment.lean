import RCC.Support.LeanOnceSoundnessProduction

/-!
# RCC defeq supported-fragment classification

This file establishes DQ-1 for the current twelve-constructor `Term` surface.
It does not define normalization or definitional equality.  It establishes the
load-bearing phase boundary needed by those later layers:

* the recursively closed `num`/`add` fragment is explicit;
* classification is total and proof carrying;
* every unsupported result carries a typed residue locating the first
  unsupported constructor;
* unsupported input is not represented as an equality verdict;
* the complete twelve-constructor root surface is mechanically enumerated.

The classifier consumes the production `Term` directly, so a change to that
surface forces this file to be revisited rather than being hidden by a
permissive catch-all.
-/

namespace Residua.RCC.DefeqFragment

/-! ## Constructor and surface coordinates -/

/-- A closed name for every constructor in the production `Term` surface. -/
inductive TermConstructor
  | num
  | var
  | add
  | sub
  | mul
  | div
  | ifE
  | neg
  | lt
  | eq
  | let_
  | call
  deriving DecidableEq, Repr

/-- The root constructor of a production term.  Every constructor is named
explicitly; there is no fallback arm. -/
def rootConstructor : Term → TermConstructor
  | .num _       => .num
  | .var _       => .var
  | .add _ _     => .add
  | .sub _ _     => .sub
  | .mul _ _     => .mul
  | .div _ _     => .div
  | .ifE _ _ _   => .ifE
  | .neg _       => .neg
  | .lt _ _      => .lt
  | .eq _ _      => .eq
  | .let_ _ _ _  => .let_
  | .call _ _    => .call

/-- The sealed constructor universe for the production term fragment. -/
def allTermConstructors : List TermConstructor :=
  [ .num, .var, .add, .sub, .mul, .div
  , .ifE, .neg, .lt, .eq, .let_, .call
  ]

/-- The sealed constructor universe covers every named constructor. -/
theorem all_term_constructors_complete (ctor : TermConstructor) :
    ctor ∈ allTermConstructors := by
  cases ctor <;> decide

/-- Consequently every production term root is in the sealed universe. -/
theorem root_constructor_covered (term : Term) :
    rootConstructor term ∈ allTermConstructors :=
  all_term_constructors_complete (rootConstructor term)

/-- Constructors that are outside the supported `num`/`add` root surface.
Using a closed type prevents a residue from naming `num` or `add` as an
unsupported root. -/
inductive UnsupportedConstructor
  | var
  | sub
  | mul
  | div
  | ifE
  | neg
  | lt
  | eq
  | let_
  | call
  deriving DecidableEq, Repr

/-- Embed an unsupported constructor name back into the complete surface. -/
def UnsupportedConstructor.toTermConstructor :
    UnsupportedConstructor → TermConstructor
  | .var   => .var
  | .sub   => .sub
  | .mul   => .mul
  | .div   => .div
  | .ifE   => .ifE
  | .neg   => .neg
  | .lt    => .lt
  | .eq    => .eq
  | .let_  => .let_
  | .call  => .call

/-- Every unsupported constructor is nevertheless accounted for by the
complete production surface. -/
theorem unsupported_constructor_covered (ctor : UnsupportedConstructor) :
    ctor.toTermConstructor ∈ allTermConstructors :=
  all_term_constructors_complete ctor.toTermConstructor

/-! ## The recursively closed supported subtype -/

/-- The supported language is the recursively closed `num`/`add` fragment. -/
inductive InNumAddFragment : Term → Prop
  | num (value : Int) :
      InNumAddFragment (.num value)
  | add {left right : Term} :
      InNumAddFragment left →
      InNumAddFragment right →
      InNumAddFragment (.add left right)

/-- A supported term, with membership certified in the type. -/
abbrev NumAddTerm := { term : Term // InNumAddFragment term }

/-- A path from the root through supported `add` nodes to the first
unsupported constructor. -/
inductive FragmentPathStep
  | addLeft
  | addRight
  deriving DecidableEq, Repr

/-- The typed explanation produced for an unsupported term. -/
structure UnsupportedFragmentResidue where
  path : List FragmentPathStep
  constructor : UnsupportedConstructor
  deriving DecidableEq, Repr

/-- Prepend one `add` edge while propagating a child residue. -/
def UnsupportedFragmentResidue.prepend
    (step : FragmentPathStep)
    (residue : UnsupportedFragmentResidue) :
    UnsupportedFragmentResidue :=
  { residue with path := step :: residue.path }

/-- A typed certificate that a term is outside the supported fragment. -/
structure UnsupportedFragmentCert (term : Term) where
  residue : UnsupportedFragmentResidue
  notInFragment : ¬ InNumAddFragment term

/-- Total proof-carrying classification of one production term. -/
inductive FragmentClassification (term : Term)
  | supported :
      InNumAddFragment term →
      FragmentClassification term
  | unsupported :
      UnsupportedFragmentCert term →
      FragmentClassification term

/-- The semantic erasure of a proof-carrying classification. -/
inductive FragmentState
  | supported
  | unsupported
  deriving DecidableEq, Repr

def FragmentClassification.state {term : Term} :
    FragmentClassification term → FragmentState
  | .supported _   => .supported
  | .unsupported _ => .unsupported

def FragmentClassification.isSupported {term : Term}
    (classification : FragmentClassification term) : Bool :=
  match classification.state with
  | .supported   => true
  | .unsupported => false

def FragmentClassification.residue? {term : Term} :
    FragmentClassification term → Option UnsupportedFragmentResidue
  | .supported _   => none
  | .unsupported c => some c.residue

private def unsupportedRoot
    (term : Term)
    (constructor : UnsupportedConstructor)
    (notInFragment : ¬ InNumAddFragment term) :
    FragmentClassification term :=
  .unsupported
    { residue := { path := [], constructor := constructor }
    , notInFragment := notInFragment
    }

/-- The total DQ-1 classifier.  Its recursive branches follow only `add`;
every other production constructor returns an explicit typed residue. -/
def classifyTerm : (term : Term) → FragmentClassification term
  | .num value =>
      .supported (.num value)
  | .add left right =>
      match classifyTerm left with
      | .unsupported leftCert =>
          .unsupported
            { residue := leftCert.residue.prepend .addLeft
            , notInFragment := by
                intro supported
                cases supported with
                | add leftSupported _ =>
                    exact leftCert.notInFragment leftSupported
            }
      | .supported leftSupported =>
          match classifyTerm right with
          | .unsupported rightCert =>
              .unsupported
                { residue := rightCert.residue.prepend .addRight
                , notInFragment := by
                    intro supported
                    cases supported with
                    | add _ rightSupported =>
                        exact rightCert.notInFragment rightSupported
                }
          | .supported rightSupported =>
              .supported (.add leftSupported rightSupported)
  | .var name =>
      unsupportedRoot (.var name) .var (by intro h; cases h)
  | .sub left right =>
      unsupportedRoot (.sub left right) .sub (by intro h; cases h)
  | .mul left right =>
      unsupportedRoot (.mul left right) .mul (by intro h; cases h)
  | .div left right =>
      unsupportedRoot (.div left right) .div (by intro h; cases h)
  | .ifE cond thenBranch elseBranch =>
      unsupportedRoot (.ifE cond thenBranch elseBranch) .ifE
        (by intro h; cases h)
  | .neg term =>
      unsupportedRoot (.neg term) .neg (by intro h; cases h)
  | .lt left right =>
      unsupportedRoot (.lt left right) .lt (by intro h; cases h)
  | .eq left right =>
      unsupportedRoot (.eq left right) .eq (by intro h; cases h)
  | .let_ name value body =>
      unsupportedRoot (.let_ name value body) .let_ (by intro h; cases h)
  | .call name argument =>
      unsupportedRoot (.call name argument) .call (by intro h; cases h)

private theorem classification_supported_iff
    {term : Term}
    (classification : FragmentClassification term) :
    classification.isSupported = true ↔ InNumAddFragment term := by
  cases classification with
  | supported proof =>
      constructor
      · intro _
        exact proof
      · intro _
        rfl
  | unsupported cert =>
      constructor
      · intro impossible
        cases impossible
      · intro inFragment
        exact False.elim (cert.notInFragment inFragment)

private theorem classification_unsupported_iff
    {term : Term}
    (classification : FragmentClassification term) :
    classification.isSupported = false ↔ ¬ InNumAddFragment term := by
  cases classification with
  | supported proof =>
      constructor
      · intro impossible
        cases impossible
      · intro notInFragment
        exact False.elim (notInFragment proof)
  | unsupported cert =>
      constructor
      · intro _
        exact cert.notInFragment
      · intro _
        rfl

/-- Classifier soundness and completeness: the executable supported bit is
true exactly for inductively supported terms. -/
theorem classify_supported_iff (term : Term) :
    (classifyTerm term).isSupported = true ↔ InNumAddFragment term := by
  exact classification_supported_iff (classifyTerm term)

/-- The negative half of classifier exactness. -/
theorem classify_unsupported_iff (term : Term) :
    (classifyTerm term).isSupported = false ↔ ¬ InNumAddFragment term := by
  exact classification_unsupported_iff (classifyTerm term)

/-- Convert the total classifier into the supported subtype or a typed
unsupported certificate. -/
def classifyToSubtype (term : Term) :
    NumAddTerm ⊕ UnsupportedFragmentCert term :=
  match classifyTerm term with
  | .supported proof   => .inl ⟨term, proof⟩
  | .unsupported cert  => .inr cert

/-! ## Comparison phase separation -/

/-- The side on which supported-fragment classification failed. -/
inductive ComparisonSide
  | left
  | right
  deriving DecidableEq, Repr

/-- Inputs to a later equality checker.  `ready` is constructible only after
both operands have entered the supported subtype.  Unsupported input has a
separate typed constructor and therefore cannot be represented as
`NotEqual`. -/
inductive ComparisonReadiness (left right : Term)
  | ready :
      InNumAddFragment left →
      InNumAddFragment right →
      ComparisonReadiness left right
  | unsupported :
      ComparisonSide →
      UnsupportedFragmentResidue →
      ComparisonReadiness left right

/-- Classify both sides before any equality judgment is permitted. -/
def prepareComparison (left right : Term) :
    ComparisonReadiness left right :=
  match classifyTerm left with
  | .unsupported cert =>
      .unsupported .left cert.residue
  | .supported leftSupported =>
      match classifyTerm right with
      | .unsupported cert =>
          .unsupported .right cert.residue
      | .supported rightSupported =>
          .ready leftSupported rightSupported

/-- Equality verdicts exist only after `ComparisonReadiness.ready`.
`Unsupported` is deliberately absent from this type. -/
inductive SupportedEqualityVerdict
  | equal
  | notEqual
  deriving DecidableEq, Repr

end Residua.RCC.DefeqFragment

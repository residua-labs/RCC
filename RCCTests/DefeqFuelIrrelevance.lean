import RCC.DefeqFuelIrrelevance

/-!
# Tests and load-bearing mutant for DQ-4

The positive witness leaves both excess-fuel amounts arbitrary.  The mutant
uses one fuel unit below the structural bound and demonstrates that removing
the sufficient-fuel premise makes the proposed equality false.
-/

namespace Residua.RCC.DefeqFuelIrrelevance.Tests

open Residua.RCC.DefeqFragment
open Residua.RCC.DefeqNormalizer
open Residua.RCC.DefeqSemanticPreservation
open Residua.RCC.DefeqFuelIrrelevance

def nestedTerm : NumAddTerm :=
  ⟨ .add (.num 4) (.add (.num 5) (.num 6))
  , .add (.num 4) (.add (.num 5) (.num 6))
  ⟩

def arbitraryEnv : Env :=
  fun name => if name = "unused" then some (.bool true) else none

def arbitraryProgs : Progs :=
  fun name =>
    if name = "unused" then some (["x"], .var "x") else none

/-! ## Arbitrary-large-fuel witness -/

theorem arbitrary_large_fuel_witness (extra₁ extra₂ : Nat) :
    evalLF (requiredFuel nestedTerm.1 + extra₁) nestedTerm.1
        arbitraryEnv arbitraryProgs =
      evalLF (requiredFuel nestedTerm.1 + extra₂) nestedTerm.1
        arbitraryEnv arbitraryProgs := by
  exact
    evalLF_arbitrary_excess_fuel
      nestedTerm arbitraryEnv arbitraryProgs extra₁ extra₂

/-! ## Mutant: the lower-bound premise is omitted -/

def oneAddTerm : NumAddTerm :=
  ⟨.add (.num 7) (.num 8), .add (.num 7) (.num 8)⟩

/-- A fuel-insensitive evaluator mutant would equate these runs.  Production
`evalLF` instead returns `none` one unit below the derived bound and the
canonical value at the bound. -/
theorem insufficient_fuel_mutant_exposed :
    requiredFuel oneAddTerm.1 = 2 ∧
    evalLF 1 oneAddTerm.1 arbitraryEnv arbitraryProgs = none ∧
    evalLF (requiredFuel oneAddTerm.1) oneAddTerm.1
        arbitraryEnv arbitraryProgs =
      some (.int (normalize oneAddTerm).value) ∧
    evalLF 1 oneAddTerm.1 arbitraryEnv arbitraryProgs ≠
      evalLF (requiredFuel oneAddTerm.1) oneAddTerm.1
        arbitraryEnv arbitraryProgs := by
  decide

#print axioms evalLF_fuel_irrelevant_above_required
#print axioms evalLF_eq_at_requiredFuel
#print axioms evalLF_arbitrary_excess_fuel
#print axioms arbitrary_large_fuel_witness
#print axioms insufficient_fuel_mutant_exposed

end Residua.RCC.DefeqFuelIrrelevance.Tests

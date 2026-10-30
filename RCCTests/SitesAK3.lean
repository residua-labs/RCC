import RCC.DigestBinding

/-!
# Registration site for AK-3 (ResiduaRCCDigestBinding)

`DigestBinding`'s structural floor is parametric; this site instantiates it at
concrete bytes.  Positive half: the same bytes are `reuse`, distinct bytes are
`miss`, and under the explicit injectivity premise address equality is byte
equality.  Discriminating half: a constant-digest mutant produces a named
`collision` refusal rather than a silent `reuse`, and cannot satisfy the
injectivity premise.  The library theorems are untouched.
-/

open Residua.RCC.Addressing

namespace Residua.RCC.RegistrationSites.AK3

/-- The honest minimal frame: the wire is the complete structured preimage
itself, so no serialization claim is made beyond `ExactFrame`'s contract. -/
def preimageFrame : ExactFrame String (DigestPreimage String) where
  encode := id
  encode_injective := fun equal => equal

/-- A faithful digest commits to the canonical bytes. -/
def faithfulHash (preimage : DigestPreimage String) : Digest :=
  ⟨preimage.canonicalBytes⟩

/-- The concrete fixture binding at kind `.value`. -/
def valueBinding (hash : DigestPreimage String → Digest) :
    DigestBinding .value String (DigestPreimage String) where
  algorithm := ⟨"site-algorithm"⟩
  domainQ := ⟨"site-domain"⟩
  schemaQ := ⟨"site-schema"⟩
  frame := preimageFrame
  hash := hash

/-- The faithful digest is injective on the framed canonical range: equal
digests give equal canonical bytes, and every other preimage field is fixed by
the binding. -/
theorem faithful_injective :
    DigestInjectiveOnCanonicalRange (valueBinding faithfulHash) := by
  intro left right equalHash
  have bytesEq : left = right := by
    have h := congrArg Digest.value equalHash
    simpa [valueBinding, DigestBinding.framedWire, preimageFrame,
      DigestBinding.preimage, faithfulHash] using h
  cases bytesEq
  rfl

/-- Positive: identical canonical bytes are inspected as `reuse`. -/
theorem faithful_same_bytes_reuse :
    inspectAddressed (binding := valueBinding faithfulHash) ⟨"alpha"⟩ ⟨"alpha"⟩ =
      .reuse := by
  exact (inspect_addressed_eq_reuse_iff _ _).mpr ⟨rfl, rfl⟩

/-- Positive: distinct canonical bytes are inspected as `miss` (under the
faithful digest, addresses differ). -/
theorem faithful_distinct_bytes_miss :
    inspectAddressed (binding := valueBinding faithfulHash) ⟨"alpha"⟩ ⟨"beta"⟩ =
      .miss := by
  apply (inspect_addressed_eq_miss_iff _ _).mpr
  intro equalAddress
  have bytesEq :=
    (digest_address_eq_iff_bytes_eq _ faithful_injective "alpha" "beta").mp
      equalAddress
  exact absurd bytesEq (by decide)

/-- Positive: under the explicit premise, address equality IS byte equality at
this fixture, in both directions. -/
theorem faithful_address_eq_iff_bytes_eq :
    (valueBinding faithfulHash).address "alpha" =
        (valueBinding faithfulHash).address "beta" ↔
      "alpha" = "beta" :=
  digest_address_eq_iff_bytes_eq _ faithful_injective _ _

/-- Collision mutant: a digest that ignores the preimage content entirely. -/
def mutantHash (_preimage : DigestPreimage String) : Digest :=
  ⟨"constant"⟩

/-- The mutant cannot satisfy the injectivity premise: two distinct byte
strings collide on its constant digest while their framed preimages differ.
This is the tooth that makes the premise load-bearing rather than decorative. -/
theorem mutant_injectivity_impossible :
    ¬ DigestInjectiveOnCanonicalRange (valueBinding mutantHash) := by
  intro injective
  have wireEq := injective (left := "alpha") (right := "beta") rfl
  have bytesEq : "alpha" = "beta" := by
    have h := congrArg DigestPreimage.canonicalBytes wireEq
    simpa [valueBinding, DigestBinding.framedWire, preimageFrame,
      DigestBinding.preimage] using h
  exact absurd bytesEq (by decide)

/-- Discriminating refusal: the mutant's same-address hit is inspected as an
explicit `collision`, never a silent `reuse`. -/
theorem mutant_hit_is_named_collision :
    inspectAddressed (binding := valueBinding mutantHash) ⟨"alpha"⟩ ⟨"beta"⟩ =
      .collision := by
  apply (inspect_addressed_eq_collision_iff _ _).mpr
  constructor
  · rfl
  · intro preimageEq
    have bytesEq : ("alpha" : String) = "beta" :=
      congrArg DigestPreimage.canonicalBytes preimageEq
    exact absurd bytesEq (by decide)

#print axioms faithful_injective
#print axioms faithful_same_bytes_reuse
#print axioms faithful_distinct_bytes_miss
#print axioms faithful_address_eq_iff_bytes_eq
#print axioms mutant_injectivity_impossible
#print axioms mutant_hit_is_named_collision

end Residua.RCC.RegistrationSites.AK3

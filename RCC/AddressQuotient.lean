import Init

/-!
# RCC typed address quotient kernel

This Prelude-only module discharges the formal AK-1 quotient-selection floor
and the AK-4 consumer-factorization law. It deliberately does not model a
canonical codec, digest injectivity, a collision-aware store, address
resolution, schema migration, an `AddressUseRegistry`, or the RCC-0 capstone.
-/

namespace Residua.RCC.Addressing

universe u v w z

/-- The exact typed identity tower declared by the RCC ADR. -/
inductive AddressKind
  | syntax
  | semantic
  | value
  | occurrence
  | judgment
  | receipt
  | event
  | schema
  | implementation
  deriving DecidableEq, Repr

/-- Nominal digest-algorithm identifier. -/
structure AlgorithmId where
  value : String
  deriving DecidableEq, Repr

/-- Nominal quotient-domain identifier. -/
structure DomainQ where
  value : String
  deriving DecidableEq, Repr

/-- Nominal canonical-schema identifier. -/
structure SchemaQ where
  value : String
  deriving DecidableEq, Repr

/--
Nominal digest carrier. No injectivity or cryptographic property is asserted
for its string representation.
-/
structure Digest where
  value : String
  deriving DecidableEq, Repr

/-- A digest is authoritative only inside its typed address envelope. -/
structure Address (kind : AddressKind) where
  algorithm : AlgorithmId
  domainQ : DomainQ
  schemaQ : SchemaQ
  digest : Digest
  deriving DecidableEq, Repr

/-- A context-indexed identity choice together with its preserved observation. -/
structure IdentityDomain (kind : AddressKind) where
  Object : Type u
  Context : Type v
  Observation : Type w
  equivalent : Context → Object → Object → Prop
  observe : Context → Object → Observation

/--
AK-1's mandatory safety floor: each contextual relation is an equivalence and
the declared observation is constant on its classes.
-/
structure QuotientAdequate {kind : AddressKind}
    (domain : IdentityDomain kind) : Prop where
  equivalence : ∀ context, Equivalence (domain.equivalent context)
  observe_sound : ∀ {context left right},
    domain.equivalent context left right →
      domain.observe context left = domain.observe context right

/-- Optional stronger adequacy: equal observations also identify a class. -/
def ObservationExact {kind : AddressKind}
    (domain : IdentityDomain kind) : Prop :=
  ∀ {context left right},
    domain.observe context left = domain.observe context right →
      domain.equivalent context left right

/-- The contextual equivalence packaged as Lean's quotient relation. -/
def IdentityDomain.setoid {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context) : Setoid domain.Object where
  r := domain.equivalent context
  iseqv := adequate.equivalence context

/-- Abstract an object into its declared contextual quotient class. -/
def qAbs {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context) (object : domain.Object) :
    Quotient (domain.setoid adequate context) :=
  Quotient.mk _ object

/-- A consumer is lawful exactly when it is constant on declared classes. -/
def ConsumerFactorsThroughQuotient {kind : AddressKind}
    (domain : IdentityDomain kind) (context : domain.Context)
    {Result : Type z} (consumer : domain.Object → Result) : Prop :=
  ∀ ⦃x y⦄,
    domain.equivalent context x y → consumer x = consumer y

/--
Explicit conditional boundary for address substitution. Concrete digest
soundness remains outside AK-1/AK-4.
-/
def AddressSound {kind : AddressKind}
    (domain : IdentityDomain kind) (context : domain.Context)
    (address : domain.Object → Address kind) : Prop :=
  ∀ ⦃left right⦄,
    address left = address right → domain.equivalent context left right

/-- Quotient equality is exactly the declared contextual equivalence. -/
theorem qAbs_eq_iff_equivalent {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context) (left right : domain.Object) :
    qAbs domain adequate context left = qAbs domain adequate context right ↔
      domain.equivalent context left right := by
  exact ⟨Quotient.exact, fun equivalent =>
    by simpa [qAbs] using Quotient.sound equivalent⟩

/--
When observation completeness is explicitly supplied, quotient equality is
also exactly observation equality.
-/
theorem quotient_exact_iff_observation {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (exact : ObservationExact domain) (context : domain.Context)
    (left right : domain.Object) :
    qAbs domain adequate context left = qAbs domain adequate context right ↔
      domain.observe context left = domain.observe context right := by
  exact (qAbs_eq_iff_equivalent domain adequate context left right).trans
    ⟨adequate.observe_sound, exact⟩

/--
AK-4: class-constant behavior is equivalent to a real function defined on
Lean's quotient type.
-/
theorem consumer_factors_iff_exists_lift {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context) {Result : Type z}
    (consumer : domain.Object → Result) :
    ConsumerFactorsThroughQuotient domain context consumer ↔
      ∃ lifted : Quotient (domain.setoid adequate context) → Result,
        ∀ object,
          lifted (qAbs domain adequate context object) = consumer object := by
  constructor
  · intro factors
    refine ⟨Quotient.lift consumer ?_, ?_⟩
    · intro left right equivalent
      exact factors equivalent
    · intro object
      rfl
  · rintro ⟨lifted, liftedSpec⟩ left right equivalent
    rw [← liftedSpec left, ← liftedSpec right]
    congr 1
    simpa [qAbs] using Quotient.sound equivalent

/-- Any quotient-respecting consumer substitutes equal abstract classes. -/
theorem quotient_substitutability {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context) {Result : Type z}
    (consumer : domain.Object → Result)
    (factors : ConsumerFactorsThroughQuotient domain context consumer)
    {left right : domain.Object}
    (equalClass :
      qAbs domain adequate context left = qAbs domain adequate context right) :
    consumer left = consumer right := by
  exact factors
    ((qAbs_eq_iff_equivalent domain adequate context left right).1 equalClass)

/--
Typed address equality permits substitution only when both address soundness
and consumer factorization are supplied explicitly.
-/
theorem typed_address_substitutability {kind : AddressKind}
    (domain : IdentityDomain kind) (adequate : QuotientAdequate domain)
    (context : domain.Context)
    {Result : Type z} (address : domain.Object → Address kind)
    (consumer : domain.Object → Result)
    (sound : AddressSound domain context address)
    (factors : ConsumerFactorsThroughQuotient domain context consumer)
    {left right : domain.Object} (equalAddress : address left = address right) :
    consumer left = consumer right := by
  obtain ⟨lifted, liftedSpec⟩ :=
    (consumer_factors_iff_exists_lift
      domain adequate context consumer).1 factors
  have equivalent : domain.equivalent context left right :=
    sound equalAddress
  have equalClass :
      qAbs domain adequate context left = qAbs domain adequate context right :=
    (qAbs_eq_iff_equivalent
      domain adequate context left right).2 equivalent
  calc
    consumer left = lifted (qAbs domain adequate context left) :=
      (liftedSpec left).symm
    _ = lifted (qAbs domain adequate context right) :=
      congrArg lifted equalClass
    _ = consumer right :=
      liftedSpec right

end Residua.RCC.Addressing

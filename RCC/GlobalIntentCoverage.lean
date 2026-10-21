import RCC.FacetCoherence

/-!
# C3 global intent coverage

Local component closure and seam exactness do not by themselves entail a
global intent.  C3 supplies the missing, explicit sufficiency bridge.

The component and seam predicates remain those of one fixed
`CoherenceWorld`.  An instance must separately explain what each local fact
means for the global intent and prove that the complete family of those local
claims is sufficient.

This theorem does not derive seam exactness and does not construct
`world.globalClosed`.  It also does not prove that the declared component and
seam lists exhaust a larger universe.  Those are separate composition
obligations.
-/

namespace Residua.RCC.GlobalIntentCoverage

open Residua.RCC.FacetCoherence

/--
The complete local closure evidence consumed by the global intent bridge.

Membership premises prevent evidence for an object outside the declared
component or seam lists from substituting for a listed local obligation.
-/
structure CompositionClosureEvidence
    (world : CoherenceWorld) : Prop where
  componentsClosed :
    ∀ component,
      component ∈ world.components →
      world.componentClosed component
  seamsExact :
    ∀ seam,
      seam ∈ world.seams →
      world.seamExact seam

/--
A proof-carrying decomposition of one externally fixed global intent.

The first two laws interpret local closure facts.  The final law is the
load-bearing coverage theorem: all listed component and seam claims jointly
imply the declared global intent.
-/
structure CompositionIntentContract
    (world : CoherenceWorld)
    (ComponentIntent : world.Component → Prop)
    (SeamIntent : world.Seam → Prop)
    (GlobalIntent : Prop) : Prop where
  componentClosedSound :
    ∀ component,
      component ∈ world.components →
      world.componentClosed component →
      ComponentIntent component
  seamExactSound :
    ∀ seam,
      seam ∈ world.seams →
      world.seamExact seam →
      SeamIntent seam
  localClaimsSuffice :
    (∀ component,
      component ∈ world.components →
      ComponentIntent component) →
    (∀ seam,
      seam ∈ world.seams →
      SeamIntent seam) →
    GlobalIntent

/--
C3 headline: complete local closure evidence satisfies the declared global
intent through the supplied one-way decomposition contract.
-/
theorem CompositionClosureEvidence.coversGlobalIntent
    {world : CoherenceWorld}
    {ComponentIntent : world.Component → Prop}
    {SeamIntent : world.Seam → Prop}
    {GlobalIntent : Prop}
    (evidence : CompositionClosureEvidence world)
    (contract :
      CompositionIntentContract
        world ComponentIntent SeamIntent GlobalIntent) :
    GlobalIntent :=
  contract.localClaimsSuffice
    (fun component member =>
      contract.componentClosedSound
        component member (evidence.componentsClosed component member))
    (fun seam member =>
      contract.seamExactSound
        seam member (evidence.seamsExact seam member))

end Residua.RCC.GlobalIntentCoverage

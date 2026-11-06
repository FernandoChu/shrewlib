import ComprehensionCategory.Basic
import Displayed.CodCatEquiv.Equivalence
import Displayed.Straightening.Equivalence

/-!
# The displayed category model

The *displayed category model* is the comprehension category `LaxNormalCat` over `Cat`, whose
types in context `Γ` are the lax normal functors from `Γ` to the bicategory of profunctors, that
is, the categories displayed over `Γ` in Bénabou's sense. Its comprehension functor is the composite
equivalence over `Cat`

```
  LaxNormalCat ≃ DisplayedCat ≃ cod Cat
```

of straightening–unstraightening (`straighteningEquiv`) and of taking total categories
(`DisplayedCat.codEquiv`): `compr = unstraighten ⋙ᵥ DisplayedCat.total`. So the context extension
`Γ ▹ F` is the total category of the unstraightening of `F`, a Grothendieck construction on
profunctors, and `𝐩 F` is its projection.

As a composite of equivalences, the comprehension functor preserves cartesian morphisms and is fully
faithful, and `LaxNormalCat` is a split fibration by restriction, so the displayed category model is
a full split comprehension category. Every functor into `Γ` is, up to isomorphism, the projection
`𝐩 F` of a type `F`: the model is a split replacement of the codomain comprehension category
`cod Cat`, which is not split.
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

/-- The comprehension functor of the displayed category model: unstraighten, then take the total
category. It is the composite equivalence `LaxNormalCat ≃ DisplayedCat ≃ cod Cat`. -/
def compr : VertFunctor LaxNormalCat.{u, u, u} (cod Cat.{u, u}) :=
  unstraighten ⋙ᵥ DisplayedCat.total

/-- **The comprehension functor preserves cartesian morphisms**, as a composite of equivalences. -/
def isCartesianComprMap : compr.{u}.PreservesCartesian := fun H =>
  DisplayedCat.codEquiv.isCartesianMap (isCartesianUnstraightenMap H)

/-- **The comprehension functor is fully faithful**, as a composite of equivalences. -/
def comprFullyFaithful : compr.{u}.FullyFaithful :=
  straighteningEquiv.fullyFaithful.comp DisplayedCat.totalFullyFaithful

/-- The comprehension structure of the displayed category model. -/
@[instance_reducible]
instance comprehension : Comprehension LaxNormalCat.{u, u, u} where
  compr := compr
  isCartesianComprMap := isCartesianComprMap

/-- **The displayed category model** is a full split comprehension category over `Cat`. -/
instance splitComprehension : SplitComprehension LaxNormalCat.{u, u, u} where

@[instance_reducible]
instance fullComprehension : FullComprehension LaxNormalCat.{u, u, u} where
  comprFullyFaithful := comprFullyFaithful

end ComprehensionCategory.DisplayedModel

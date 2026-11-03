import Displayed.Opfibration.SplitOpfibLax

/-!
# Straightening split opfibrations

The straightening of a split opfibration `D` over `A` is the functor `A ⥤ Cat` of its fibres
`a ↦ D.Fiber a`, with the pushforward functors `pushFunctor f`. It is a functor by `rfl`, since the
splitting laws and the functoriality of `pushMap` are rules.

There is no straightening of morphisms here: the inverse of the unstraightening on morphisms is
`unstraightenPreimage`, and `Equivalence.lean` assembles the equivalence from it.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : SplitOpfibOb A)

/-- **The straightening of a split opfibration** `D`: its fibres, with the pushforward
functors. -/
def straightenObj : A ⥤ Cat.{u, u} where
  obj a := Cat.of (X.toDisplayed.Fiber a)
  map f := (X.toDisplayed.pushFunctor f).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Opfibration.Straightening

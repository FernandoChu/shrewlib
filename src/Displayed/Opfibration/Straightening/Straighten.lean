import Displayed.Opfibration.Straightening.SplitOpfibCat

/-!
# Straightening split opfibrations

The straightening of a split opfibration `p : E ⥤ A` is the functor `A ⥤ Cat` of its fibres
`a ↦ Fibre p a`, with the pushforward functors `pushFunctor f`. It is a functor by `rfl`, since the
splitting laws and the functoriality of `pushMap` are rules.

There is no straightening of morphisms here: the inverse of the unstraightening on morphisms is
`unstraightenPreimage`, and `Equivalence.lean` assembles the equivalence from it.
-/

universe u

namespace Displayed.Opfibration.Straightening

open CategoryTheory Displayed

open Displayed.Straightening (fibres)

open scoped Displayed

variable {A : Cat.{u, u}} (X : SplitOpfibOb A)

/-- **The straightening of a split opfibration** `p : E ⥤ A`: its fibres, with the pushforward
functors. -/
def straightenObj : A ⥤ Cat.{u, u} where
  obj a := Cat.of ((fibres X.ob).Fiber a)
  map f := ((fibres X.ob).pushFunctor f).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Opfibration.Straightening

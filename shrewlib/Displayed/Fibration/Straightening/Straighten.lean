import Displayed.Fibration.SplitFibLax
import Rules.Opposite

/-!
# Straightening split fibrations

The straightening of a split fibration `D` over `A` is the functor `Aᵒᵖ ⥤ Cat` of its fibres
`a ↦ D.Fiber a`, with the pullback functors `pullFunctor f`. It is a functor by `rfl`, since the
splitting laws and the functoriality of `pullMap` are rules.

There is no straightening of morphisms here: the inverse of the unstraightening on morphisms is
`unstraightenPreimage`, and `Equivalence.lean` assembles the equivalence from it. This is the dual
of `Opfibration/Straightening/Straighten.lean`.
-/

universe u

namespace Displayed.Fibration.Straightening

open CategoryTheory Opposite Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : SplitFibOb A)

/-- **The straightening of a split fibration** `D`: its fibres, with the pullback functors. -/
def straightenObj : Aᵒᵖ ⥤ Cat.{u, u} where
  obj a := Cat.of (X.toDisplayed.Fiber a.unop)
  map f := (X.toDisplayed.pullFunctor f.unop).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

end Displayed.Fibration.Straightening

import Displayed.Discrete.Basic
import Displayed.Discrete.Straightening.IDisc
import Displayed.Opfibration.Straightening.Straighten

/-!
# Straightening discrete opfibrations

The straightening of a discrete opfibration `X` over `A` is its straightening as a split
opfibration, the functor `A ⥤ Cat` of its fibres `a ↦ X.Fiber a` with the pushforward functors,
whose values are discrete since the fibres are.
-/

universe u

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : DiscOpfibOb A)

/-- **The straightening of a discrete opfibration** `X`: its fibres, with the pushforward
functors. -/
def straightenObj : IDiscOb A where
  toFunctor := Opfibration.Straightening.straightenObj (DiscOpfibCat.forget.obj X)
  isDiscrete := X.isDiscrete

end Displayed.Discrete.Straightening

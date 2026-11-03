import Displayed.Discrete.Basic
import Displayed.Discrete.Straightening.IDisc
import Displayed.Opfibration.Straightening.Straighten

/-!
# Straightening discrete opfibrations

The straightening of a discrete opfibration `X` over `A` is its straightening as a split
opfibration, the functor `A ⥤ Cat` of its fibres `a ↦ X.Fiber a` with the pushforward functors,
whose values are discrete since the fibres are. The straightening of a displayed functor is its
straightening as a functor between split opfibrations, a lax transformation, which is a morphism of
`IDisc`: this is the vertical functor `straighten : DiscOpfibCat ⟶ IDisc`.
-/

universe u

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed

open scoped Displayed

variable {A : Cat.{u, u}} (X : DiscOpfibOb A)

/-- **The straightening of a discrete opfibration** `X`: its fibres, with the pushforward
functors. -/
def straightenObj : IDiscOb.{u} A where
  toFunctor := Opfibration.Straightening.straightenObj (DiscOpfibCat.forget.obj X)
  isDiscrete := X.isDiscrete

/-- **The straightening of discrete opfibrations**: that of split opfibrations, on the discrete
ones. -/
def straighten : VertFunctor DiscOpfibCat.{u} IDisc.{u} where
  obj X := straightenObj X
  map H := Opfibration.Straightening.straighten.map (DiscOpfibCat.forget.map H)
  map_id X := Opfibration.Straightening.straighten.map_id (DiscOpfibCat.forget.obj X)
  map_comp H K := Opfibration.Straightening.straighten.map_comp (DiscOpfibCat.forget.map H)
    (DiscOpfibCat.forget.map K)

end Displayed.Discrete.Straightening

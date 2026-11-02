import Displayed.CodCatEquiv.Equivalence
import Displayed.Fibration.DisplayedCat

/-!
# Reindexing goes to pullbacks, and the fibration `cod Cat`

Taking total categories, `DisplayedCat.total : DisplayedCat ⟶ cod Cat`, sends the chosen lift
`DisplayedCat.clift u E` to a cartesian morphism of `cod Cat`
(`DisplayedCat.isCartesianTotalMapClift`): the total category of `DisplayedCat.pull u E` is the
pullback of `E.Total` along `u`. This holds because `total` is an equivalence over `Cat`, which
preserves cartesian morphisms.

`cod Cat` is a fibration over `Cat` (`DisplayedCat.fibCodCat`), with the cleavage transferred from
the split fibration `DisplayedCat` along `DisplayedCat.codEquiv`. It is not split: the pullback of
`p` along `v ≫ u` is only isomorphic to its pullback along `u` and then `v`.
-/

universe u

open CategoryTheory

namespace Displayed.DisplayedCat

open scoped Displayed

/-- **Reindexing goes to pullbacks**: `(pull u E).Total` is the pullback of `E.Total` along `u`,
since `total` is an equivalence and the chosen lift `clift u E` is cartesian. -/
def isCartesianTotalMapClift {A B : Cat.{u, u}} {u : A ⟶ B} {E : Displayed.{u, u, u, u} B} :
    IsCartesian (total.map (clift u E)) :=
  codEquiv.isCartesianMap (isCartesianClift u E)

/-- **`cod Cat` is a fibration over `Cat`**, with the cleavage transferred from `DisplayedCat` along
`DisplayedCat.codEquiv`. -/
instance fibCodCat : Fib (cod Cat.{u, u}) :=
  codEquiv.fib

end Displayed.DisplayedCat

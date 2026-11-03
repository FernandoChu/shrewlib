import DoubleDisplayed.D2SFib.DProfStr
import DoubleDisplayed.D2SFib.D2SFibStr
import DoubleDisplayed.D2SFib.Straightening.Straighten

/-!
# Straightening of D2SFibs, over `SplitOpfibStr`

The straightening `straightenObj C : Bᵒᵖ.Total ⥤ Cat` of a split D2SFib `C` over `B` sends
`⟨a, x⟩` to the fiber of `C` over `x`, and a morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`
(`DoubleDisplayed/D2SFib/Straightening/Straighten.lean`). Here we extend it to the maps of D2SFibs
over arbitrary opcartesian functors, which makes it natural in `B`: a map `Φ` over `H` gives the
natural transformation `straightenObj C ⟶ H.dualOp.total ⋙ straightenObj C'` whose components are
the fiber functors of `Φ` (`straightenStrMap`), and the straightening is a vertical functor
`straightenStr : VertFunctor D2SFibStr DProfStr` over `SplitOpfibStr`.

The naturality of `straightenStrMap Φ` holds by `rfl`: `Φ` commutes with `pushMap` and `pullMap`,
by the rules of `D2SFibMap`.
-/

universe u

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {B : Displayed.{u, u, u, u} A}
  {B' : Displayed.{u, u, u, u} A'} [SplitOpfib B] [SplitOpfib B']
  {H : OpcartesianFunctor u.toFunctor B B'} {C : DoubleDisplayed.{u, u, u, u, u, u} B}
  {C' : DoubleDisplayed.{u, u, u, u, u, u} B'} [SplitD2SFib C] [SplitD2SFib C']

/-- **The straightening of a map of D2SFibs** `Φ` over `H`: the natural transformation
`straightenObj C ⟶ H.dualOp.total ⋙ straightenObj C'` whose components are the fiber functors of
`Φ`. -/
def straightenStrMap (Φ : D2SFibMap H C C') :
    straightenObj C ⟶ H.dualOp.total ⋙ straightenObj C' where
  app x := (Φ.toDDFunctor.fiber x.2).toCatHom
  naturality _ _ _ := rfl

/-- **The straightening over `SplitOpfibStr`**: D2SFibs go to their straightenings, and their maps
over `H` to morphisms of dependent profunctors over `H`. -/
def straightenStr : VertFunctor D2SFibStr.{u} DProfStr.{u} where
  obj E := straightenObj E.C
  map Φ := straightenStrMap Φ
  map_id _ := rfl
  map_comp _ _ := rfl

end DoubleDisplayed.D2SFib.Straightening

import DoubleDisplayed.D2SFib.Fibred.DProf
import DoubleDisplayed.D2SFib.Fibred.D2SFibDisp
import DoubleDisplayed.D2SFib.Straightening.Straighten

/-!
# Straightening of D2SFibs, over `ICatStr`

The straightening `straightenObj C : (∫ F)ᵒᵖ.Total ⥤ Cat` of a split D2SFib `C` over `∫ F` sends
`⟨a, x⟩` to the fiber of `C` over `x`, and a morphism `⟨α, β⟩` to `pushFunctor α ⋙ pullFunctor β`
(`DoubleDisplayed/D2SFib/Straightening/Straighten.lean`). Here we extend it to the maps of D2SFibs
over arbitrary strict transformations, which makes it natural in `A` and `F`: a map `Φ` over
`τ.unstraighten` gives the natural transformation
`straightenObj C ⟶ τ.dualTotal ⋙ straightenObj C'` whose components are the fiber functors of `Φ`
(`straightenMap`), and the straightening is a vertical functor
`straighten : VertFunctor D2SFibDisp DProf` over `ICatStr`.

The naturality of `straightenMap Φ` holds by `rfl`: `Φ` commutes with `pushMap` and `pullMap`, by
the rules of `D2SFibMap`.
-/

universe u

namespace DoubleDisplayed.D2SFib.Fibred

open CategoryTheory Displayed DoubleDisplayed D2SFib Displayed.Opfibration.Straightening
  DoubleDisplayed.D2SFib.Straightening

open scoped Displayed DoubleDisplayed

variable {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}}
  {τ : StrictTrans F (u.toFunctor ⋙ G)} {C : DoubleDisplayed.{u, u, u, u, u, u} (∫ F)}
  {C' : DoubleDisplayed.{u, u, u, u, u, u} (∫ G)} [SplitD2SFib C] [SplitD2SFib C']

/-- **The straightening of a map of D2SFibs** `Φ` over `τ.unstraighten`: the natural
transformation `straightenObj C ⟶ τ.dualTotal ⋙ straightenObj C'` whose components are the fiber
functors of `Φ`. -/
def straightenMap (Φ : D2SFibMap τ.unstraighten C C') :
    straightenObj C ⟶ τ.dualTotal ⋙ straightenObj C' where
  app x := (Φ.toDDFunctor.fiber x.2).toCatHom
  naturality _ _ _ := rfl

/-- **The straightening over `ICatStr`**: D2SFibs go to their straightenings, and their maps over
`τ` to morphisms of dependent profunctors over `τ`. -/
def straighten : VertFunctor D2SFibDisp.{u} DProf.{u} where
  obj E := straightenObj E.C
  map Φ := straightenMap Φ
  map_id _ := rfl
  map_comp _ _ := rfl

end DoubleDisplayed.D2SFib.Fibred

import Displayed.Opfibration.Straightening.ICatStr
import DoubleDisplayed.D2SFib.Category

/-!
# The fibred category of D2SFibs

The category of split dependent 2-sided fibrations (D2SFibs, `DoubleDisplayed/D2SFib/Basic.lean`)
over all indexed categories, doubly displayed over `ICatStr`: over `F : A ⥤ Cat`, the split
D2SFibs over the unstraightening `∫ F` (the objects of `D2SFibCat (∫ F)`), and over a strict
transformation `τ`, the maps of D2SFibs over its unstraightening `τ.unstraighten`, the opcartesian
functor `∫ F ⟶ ∫ G`. Its laws hold by `rfl`.

Over the identities of `ICatStr`, `τ.unstraighten` is the identity opcartesian functor by a rule,
so the fiber of `D2SFibDisp` over `F` has the maps of D2SFibs over the identity of `∫ F` as
morphisms, which are the morphisms of `D2SFibCat (∫ F)`.
-/

universe u

namespace DoubleDisplayed

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- **The fibred category of D2SFibs**, doubly displayed over `ICatStr`: over `F : A ⥤ Cat`, the
split D2SFibs over `∫ F`, and over a strict transformation `τ`, the maps of D2SFibs over
`τ.unstraighten`. -/
def D2SFibDisp : DoubleDisplayed.{u, u + 1, u, u + 1, u, u + 1} ICatStr.{u} where
  Ob {A} (F : A ⥤ Cat.{u, u}) := D2SFibCat.{u, u, u, u, u, u} (∫ F)
  Hom {_ _ u F G} (τ : StrictTrans F (u.toFunctor ⋙ G)) E E' :=
    D2SFibMap (StrictTrans.unstraighten (u := u.toFunctor) τ) E.C E'.C
  id E := D2SFibMap.id E.C
  comp Φ Ψ := Φ.comp Ψ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The D2SFib structure of an object of `D2SFibDisp`. The instance `D2SFibCat.str` does not apply
to it, since `D2SFibDisp.Ob F` is not reducibly `D2SFibCat (∫ F)`. -/
instance {A : Cat.{u, u}} {F : ICatStr.Ob A} (E : D2SFibDisp.Ob F) :
    SplitD2SFib (D2SFibCat.C (B := ∫ (F : A ⥤ Cat.{u, u})) E) :=
  D2SFibCat.str E

end DoubleDisplayed

import DoubleDisplayed.D2SFib.Straightening.Str.Equivalence
import Displayed.Opfibration.Straightening.Str

/-!
# Straightening–unstraightening for D2SFibs, over `ICatStr`

The straightening of D2SFibs over `SplitOpfibStr` restricts to the split opfibrations that are
unstraightenings of functors `F : A ⥤ Cat`, by reindexing along the unstraightening
`unstraightenStr : ICatStr ⟶ SplitOpfibStr` of `Displayed/Opfibration/Straightening/Str.lean`:

* `DProf`, the category of dependent profunctors over `ICatStr`: over `F`, the functors
  `(∫ F)ᵒᵖ.Total ⥤ Cat` out of the Grothendieck construction of `a ↦ (F a)ᵒᵖ`, and over a strict
  transformation `τ`, the natural transformations `P ⟶ τ.dualTotal ⋙ P'` (`DProf.hom_eq`);
* `D2SFibICatStr`: over `F`, the split D2SFibs over `∫ F`, and over `τ`, the maps of D2SFibs over
  `τ.unstraighten` (`D2SFibICatStr.hom_eq`).

Both are split fibrations over `ICatStr`, as reindexings of split fibrations, and the equivalence
`straighteningEquivStr` and its cartesian functors reindex to an equivalence of fibred categories
over `ICatStr` (`straighteningEquivICatStr`).
-/

universe u

namespace DoubleDisplayed

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- **The category of dependent profunctors over `ICatStr`**: the reindexing of `DProfStr` along
the unstraightening `ICatStr ⟶ SplitOpfibStr`. -/
abbrev DProf : DoubleDisplayed.{u, u + 1, u, u + 1, u, u + 1} ICatStr.{u} :=
  DProfStr.reindex Opfibration.Straightening.unstraightenStr

/-- **The fibred category of D2SFibs over `ICatStr`**: the reindexing of `D2SFibStr` along the
unstraightening `ICatStr ⟶ SplitOpfibStr`. -/
abbrev D2SFibICatStr : DoubleDisplayed.{u, u + 1, u, u + 1, u, u + 1} ICatStr.{u} :=
  D2SFibStr.reindex Opfibration.Straightening.unstraightenStr

/-- A dependent profunctor over `F` is a functor `(∫ F)ᵒᵖ.Total ⥤ Cat`. -/
theorem DProf.ob_eq {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) :
    DProf.Ob (B := ICatStr) F = ((∫ F)ᵒᵖ.Total ⥤ Cat.{u, u}) := rfl

/-- A morphism of dependent profunctors over `τ` is a natural transformation
`P ⟶ τ.dualTotal ⋙ P'`. -/
theorem DProf.hom_eq {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}} {G : A' ⥤ Cat.{u, u}}
    (τ : StrictTrans F (u.toFunctor ⋙ G)) (P : (∫ F)ᵒᵖ.Total ⥤ Cat.{u, u})
    (P' : (∫ G)ᵒᵖ.Total ⥤ Cat.{u, u}) :
    DProf.Hom τ P P' = (P ⟶ StrictTrans.dualTotal (u := u.toFunctor) τ ⋙ P') :=
  rfl

/-- A D2SFib over `F` is a split D2SFib over `∫ F`. -/
theorem D2SFibICatStr.ob_eq {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) :
    D2SFibICatStr.Ob (B := ICatStr) F = D2SFibCat.{u, u, u, u, u, u} (∫ F) := rfl

/-- A map of D2SFibs over `τ` is a map of D2SFibs over `τ.unstraighten`. -/
theorem D2SFibICatStr.hom_eq {A A' : Cat.{u, u}} {u : A ⟶ A'} {F : A ⥤ Cat.{u, u}}
    {G : A' ⥤ Cat.{u, u}} (τ : StrictTrans F (u.toFunctor ⋙ G))
    (E : D2SFibCat.{u, u, u, u, u, u} (∫ F)) (E' : D2SFibCat.{u, u, u, u, u, u} (∫ G)) :
    D2SFibICatStr.Hom τ E E' =
      D2SFibMap (StrictTrans.unstraighten (u := u.toFunctor) τ) E.C E'.C :=
  rfl

namespace D2SFib.Straightening

/-- **Straightening–unstraightening for D2SFibs over `ICatStr`**: the unstraightening of
dependent profunctors is an equivalence `DProf ≃ D2SFibICatStr` over `ICatStr`, with inverse the
straightening. -/
def straighteningEquivICatStr : VertEquivalence DProf.{u} D2SFibICatStr.{u} :=
  straighteningEquivStr.reindex Opfibration.Straightening.unstraightenStr

/-- The unstraightening over `ICatStr` is a cartesian functor. -/
def unstraightenICatStrCartesian : DDCartesianFunctor DProf.{u} D2SFibICatStr.{u} :=
  unstraightenStrCartesian.reindex Opfibration.Straightening.unstraightenStr

/-- The straightening over `ICatStr` is a cartesian functor. -/
def straightenICatStrCartesian : DDCartesianFunctor D2SFibICatStr.{u} DProf.{u} :=
  straightenStrCartesian.reindex Opfibration.Straightening.unstraightenStr

end D2SFib.Straightening

end DoubleDisplayed

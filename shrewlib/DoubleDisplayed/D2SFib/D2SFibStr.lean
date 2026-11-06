import Displayed.Opfibration.SplitOpfibStr
import DoubleDisplayed.D2SFib.Category
import DoubleDisplayed.Fibration

/-!
# The fibred category of D2SFibs

The category `D2SFibStr` of split dependent 2-sided fibrations (`DoubleDisplayed/D2SFib/Basic.lean`)
over all split opfibrations, doubly displayed over `SplitOpfibStr`: over a split opfibration `B`,
the split D2SFibs over `B` (the objects of `D2SFibCat B`), and over an opcartesian functor `H`, the
maps of D2SFibs over `H` (`D2SFibMap`). Its laws hold by `rfl`, and its fiber over `B` is the
category `D2SFibCat B`.

`D2SFibStr` is a split fibration over `SplitOpfibStr` by reindexing: the pullback of a D2SFib `C'`
along `H` is its reindexing along `H`, with `D2SFibMap.reindexLift` as chosen lift
(`D2SFibStr.splitDDFib`). Reindexing is strictly functorial, so this fibration is split, while the
fibration of D2SFibs presented as functors into a total category, by pullback, is not.

`D2SFibStr` is reducible, so that `D2SFibStr.Ob B` is `D2SFibCat B` for instance search, and the
D2SFib structure of its objects is `D2SFibCat.str`. This is safe because the category that
instance search then finds on `D2SFibStr.Fiber B`, that of `D2SFibCat B`, is the fiber category.
-/

universe v₃ u₃ v₂ u₂ v₁ u₁

namespace DoubleDisplayed

open CategoryTheory Displayed

open scoped Displayed

-- The universes of the displayed categories and of the fibers only occur in the levels of
-- `D2SFibStr` through the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- **The fibred category of D2SFibs**, doubly displayed over `SplitOpfibStr`: over `B`, the split
D2SFibs over `B`, and over an opcartesian functor `H`, the maps of D2SFibs over `H`. -/
abbrev D2SFibStr : DoubleDisplayed SplitOpfibStr.{v₂, u₂, v₁, u₁} where
  Ob {_} (B : SplitOpfibOb.{v₂, u₂} _) := D2SFibCat.{v₃, u₃} B.toDisplayed
  Hom {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B')) E E' :=
    D2SFibMap H (D2SFibCat.C E) (D2SFibCat.C E')
  id E := D2SFibMap.id (D2SFibCat.C E)
  comp Φ Ψ := Φ.comp Ψ

/-- The chosen pullback of a D2SFib along an opcartesian functor `H` is its reindexing along `H`,
with `D2SFibMap.reindexLift` as chosen lift. -/
instance D2SFibStr.ddFib : DDFib D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁} where
  pull {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B')) (E : D2SFibCat (SplitOpfibOb.toDisplayed B')) :=
    (⟨E.C.reindex H.toDispFunctor⟩ : D2SFibCat (SplitOpfibOb.toDisplayed B))
  clift {_ _ u B B'} (H : OpcartesianFunctor u.toFunctor (SplitOpfibOb.toDisplayed B)
      (SplitOpfibOb.toDisplayed B')) (E : D2SFibCat (SplitOpfibOb.toDisplayed B')) :=
    D2SFibMap.reindexLift H E.C
  isCartesianClift _ _ :=
    { lift := fun {_ _ _} _ {_} χ => D2SFibMap.liftReindex _ _ χ
      lift_fac := fun {_ _ _} _ {_} _ => rfl
      lift_uniq := fun {_ _ _ _ _ _} _ h => by subst h; rfl }

instance D2SFibStr.preSplitDDFib : PreSplitDDFib D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁} := {}

/-- **`D2SFibStr` is a split fibration over `SplitOpfibStr`**, by reindexing. -/
instance D2SFibStr.splitDDFib : SplitDDFib D2SFibStr.{v₃, u₃, v₂, u₂, v₁, u₁} := {}

end DoubleDisplayed

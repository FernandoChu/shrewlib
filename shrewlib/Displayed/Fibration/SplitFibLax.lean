import Displayed.Fibration.Basic
import Displayed.Displayed.DisplayedCat

/-!
# The category of split fibrations

The split fibrations form a category displayed over `Cat` (`SplitFibLax`): an object over `A` is a
displayed category over `A` with a `SplitFib` structure (`SplitFibOb`), and a morphism over
`u : A ⟶ B` is any displayed functor over `u` (`DispFunctor`), which need not preserve the chosen
lifts. Its laws hold by `rfl`. Forgetting the cleavage is a fully faithful vertical functor into
the displayed categories, `SplitFibLax.forget : SplitFibLax ⟶ DisplayedCat`.

This is the dual of `Opfibration/SplitFibLax.lean`, and is not in `Basic.lean` for the same
reason: displayed functors over a functor need the functor laws as rules (`Rules.Functor`), which
should not reach every file using fibrations.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A split fibration over `A`: a displayed category over `A` with a split cleavage. -/
structure SplitFibOb (A : Cat.{u, u}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{u, u, u, u} A
  /-- Its split cleavage. -/
  [splitFib : SplitFib toDisplayed]

attribute [instance] SplitFibOb.splitFib

/-- The split fibrations, displayed over `Cat`: an object over `A` is a split fibration over
`A`, and a morphism over `u` is a displayed functor over `u`, with no condition on the
cleavages. -/
def SplitFibLax : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := SplitFibOb A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The split cleavage of an object of `SplitFibLax`. The instance `SplitFibOb.splitFib` does not
apply to it, since `SplitFibLax.Ob A` is not reducibly `SplitFibOb A`. -/
instance SplitFibLax.splitFib {A : Cat.{u, u}} (X : SplitFibLax.Ob A) :
    SplitFib (SplitFibOb.toDisplayed X) :=
  SplitFibOb.splitFib X

/-- The vertical functor forgetting the split cleavage. -/
def SplitFibLax.forget : VertFunctor SplitFibLax.{u} DisplayedCat.{u} where
  obj X := X.toDisplayed
  map H := H
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the split cleavage is fully faithful, since the morphisms are the same. -/
def SplitFibLax.forgetFullyFaithful : SplitFibLax.forget.{u}.FullyFaithful where
  preimage H := H
  map_preimage _ := rfl
  preimage_map _ := rfl

end Displayed

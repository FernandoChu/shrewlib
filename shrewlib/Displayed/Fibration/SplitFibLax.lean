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

universe v₂ u₂ v₁ u₁

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A split fibration over `A`: a displayed category over `A` with a split cleavage. -/
structure SplitFibOb (A : Cat.{v₁, u₁}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{v₂, u₂} A
  /-- Its split cleavage. -/
  [splitFib : SplitFib toDisplayed]

attribute [instance] SplitFibOb.splitFib

-- The universes of the displayed categories only occur in the levels of `SplitFibLax` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The split fibrations, displayed over `Cat`: an object over `A` is a split fibration over
`A`, and a morphism over `u` is a displayed functor over `u`, with no condition on the
cleavages. -/
def SplitFibLax : Displayed Cat.{v₁, u₁} where
  Ob A := SplitFibOb.{v₂, u₂} A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K

/-- The split cleavage of an object of `SplitFibLax`. The instance `SplitFibOb.splitFib` does not
apply to it, since `SplitFibLax.Ob A` is not reducibly `SplitFibOb A`. -/
instance SplitFibLax.splitFib {A : Cat.{v₁, u₁}} (X : SplitFibLax.{v₂, u₂}.Ob A) :
    SplitFib (SplitFibOb.toDisplayed X) :=
  SplitFibOb.splitFib X

/-- The vertical functor forgetting the split cleavage. -/
def SplitFibLax.forget :
    VertFunctor SplitFibLax.{v₂, u₂, v₁, u₁} DisplayedCat.{v₂, u₂, v₁, u₁} where
  obj X := X.toDisplayed
  map H := H

/-- Forgetting the split cleavage is fully faithful, since the morphisms are the same. -/
def SplitFibLax.forgetFullyFaithful : SplitFibLax.forget.{v₂, u₂, v₁, u₁}.FullyFaithful where
  preimage H := H

end Displayed

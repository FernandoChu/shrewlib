import Displayed.Opfibration.Basic
import Displayed.Displayed.DisplayedCat

/-!
# The category of split opfibrations

The split opfibrations form a category displayed over `Cat` (`SplitOpfibCat`): an object over `A`
is a displayed category over `A` with a `SplitOpfib` structure (`SplitOpfibOb`), and a morphism
over `u : A ⟶ B` is any displayed functor over `u` (`DispFunctor`), which need not preserve the
chosen lifts. Its laws hold by `rfl`. Forgetting the opcleavage is a fully faithful vertical
functor into the displayed categories, `SplitOpfibCat.forget : SplitOpfibCat ⟶ DisplayedCat`.

This is not in `Basic.lean` since displayed functors over a functor need the functor laws as rules
(`Rules.Functor`), which should not reach every file using opfibrations.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A split opfibration over `A`: a displayed category over `A` with a split opcleavage. -/
structure SplitOpfibOb (A : Cat.{u, u}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{u, u, u, u} A
  /-- Its split opcleavage. -/
  [splitOpfib : SplitOpfib toDisplayed]

attribute [instance] SplitOpfibOb.splitOpfib

/-- The split opfibrations, displayed over `Cat`: an object over `A` is a split opfibration over
`A`, and a morphism over `u` is a displayed functor over `u`, with no condition on the
opcleavages. -/
def SplitOpfibCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := SplitOpfibOb A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The vertical functor forgetting the split opcleavage. -/
def SplitOpfibCat.forget : VertFunctor SplitOpfibCat.{u} DisplayedCat.{u} where
  obj X := X.toDisplayed
  map H := H
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the split opcleavage is fully faithful, since the morphisms are the same. -/
def SplitOpfibCat.forgetFullyFaithful : SplitOpfibCat.forget.{u}.FullyFaithful where
  preimage H := H
  map_preimage _ := rfl
  preimage_map _ := rfl

end Displayed

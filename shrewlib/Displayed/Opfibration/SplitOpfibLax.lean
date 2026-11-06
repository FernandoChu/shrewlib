import Displayed.Opfibration.Basic
import Displayed.Displayed.DisplayedCat

/-!
# The category of split opfibrations

The split opfibrations form a category displayed over `Cat` (`SplitOpfibLax`): an object over `A`
is a displayed category over `A` with a `SplitOpfib` structure (`SplitOpfibOb`), and a morphism
over `u : A ⟶ B` is any displayed functor over `u` (`DispFunctor`), which need not preserve the
chosen lifts. Its laws hold by `rfl`. Forgetting the opcleavage is a fully faithful vertical
functor into the displayed categories, `SplitOpfibLax.forget : SplitOpfibLax ⟶ DisplayedCat`.

This is not in `Basic.lean` since displayed functors over a functor need the functor laws as rules
(`Rules.Functor`), which should not reach every file using opfibrations.
-/

universe v₁ u₁ v₂ u₂ u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A split opfibration over `A`: a displayed category over `A` with a split opcleavage. -/
structure SplitOpfibOb (A : Cat.{v₁, u₁}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{v₁, u₁, v₂, u₂} A
  /-- Its split opcleavage. -/
  [splitOpfib : SplitOpfib toDisplayed]

attribute [instance] SplitOpfibOb.splitOpfib

/-- The split opfibrations, displayed over `Cat`: an object over `A` is a split opfibration over
`A`, and a morphism over `u` is a displayed functor over `u`, with no condition on the
opcleavages. -/
def SplitOpfibLax : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := SplitOpfibOb.{u, u, u, u} A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K

/-- The split opcleavage of an object of `SplitOpfibLax`. The instance `SplitOpfibOb.splitOpfib`
does not apply to it, since `SplitOpfibLax.Ob A` is not reducibly `SplitOpfibOb A`. -/
instance SplitOpfibLax.splitOpfib {A : Cat.{u, u}} (X : SplitOpfibLax.Ob A) :
    SplitOpfib (SplitOpfibOb.toDisplayed X) :=
  SplitOpfibOb.splitOpfib X

/-- The vertical functor forgetting the split opcleavage. -/
def SplitOpfibLax.forget : VertFunctor SplitOpfibLax.{u} DisplayedCat.{u} where
  obj X := X.toDisplayed
  map H := H

/-- Forgetting the split opcleavage is fully faithful, since the morphisms are the same. -/
def SplitOpfibLax.forgetFullyFaithful : SplitOpfibLax.forget.{u}.FullyFaithful where
  preimage H := H

end Displayed

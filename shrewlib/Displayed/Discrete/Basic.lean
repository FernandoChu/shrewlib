import Displayed.Opfibration.SplitOpfibLax
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Discrete opfibrations

A *discrete opfibration* over `A` (`DiscOpfibOb A`) is a displayed category over `A` with a split
opcleavage whose fibres are discrete categories (Mathlib's `IsDiscrete`): a vertical morphism is an
equality of its endpoints, and there is at most one. Every morphism over `f` out of `x` is then the
chosen lift `olift f x`, followed by a vertical morphism, that is, an equality `push f x = y`.

The discrete opfibrations form a category displayed over `Cat` (`DiscOpfibCat`), with all displayed
functors as morphisms, like the split opfibrations (`SplitOpfibLax`): forgetting the discreteness is
a fully faithful vertical functor `DiscOpfibCat.forget : DiscOpfibCat ⟶ SplitOpfibLax`.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A discrete opfibration over `A`: a displayed category over `A` with a split opcleavage, whose
fibres are discrete. -/
structure DiscOpfibOb (A : Cat.{u, u}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{u, u, u, u} A
  /-- Its split opcleavage. -/
  [splitOpfib : SplitOpfib toDisplayed]
  /-- Its fibres are discrete. -/
  isDiscrete : ∀ a, IsDiscrete (toDisplayed.Fiber a)

attribute [instance] DiscOpfibOb.splitOpfib DiscOpfibOb.isDiscrete

/-- The discrete opfibrations, displayed over `Cat`: an object over `A` is a discrete opfibration
over `A`, and a morphism over `u` is a displayed functor over `u`. -/
def DiscOpfibCat : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := DiscOpfibOb A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The split opcleavage of an object of `DiscOpfibCat`. The instance `DiscOpfibOb.splitOpfib` does
not apply to it, since `DiscOpfibCat.Ob A` is not reducibly `DiscOpfibOb A`. -/
instance DiscOpfibCat.splitOpfib {A : Cat.{u, u}} (X : DiscOpfibCat.Ob A) :
    SplitOpfib (DiscOpfibOb.toDisplayed X) :=
  DiscOpfibOb.splitOpfib X

/-- The vertical functor forgetting the discreteness. -/
def DiscOpfibCat.forget : VertFunctor DiscOpfibCat.{u} SplitOpfibLax.{u} where
  obj X := { toDisplayed := X.toDisplayed, splitOpfib := X.splitOpfib }
  map H := H
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting the discreteness is fully faithful, since the morphisms are the same. -/
def DiscOpfibCat.forgetFullyFaithful : DiscOpfibCat.forget.{u}.FullyFaithful where
  preimage H := H
  map_preimage _ := rfl
  preimage_map _ := rfl

end Displayed

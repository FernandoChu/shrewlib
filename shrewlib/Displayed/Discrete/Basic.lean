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

The reindexing of a discrete opfibration is a discrete opfibration: its fibres are those of the
discrete opfibration. So `DiscOpfibCat` is a split fibration over `Cat`, with the reindexing and the
chosen lifts of `DisplayedCat` (`DiscOpfibCat.splitFibCat`), and forgetting the discreteness
preserves the chosen lifts (`DiscOpfibCat.forgetCartesian`).
-/

universe v₂ u₂ v₁ u₁

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A discrete opfibration over `A`: a displayed category over `A` with a split opcleavage, whose
fibres are discrete. -/
structure DiscOpfibOb (A : Cat.{v₁, u₁}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{v₂, u₂} A
  /-- Its split opcleavage. -/
  [splitOpfib : SplitOpfib toDisplayed]
  /-- Its fibres are discrete. -/
  isDiscrete : ∀ a, IsDiscrete (toDisplayed.Fiber a)

attribute [instance] DiscOpfibOb.splitOpfib DiscOpfibOb.isDiscrete

-- The universes of the displayed categories only occur in the levels of `DiscOpfibCat` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The discrete opfibrations, displayed over `Cat`: an object over `A` is a discrete opfibration
over `A`, and a morphism over `u` is a displayed functor over `u`. -/
def DiscOpfibCat : Displayed Cat.{v₁, u₁} where
  Ob A := DiscOpfibOb.{v₂, u₂} A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K

/-- The split opcleavage of an object of `DiscOpfibCat`. The instance `DiscOpfibOb.splitOpfib` does
not apply to it, since `DiscOpfibCat.Ob A` is not reducibly `DiscOpfibOb A`. -/
instance DiscOpfibCat.splitOpfib {A : Cat.{v₁, u₁}} (X : DiscOpfibCat.{v₂, u₂}.Ob A) :
    SplitOpfib (DiscOpfibOb.toDisplayed X) :=
  DiscOpfibOb.splitOpfib X

/-- The vertical functor forgetting the discreteness. -/
def DiscOpfibCat.forget :
    VertFunctor DiscOpfibCat.{v₂, u₂, v₁, u₁} SplitOpfibLax.{v₂, u₂, v₁, u₁} where
  obj X := { toDisplayed := X.toDisplayed, splitOpfib := X.splitOpfib }
  map H := H

/-- Forgetting the discreteness is fully faithful, since the morphisms are the same. -/
def DiscOpfibCat.forgetFullyFaithful : DiscOpfibCat.forget.{v₂, u₂, v₁, u₁}.FullyFaithful where
  preimage H := H

/-! ## Reindexing -/

namespace DiscOpfibCat

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : DiscOpfibOb.{v₂, u₂} B)

/-- The reindexing of a discrete opfibration along `u`, whose fibres are those of `X`. -/
def pull : DiscOpfibOb.{v₂, u₂} A where
  toDisplayed := DisplayedCat.pull u X.toDisplayed
  isDiscrete a := X.isDiscrete (u.toFunctor.obj a)

/-- The chosen lift `pull u X ⟶[u] X`: that of `DisplayedCat`. -/
def clift : DiscOpfibCat.Hom u (pull u X) X := DisplayedCat.clift u X.toDisplayed

/-- The chosen lift is cartesian, since it is in `DisplayedCat` and the morphisms are the same. -/
def isCartesianClift : IsCartesian (D := DiscOpfibCat) (clift u X) :=
  let H := DisplayedCat.isCartesianClift u X.toDisplayed
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end DiscOpfibCat

/-- **`DiscOpfibCat` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`DisplayedCat`. -/
instance DiscOpfibCat.preSplitFibCat : PreSplitFib DiscOpfibCat.{v₂, u₂, v₁, u₁} where
  pull u X := DiscOpfibCat.pull u X
  clift u X := DiscOpfibCat.clift u X
  isCartesianClift u X := DiscOpfibCat.isCartesianClift u X

instance DiscOpfibCat.splitFibCat : SplitFib DiscOpfibCat.{v₂, u₂, v₁, u₁} := {}

/-- **Forgetting the discreteness preserves the chosen lifts**: it is a cartesian functor into
`SplitOpfibLax`. -/
def DiscOpfibCat.forgetCartesian :
    CartesianFunctor (𝟭 Cat.{v₁, u₁}) DiscOpfibCat.{v₂, u₂, v₁, u₁}
      SplitOpfibLax.{v₂, u₂, v₁, u₁} where
  toPre := { toDispFunctor := DiscOpfibCat.forget }

end Displayed

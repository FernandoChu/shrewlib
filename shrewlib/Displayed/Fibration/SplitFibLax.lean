import Displayed.Fibration.Basic
import Displayed.Displayed.DisplayedCat
import Displayed.Fibration.CartesianFunctor
import Displayed.Fibration.DisplayedCat

/-!
# The category of split fibrations

The split fibrations form a category displayed over `Cat` (`SplitFibLax`): an object over `A` is a
displayed category over `A` with a `SplitFib` structure (`SplitFibOb`), and a morphism over
`u : A ⟶ B` is any displayed functor over `u` (`DispFunctor`), which need not preserve the chosen
lifts. Its laws hold by `rfl`. Forgetting the cleavage is a fully faithful vertical functor into
the displayed categories, `SplitFibLax.forget : SplitFibLax ⟶ DisplayedCat`.

The reindexing `DisplayedCat.pull u E` of a fibration `E` along `u` is a fibration, pulling back
along `u f`, and it is split if `E` is (`DisplayedCat.pullSplitFib`). So `SplitFibLax` is a split
fibration over `Cat`, with the reindexing and the chosen lifts of `DisplayedCat`, whose laws hold by
`rfl` (`SplitFibLax.splitFibCat`), and forgetting the cleavage preserves the chosen lifts
(`SplitFibLax.forgetCartesian`).

This is the dual of `Opfibration/SplitOpfibLax.lean`, and is not in `Basic.lean` for the same
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

/-! ## Reindexing -/

namespace DisplayedCat

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (E : Displayed.{v₂, u₂} B)

/-- The chosen lift of `u f` at `y` is cartesian in the reindexing of `E` along `u`: a morphism
over `g ≫ f` there is one over `u g ≫ u f` in `E`, factored in `E`. -/
def isCartesianPullClift [Fib E] {a a' : A} (f : a ⟶ a') (y : (pull u E).Ob a') :
    IsCartesian (D := pull u E) (x := E.pull (u.toFunctor.map f) y)
      (E.clift (u.toFunctor.map f) y) where
  lift g _ χ := (E.isCartesianClift (u.toFunctor.map f) y).lift (u.toFunctor.map g) χ
  lift_fac g _ χ := (E.isCartesianClift (u.toFunctor.map f) y).lift_fac (u.toFunctor.map g) χ
  lift_uniq ψ hψ := (E.isCartesianClift (u.toFunctor.map f) y).lift_uniq ψ hψ

/-- **The reindexing of a fibration is a fibration**, pulling back along `u f`. -/
@[instance_reducible]
instance pullFib [Fib E] : Fib (pull u E) where
  pull f y := E.pull (u.toFunctor.map f) y
  clift f y := E.clift (u.toFunctor.map f) y
  isCartesianClift f y := isCartesianPullClift u E f y

@[instance_reducible]
instance pullPreSplitFib [PreSplitFib E] : PreSplitFib (pull u E) where

/-- **The reindexing of a split fibration is split**, with laws by `rfl`. -/
instance pullSplitFib [SplitFib E] : SplitFib (pull u E) := {}

end DisplayedCat

namespace SplitFibLax

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : SplitFibOb.{v₂, u₂} B)

/-- The reindexing of a split fibration along `u`, a split fibration. -/
def pull : SplitFibOb.{v₂, u₂} A := ⟨DisplayedCat.pull u X.toDisplayed⟩

/-- The chosen lift `pull u X ⟶[u] X`: that of `DisplayedCat`. -/
def clift : SplitFibLax.Hom u (pull u X) X := DisplayedCat.clift u X.toDisplayed

/-- The chosen lift is cartesian, since it is in `DisplayedCat` and the morphisms are the same. -/
def isCartesianClift : IsCartesian (D := SplitFibLax) (clift u X) :=
  let H := DisplayedCat.isCartesianClift u X.toDisplayed
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end SplitFibLax

/-- **`SplitFibLax` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`DisplayedCat`. -/
instance SplitFibLax.preSplitFibCat : PreSplitFib SplitFibLax.{v₂, u₂, v₁, u₁} where
  pull u X := SplitFibLax.pull u X
  clift u X := SplitFibLax.clift u X
  isCartesianClift u X := SplitFibLax.isCartesianClift u X

instance SplitFibLax.splitFibCat : SplitFib SplitFibLax.{v₂, u₂, v₁, u₁} := {}

/-- **Forgetting the cleavage preserves the chosen lifts**: it is a cartesian functor into
`DisplayedCat`. -/
def SplitFibLax.forgetCartesian :
    CartesianFunctor (𝟭 Cat.{v₁, u₁}) SplitFibLax.{v₂, u₂, v₁, u₁}
      DisplayedCat.{v₂, u₂, v₁, u₁} where
  toPre := { toDispFunctor := SplitFibLax.forget }

end Displayed

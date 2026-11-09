import Displayed.Opfibration.Basic
import Displayed.Displayed.DisplayedCat
import Displayed.Fibration.CartesianFunctor
import Displayed.Fibration.DisplayedCat

/-!
# The category of split opfibrations

The split opfibrations form a category displayed over `Cat` (`SplitOpfibLax`): an object over `A`
is a displayed category over `A` with a `SplitOpfib` structure (`SplitOpfibOb`), and a morphism
over `u : A ⟶ B` is any displayed functor over `u` (`DispFunctor`), which need not preserve the
chosen lifts. Its laws hold by `rfl`. Forgetting the opcleavage is a fully faithful vertical
functor into the displayed categories, `SplitOpfibLax.forget : SplitOpfibLax ⟶ DisplayedCat`.

The reindexing `DisplayedCat.pull u E` of an opfibration `E` along `u` is an opfibration, pushing
forward along `u f`, and it is split if `E` is (`DisplayedCat.pullSplitOpfib`). So `SplitOpfibLax`
is a split fibration over `Cat`, with the reindexing and the chosen lifts of `DisplayedCat`, whose
laws hold by `rfl` (`SplitOpfibLax.splitFibCat`), and forgetting the opcleavage preserves the chosen
lifts (`SplitOpfibLax.forgetCartesian`).

This is not in `Basic.lean` since displayed functors over a functor need the functor laws as rules
(`Rules.Functor`), which should not reach every file using opfibrations.
-/

universe v₂ u₂ v₁ u₁

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- A split opfibration over `A`: a displayed category over `A` with a split opcleavage. -/
structure SplitOpfibOb (A : Cat.{v₁, u₁}) where
  /-- The displayed category. -/
  toDisplayed : Displayed.{v₂, u₂} A
  /-- Its split opcleavage. -/
  [splitOpfib : SplitOpfib toDisplayed]

attribute [instance] SplitOpfibOb.splitOpfib

-- The universes of the displayed categories only occur in the levels of `SplitOpfibLax` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The split opfibrations, displayed over `Cat`: an object over `A` is a split opfibration over
`A`, and a morphism over `u` is a displayed functor over `u`, with no condition on the
opcleavages. -/
def SplitOpfibLax : Displayed Cat.{v₁, u₁} where
  Ob A := SplitOpfibOb.{v₂, u₂} A
  Hom u X Y := DispFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := DispFunctor.id X.toDisplayed
  comp H K := H.comp K

/-- The split opcleavage of an object of `SplitOpfibLax`. The instance `SplitOpfibOb.splitOpfib`
does not apply to it, since `SplitOpfibLax.Ob A` is not reducibly `SplitOpfibOb A`. -/
instance SplitOpfibLax.splitOpfib {A : Cat.{v₁, u₁}} (X : SplitOpfibLax.{v₂, u₂}.Ob A) :
    SplitOpfib (SplitOpfibOb.toDisplayed X) :=
  SplitOpfibOb.splitOpfib X

/-- The vertical functor forgetting the split opcleavage. -/
def SplitOpfibLax.forget :
    VertFunctor SplitOpfibLax.{v₂, u₂, v₁, u₁} DisplayedCat.{v₂, u₂, v₁, u₁} where
  obj X := X.toDisplayed
  map H := H

/-- Forgetting the split opcleavage is fully faithful, since the morphisms are the same. -/
def SplitOpfibLax.forgetFullyFaithful : SplitOpfibLax.forget.{v₂, u₂, v₁, u₁}.FullyFaithful where
  preimage H := H

/-! ## Reindexing -/

namespace DisplayedCat

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (E : Displayed.{v₂, u₂} B)

/-- The chosen lift of `u f` at `x` is opcartesian in the reindexing of `E` along `u`: a morphism
over `f ≫ g` there is one over `u f ≫ u g` in `E`, factored in `E`. -/
def isOpcartesianPullOlift [Opfib E] {a a' : A} (f : a ⟶ a') (x : (pull u E).Ob a) :
    IsOpcartesian (D := pull u E) (y := E.push (u.toFunctor.map f) x)
      (E.olift (u.toFunctor.map f) x) where
  desc g _ χ := (E.isOpcartesianOlift (u.toFunctor.map f) x).desc (u.toFunctor.map g) χ
  desc_fac g _ χ := (E.isOpcartesianOlift (u.toFunctor.map f) x).desc_fac (u.toFunctor.map g) χ
  desc_uniq ψ hψ := (E.isOpcartesianOlift (u.toFunctor.map f) x).desc_uniq ψ hψ

/-- **The reindexing of an opfibration is an opfibration**, pushing forward along `u f`. -/
@[instance_reducible]
instance pullOpfib [Opfib E] : Opfib (pull u E) where
  push f x := E.push (u.toFunctor.map f) x
  olift f x := E.olift (u.toFunctor.map f) x
  isOpcartesianOlift f x := isOpcartesianPullOlift u E f x

@[instance_reducible]
instance pullPreSplitOpfib [PreSplitOpfib E] : PreSplitOpfib (pull u E) where

/-- **The reindexing of a split opfibration is split**, with laws by `rfl`. -/
instance pullSplitOpfib [SplitOpfib E] : SplitOpfib (pull u E) := {}

end DisplayedCat

namespace SplitOpfibLax

variable {A B : Cat.{v₁, u₁}} (u : A ⟶ B) (X : SplitOpfibOb.{v₂, u₂} B)

/-- The reindexing of a split opfibration along `u`, a split opfibration. -/
def pull : SplitOpfibOb.{v₂, u₂} A := ⟨DisplayedCat.pull u X.toDisplayed⟩

/-- The chosen lift `pull u X ⟶[u] X`: that of `DisplayedCat`. -/
def clift : SplitOpfibLax.Hom u (pull u X) X := DisplayedCat.clift u X.toDisplayed

/-- The chosen lift is cartesian, since it is in `DisplayedCat` and the morphisms are the same. -/
def isCartesianClift : IsCartesian (D := SplitOpfibLax) (clift u X) :=
  let H := DisplayedCat.isCartesianClift u X.toDisplayed
  { lift := fun g _ χ => H.lift g χ
    lift_fac := fun g _ χ => H.lift_fac g χ
    lift_uniq := fun ψ hψ => H.lift_uniq ψ hψ }

end SplitOpfibLax

/-- **`SplitOpfibLax` is a split fibration over `Cat`**, with the reindexing and the chosen lifts of
`DisplayedCat`. -/
instance SplitOpfibLax.preSplitFibCat : PreSplitFib SplitOpfibLax.{v₂, u₂, v₁, u₁} where
  pull u X := SplitOpfibLax.pull u X
  clift u X := SplitOpfibLax.clift u X
  isCartesianClift u X := SplitOpfibLax.isCartesianClift u X

instance SplitOpfibLax.splitFibCat : SplitFib SplitOpfibLax.{v₂, u₂, v₁, u₁} := {}

/-- **Forgetting the opcleavage preserves the chosen lifts**: it is a cartesian functor into
`DisplayedCat`. -/
def SplitOpfibLax.forgetCartesian :
    CartesianFunctor (𝟭 Cat.{v₁, u₁}) SplitOpfibLax.{v₂, u₂, v₁, u₁}
      DisplayedCat.{v₂, u₂, v₁, u₁} where
  toPre := { toDispFunctor := SplitOpfibLax.forget }

end Displayed

import Displayed.Opfibration.SplitOpfibLax
import Displayed.Opfibration.OpcartesianFunctor

/-!
# The category of split opfibrations and opcartesian functors

The split opfibrations form a category displayed over `Cat` with the opcartesian functors as
morphisms (`SplitOpfibStr`): an object over `A : Cat.{v₁, u₁}` is a split opfibration over `A`
whose displayed categories are in `Displayed.{v₂, u₂}` (`SplitOpfibOb`),
and a morphism over `u : A ⟶ B` is a displayed functor over `u` sending the chosen lifts to the
chosen lifts (`OpcartesianFunctor`). Its laws hold by `rfl`.

Forgetting that the chosen lifts are preserved is a faithful vertical functor
`SplitOpfibStr.forget : SplitOpfibStr ⟶ SplitOpfibLax`, the identity on objects.
-/

universe v₂ u₂ v₁ u₁

open CategoryTheory

namespace Displayed

open scoped Displayed

-- The universes of the displayed categories only occur in the levels of `SplitOpfibStr` through
-- the `max` of the levels of their objects and morphisms.
set_option linter.checkUnivs false in
/-- The split opfibrations, displayed over `Cat`: an object over `A` is a split opfibration over
`A`, and a morphism over `u` is an opcartesian functor over `u`. -/
def SplitOpfibStr : Displayed Cat.{v₁, u₁} where
  Ob A := SplitOpfibOb.{v₂, u₂} A
  Hom u X Y := OpcartesianFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := OpcartesianFunctor.id X.toDisplayed
  comp H K := H.comp K

/-- The split opcleavage of an object of `SplitOpfibStr`. The instance `SplitOpfibOb.splitOpfib`
does not apply to it, since `SplitOpfibStr.Ob A` is not reducibly `SplitOpfibOb A`. -/
instance SplitOpfibStr.splitOpfib {A : Cat.{v₁, u₁}} (X : SplitOpfibStr.{v₂, u₂}.Ob A) :
    SplitOpfib (SplitOpfibOb.toDisplayed X) :=
  SplitOpfibOb.splitOpfib X

/-- The vertical functor forgetting that the chosen lifts are preserved. -/
def SplitOpfibStr.forget :
    VertFunctor SplitOpfibStr.{v₂, u₂, v₁, u₁} SplitOpfibLax.{v₂, u₂, v₁, u₁} where
  obj X := X
  map H := H.toDispFunctor

/-- Forgetting that the chosen lifts are preserved is faithful. -/
theorem SplitOpfibStr.forget_map_injective {A B : Cat.{v₁, u₁}} {u : A ⟶ B}
    {X : SplitOpfibOb.{v₂, u₂} A} {Y : SplitOpfibOb.{v₂, u₂} B}
    {H K : SplitOpfibStr.{v₂, u₂}.Hom u X Y}
    (h : SplitOpfibStr.forget.map H = SplitOpfibStr.forget.map K) : H = K :=
  OpcartesianFunctor.ext (D := X.toDisplayed) (E := Y.toDisplayed) h

end Displayed

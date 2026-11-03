import Displayed.Opfibration.SplitOpfibLax
import Displayed.Opfibration.OpcartesianFunctor

/-!
# The category of split opfibrations and opcartesian functors

The split opfibrations form a category displayed over `Cat` with the opcartesian functors as
morphisms (`SplitOpfibStr`): an object over `A` is a split opfibration over `A` (`SplitOpfibOb`),
and a morphism over `u : A ⟶ B` is a displayed functor over `u` sending the chosen lifts to the
chosen lifts (`OpcartesianFunctor`). Its laws hold by `rfl`.

Forgetting that the chosen lifts are preserved is a faithful vertical functor
`SplitOpfibStr.forget : SplitOpfibStr ⟶ SplitOpfibLax`, the identity on objects.
-/

universe u

open CategoryTheory

namespace Displayed

open scoped Displayed

/-- The split opfibrations, displayed over `Cat`: an object over `A` is a split opfibration over
`A`, and a morphism over `u` is an opcartesian functor over `u`. -/
def SplitOpfibStr : Displayed.{u, u + 1, u, u + 1} Cat.{u, u} where
  Ob A := SplitOpfibOb A
  Hom u X Y := OpcartesianFunctor u.toFunctor X.toDisplayed Y.toDisplayed
  id X := OpcartesianFunctor.id X.toDisplayed
  comp H K := H.comp K
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The split opcleavage of an object of `SplitOpfibStr`. The instance `SplitOpfibOb.splitOpfib`
does not apply to it, since `SplitOpfibStr.Ob A` is not reducibly `SplitOpfibOb A`. -/
instance SplitOpfibStr.splitOpfib {A : Cat.{u, u}} (X : SplitOpfibStr.Ob A) :
    SplitOpfib (SplitOpfibOb.toDisplayed X) :=
  SplitOpfibOb.splitOpfib X

/-- The vertical functor forgetting that the chosen lifts are preserved. -/
def SplitOpfibStr.forget : VertFunctor SplitOpfibStr.{u} SplitOpfibLax.{u} where
  obj X := X
  map H := H.toDispFunctor
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Forgetting that the chosen lifts are preserved is faithful. -/
theorem SplitOpfibStr.forget_map_injective {A B : Cat.{u, u}} {u : A ⟶ B} {X : SplitOpfibOb A}
    {Y : SplitOpfibOb B} {H K : SplitOpfibStr.Hom u X Y}
    (h : SplitOpfibStr.forget.map H = SplitOpfibStr.forget.map K) : H = K :=
  OpcartesianFunctor.ext (D := X.toDisplayed) (E := Y.toDisplayed) h

end Displayed

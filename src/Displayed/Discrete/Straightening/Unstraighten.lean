import Displayed.Discrete.Basic
import Displayed.Discrete.Straightening.IDisc
import Displayed.Opfibration.Straightening.Unstraighten

/-!
# Unstraightening functors into discrete categories

The unstraightening `∫ F` of a functor `F : A ⥤ Cat` into discrete categories has discrete fibres
(`isDiscrete_unstraighten`): a vertical morphism `x ⟶ y` is a morphism `F (𝟙 a) x ⟶ y`, that is
`x ⟶ y`, of the discrete category `F a`. So it is a discrete opfibration (`unstraightenObj`), whose
morphisms `x ⟶[f] y` are the morphisms `F f x ⟶ y` of `F a'`, which exist exactly when
`F f x = y`.

The unstraightening functor `unstraighten : IDisc ⟶ DiscOpfibCat` is that of the split
opfibrations, restricted: followed by forgetting the discreteness, it is `IDisc.forget` followed by
the unstraightening of the split opfibrations (`unstraighten_comp_forget`, by `rfl`). It is fully
faithful, with the inverse on morphisms of the unstraightening of the split opfibrations, since
the morphisms are the same.
-/

universe u

namespace Displayed.Discrete.Straightening

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- The fibres of the unstraightening of a functor `F : A ⥤ Cat` into discrete categories are
discrete: a vertical morphism `x ⟶ y` is a morphism `F (𝟙 a) x ⟶ y`, that is `x ⟶ y`, of the
discrete category `F a`. -/
theorem isDiscrete_unstraighten {A : Cat.{u, u}} (F : A ⥤ Cat.{u, u}) [∀ a, IsDiscrete (F.obj a)]
    (a : A) : IsDiscrete ((∫ F).Fiber a) where
  subsingleton x y := IsDiscrete.subsingleton (C := F.obj a) x y
  eq_of_hom φ := IsDiscrete.eq_of_hom (C := F.obj a) φ

/-- **The unstraightening of a functor into discrete categories**, a discrete opfibration: its
unstraightening as a functor into `Cat`. -/
def unstraightenObj {A : Cat.{u, u}} (X : IDiscOb A) : DiscOpfibOb A where
  toDisplayed := ∫ X.toFunctor
  splitOpfib := unstraightenSplitOpfib X.toFunctor
  isDiscrete := @isDiscrete_unstraighten _ X.toFunctor X.isDiscrete

/-- **The unstraightening**, into the discrete opfibrations: `X` goes to `∫ X`, and a lax
transformation over `u` to the induced displayed functor. -/
def unstraighten : VertFunctor IDisc.{u} DiscOpfibCat.{u} where
  obj X := unstraightenObj X
  map {_ _ u _ _} α := unstraightenMap (u := u.toFunctor) α
  map_id _ := rfl
  map_comp _ _ := DispFunctor.ext (fun _ => rfl) fun _ => HEq.rfl

/-- The unstraightening, followed by forgetting the discreteness, is the inclusion into the
indexed categories followed by their unstraightening. -/
theorem unstraighten_comp_forget :
    unstraighten.{u} ⋙ᵥ DiscOpfibCat.forget =
      IDisc.forget.toDispFunctor ⋙ᵥ Opfibration.Straightening.unstraighten :=
  rfl

/-- **The unstraightening is fully faithful**: displayed functors between unstraightenings over `u`
are lax transformations, as for the split opfibrations. -/
def unstraightenFullyFaithful : unstraighten.{u}.FullyFaithful where
  preimage H := unstraightenPreimage H
  map_preimage H := unstraightenMap_preimage H
  preimage_map α := unstraightenPreimage_map α

end Displayed.Discrete.Straightening

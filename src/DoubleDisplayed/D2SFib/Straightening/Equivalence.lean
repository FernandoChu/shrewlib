import DoubleDisplayed.D2SFib.Straightening.Straighten
import DoubleDisplayed.D2SFib.Straightening.Unstraighten
import DoubleDisplayed.D2SFib.Straightening.Counit

/-!
# Straightening–unstraightening for D2SFibs: `Functor(∫(Bᵈᵒ), Cat) ≌ D2SFib(A, B)`

Straightening–unstraightening for D2SFibs, in the displayed setting: the category of functors
from the total category of the dual opfibration of `B` into `Cat` is equivalent to the category of
dependent 2-sided split fibrations over `B`.

The two functors are `unstraighten` (`Φ`) and `straighten` (`Ψ`). This file supplies the unit
`𝟭 ≅ Φ ⋙ Ψ`, and assembles it with the counit `Ψ ⋙ Φ ≅ 𝟭` of `Counit.lean`.

The fiber of `Unstraightening F` over `b` is `F.obj ⟨a, b⟩` on the nose, so the components of the
unit are identity functors. Its naturality is the factorization of a morphism of `∫(Bᵈᵒ)` into a
chosen horizontal and a chosen vertical morphism, `Unstraightening.map_eq`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

noncomputable section

namespace Unstraightening

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) {a : A}

/-- The unit component, forward direction: the fiber of `Unstraightening F` over `b` is
`F.obj ⟨a, b⟩`. -/
def unitFiberFunctor (b : B.Ob a) : F.obj (B.dualOp.tot b) ⥤ (Unstraightening F).Fiber b where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component, backward direction. -/
def unitFiberInv (b : B.Ob a) : (Unstraightening F).Fiber b ⥤ F.obj (B.dualOp.tot b) where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component as an isomorphism of `Cat`. -/
def unitFiberIso (b : B.Ob a) : F.obj (B.dualOp.tot b) ≅ Cat.of ((Unstraightening F).Fiber b) where
  hom := (unitFiberFunctor F b).toCatHom
  inv := (unitFiberInv F b).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end Unstraightening

/-- **The unit at `F`**: `F ≅ Ψ (Φ F)`, by identity functors. -/
def unitApp (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : F ≅ straightenObj (Unstraightening F) :=
  NatIso.ofComponents (fun x => Unstraightening.unitFiberIso F x.2) (fun {x _} u => by
    apply Cat.ext
    change (F.map u).toFunctor ⋙ Unstraightening.unitFiberFunctor F _
      = Unstraightening.unitFiberFunctor F x.2
        ⋙ (pushFunctor (C := Unstraightening F) u.base x.2
          ⋙ pullFunctor (C := Unstraightening F) u.fiber)
    rw [Unstraightening.map_eq F u]
    exact Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))

/-- **The unit**: `𝟭 ≅ Φ ⋙ Ψ`. -/
def unitIso : 𝟭 (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≅ unstraighten ⋙ straighten :=
  NatIso.ofComponents (fun F => unitApp F) (fun _ =>
    NatTrans.ext (funext fun _ => Cat.ext (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))))

end

/-- **Straightening–unstraightening for D2SFibs**: the unstraightening `Φ = unstraighten` and the
fiberwise functor `Ψ = straighten` are mutually inverse equivalences between functors
`∫(Bᵈᵒ) ⥤ Cat` and dependent 2-sided split fibrations over `B`. -/
noncomputable def straighteningEquiv (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B :=
  CategoryTheory.Equivalence.mk unstraighten straighten unitIso counitIso

@[simp] theorem straighteningEquiv_functor (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (straighteningEquiv.{v₁, u₁, v₂, u₂, v₃, u₃} B).functor = unstraighten := rfl

@[simp] theorem straighteningEquiv_inverse (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (straighteningEquiv.{v₁, u₁, v₂, u₂, v₃, u₃} B).inverse = straighten := rfl

end DoubleDisplayed.D2SFib.Straightening

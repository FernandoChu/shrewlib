import Nfib.D2SFib.ToFunctor
import Nfib.D2SFib.Grothendieck
import Nfib.D2SFib.Counit

/-!
# The main equivalence `Functor(∫(Bᵈᵒ), Cat) ≌ D2SFib(A, B)`

This file states and proves the displayed adaptation of Proposition `prop:d2sfibequiv`: the category
of functors from the total category of the dual opfibration of `B` into `Cat` is equivalent to the
category of dependent 2-sided split fibrations over `B`.

The two functors are `D2SGCFunctor` (`Φ`, milestone **M8**) and `toFunctor` (`Ψ`, milestone
**M7**). This file supplies the unit `𝟭 ≅ Φ ⋙ Ψ`, and assembles it with the counit `Ψ ⋙ Φ ≅ 𝟭` of
`Counit.lean` (milestone **M9**).

The fiber of `D2SGC F` over `b` is `F.obj ⟨a, b⟩` on the nose, so the components of the unit are
identity functors. Its naturality is the factorization of a morphism of `∫(Bᵈᵒ)` into a chosen
horizontal and a chosen vertical morphism, `D2SGC.map_eq`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

noncomputable section

namespace D2SGC

variable (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) {a : A}

/-- The unit component, forward direction: the fiber of `D2SGC F` over `b` is `F.obj ⟨a, b⟩`. -/
def unitFiberFunctor (b : B.Ob a) : F.obj (B.dualOp.tot b) ⥤ (D2SGC F).Fiber b where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component, backward direction. -/
def unitFiberInv (b : B.Ob a) : (D2SGC F).Fiber b ⥤ F.obj (B.dualOp.tot b) where
  obj c := c
  map θ := θ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The unit component as an isomorphism of `Cat`. -/
def unitFiberIso (b : B.Ob a) : F.obj (B.dualOp.tot b) ≅ Cat.of ((D2SGC F).Fiber b) where
  hom := (unitFiberFunctor F b).toCatHom
  inv := (unitFiberInv F b).toCatHom
  hom_inv_id := rfl
  inv_hom_id := rfl

end D2SGC

/-- **The unit at `F`**: `F ≅ Ψ (Φ F)`, by identity functors. -/
def unitApp (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) : F ≅ toFunctorObj (D2SGC F) :=
  NatIso.ofComponents (fun x => D2SGC.unitFiberIso F x.2) (fun {x _} u => by
    apply Cat.ext
    change (F.map u).toFunctor ⋙ D2SGC.unitFiberFunctor F _
      = D2SGC.unitFiberFunctor F x.2
        ⋙ (pushFunctor (C := D2SGC F) u.base x.2 ⋙ pullFunctor (C := D2SGC F) u.fiber)
    rw [D2SGC.map_eq F u]
    exact Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))

/-- **The unit**: `𝟭 ≅ Φ ⋙ Ψ`. -/
def unitIso : 𝟭 (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≅ D2SGCFunctor ⋙ toFunctor :=
  NatIso.ofComponents (fun F => unitApp F) (fun _ =>
    NatTrans.ext (funext fun _ => Cat.ext (Functor.ext (fun _ => rfl) (fun _ _ _ => rfl))))

end

/-- **Main theorem** (displayed adaptation of Proposition `prop:d2sfibequiv`): the D2S Grothendieck
construction `Φ = D2SGCFunctor` and the fiberwise functor `Ψ = toFunctor` are mutually inverse
equivalences between functors `∫(Bᵈᵒ) ⥤ Cat` and dependent 2-sided split fibrations over `B`. -/
noncomputable def d2sfibEquivalence (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B :=
  CategoryTheory.Equivalence.mk D2SGCFunctor toFunctor unitIso counitIso

@[simp] theorem d2sfibEquivalence_functor (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (d2sfibEquivalence.{v₁, u₁, v₂, u₂, v₃, u₃} B).functor = D2SGCFunctor := rfl

@[simp] theorem d2sfibEquivalence_inverse (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (d2sfibEquivalence.{v₁, u₁, v₂, u₂, v₃, u₃} B).inverse = toFunctor := rfl

end Nfib

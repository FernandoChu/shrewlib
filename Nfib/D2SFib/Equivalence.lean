import Nfib.D2SFib.ToFunctor
import Nfib.D2SFib.Grothendieck
import Nfib.D2SFib.Counit

/-!
# The main equivalence `Functor(∫(Bᵈᵒ), Cat) ≌ D2SFib(A, B)`

This file states and proves the displayed adaptation of Proposition `prop:d2sfibequiv`: the category
of functors from the total category of the dual opfibration of `B` into `Cat` is equivalent to the
category of dependent 2-sided split fibrations over `B`.

The two functors are `D2SGCFunctor` (`Φ`, milestone **M8**) and `toFunctor` (`Ψ`, milestone
**M7**). This file supplies the unit `𝟭 ≅ Φ ⋙ Ψ` and the counit `Ψ ⋙ Φ ≅ 𝟭` and assembles them
(milestone **M9**).

The universes are pinned so that the fibers `E.C.Fiber b` of an `E : D2SFibCat.{…, v₃, u₃} B` are
categories with objects in `Type u₃` and homs in `Type v₃`, i.e. objects of `Cat.{v₃, u₃}`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A} [SplitOpfib B]

/-! ### The unit -/

/-- **M9's unit at `F`**: `F ≅ Ψ (Φ F)`. Identity on objects; on morphisms it is the
`eqToHom`-conjugation of `D2SGC.unitFiberIso`, and its naturality is `D2SGC.unitNat_eq`. -/
noncomputable def unitApp (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) :
    F ≅ toFunctorObj (D2SGC F) :=
  NatIso.ofComponents (fun x => D2SGC.unitFiberIso F x.2)
    (fun {_ _} u => Cat.ext (D2SGC.unitFiber_naturality F u))

@[simp] theorem unitApp_hom_app (F : B.dualOp.Total ⥤ Cat.{v₃, u₃}) (x : B.dualOp.Total) :
    ((unitApp F).hom.app x).toFunctor = D2SGC.unitFiberFunctor F x.2 := rfl

@[simp] theorem toFunctor_map_D2SGCMap_app {F F' : B.dualOp.Total ⥤ Cat.{v₃, u₃}} (κ : F ⟶ F')
    (x : B.dualOp.Total) :
    ((toFunctor.map (D2SGCFunctor.map κ)).app x).toFunctor
      = (D2SGCMap κ).toVertFunctor.fiber x.2 := rfl

/-- **M9's unit**: `𝟭 ≅ Φ ⋙ Ψ`. -/
noncomputable def unitIso :
    𝟭 (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≅ D2SGCFunctor ⋙ toFunctor :=
  NatIso.ofComponents (fun F => unitApp F) (fun {F F'} κ => by
    refine NatTrans.ext ?_
    funext x
    simp only [NatTrans.comp_app, Functor.id_map]
    refine Cat.ext (CategoryTheory.Functor.hext (fun _ => rfl) (fun c c' θ => ?_))
    simp only [Cat.Hom.comp_toFunctor, Functor.comp_map, unitApp_hom_app,
      toFunctor_map_D2SGCMap_app]
    refine (D2SGC.unitFiberFunctor_map_heq (B := B) F' x.2 _).trans (HEq.symm ?_)
    refine (D2SGC.gmap_heq_map κ _).trans ?_
    refine (D2SGC.kapp_map_heq κ rfl
      (D2SGC.fmap_congr_obj F (D2SGC.dualHoriz_id_eq (B := B) x.2).symm c')
      (D2SGC.unitFiberFunctor_map_heq (B := B) F x.2 θ)).trans ?_
    refine HEq.trans (heq_of_eq (Functor.congr_hom
      (D2SGC.kapp_naturality κ (dualHoriz (B := B) (𝟙 x.1) x.2)) θ)) ?_
    simp
    rfl)

/-! ### The main theorem: `Φ` and `Ψ` are mutually inverse -/

/-- **Main theorem** (displayed adaptation of Proposition `prop:d2sfibequiv`): the D2S Grothendieck
construction `Φ = D2SGCFunctor` and the fiberwise functor `Ψ = toFunctor` are mutually inverse
equivalences between functors `∫(Bᵈᵒ) ⥤ Cat` and dependent 2-sided split fibrations over `B`. -/
noncomputable def d2sfibEquivalence (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (B.dualOp.Total ⥤ Cat.{v₃, u₃}) ≌ D2SFibCat.{v₁, u₁, v₃, u₃, v₂, u₂} B :=
  CategoryTheory.Equivalence.mk D2SGCFunctor toFunctor unitIso counitIso

@[simp] theorem d2sfibEquivalence_functor (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (d2sfibEquivalence.{v₁, u₁, v₂, u₂, v₃, u₃} B).functor = D2SGCFunctor := rfl

@[simp] theorem d2sfibEquivalence_inverse (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B] :
    (d2sfibEquivalence.{v₁, u₁, v₂, u₂, v₃, u₃} B).inverse = toFunctor := rfl

end Nfib

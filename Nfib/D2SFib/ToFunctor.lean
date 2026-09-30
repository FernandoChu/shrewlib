import Nfib.D2SFib.Category
import Nfib.Displayed.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# `Ψ`: from D2SFibs to functors `∫(Bᵈᵒ) ⥤ Cat`

Milestone **M7** of `PLAN.md`: the functor sending a D2SFib `C` to the functor
`⟨a, b⟩ ↦ C.Fiber b` on the total category of the dual opfibration.

`toFunctorObj` (the object part of `Ψ`) is fully proved. The functor `Ψ` itself
(`D2SFib.toFunctor`) is built from it below.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed A} [SplitOpfib B]

/-- The functor `∫(Bᵈᵒ) ⥤ Cat` underlying `Ψ C`: `⟨a, b⟩ ↦ C.Fiber b`, with a morphism `⟨α, β⟩`
sent to `pushFunctor α ⋙ pullFunctor β`. -/
noncomputable def toFunctorObj (C : DoubleDisplayed B) [D2SFib C] :
    B.dualOp.Total ⥤ Cat.{v₃, u₃} where
  obj x := Cat.of (C.Fiber x.2)
  map {x x'} F :=
    have β : B.Hom (𝟙 x'.1) x'.2 (B.transp F.base x.2) := F.fiber
    (D2SFib.pushFunctor (C := C) F.base x.2 ⋙ D2SFib.pullFunctor (C := C) β).toCatHom
  map_id x := by
    apply Cat.ext
    rw [Cat.Hom.id_toFunctor]
    refine CategoryTheory.Functor.ext (fun c => ?_) (fun c c' f => ?_)
    · exact eq_of_heq ((D2SFib.pull_eqToHom (C := C) (B.transp_id x.2).symm _).trans
        (D2SFib.push_id_heq (C := C) c))
    · refine (CategoryTheory.conj_eqToHom_iff_heq (C := C.Fiber x.2) _ _
        (eq_of_heq ((D2SFib.pull_eqToHom (C := C) (B.transp_id x.2).symm _).trans
          (D2SFib.push_id_heq (C := C) c)))
        (eq_of_heq ((D2SFib.pull_eqToHom (C := C) (B.transp_id x.2).symm _).trans
          (D2SFib.push_id_heq (C := C) c')))).mpr ?_
      exact (D2SFib.pullMap_eqToHom (C := C) (B.transp_id x.2).symm _).trans
        (D2SFib.pushMap_id_heq (C := C) f)
  map_comp {x x' x''} F G := by
    apply Cat.ext
    rw [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor, Functor.toCatHom_toFunctor,
      Functor.toCatHom_toFunctor]
    have h1 : ∀ (c : C.Fiber x.2), D2SFib.pull (C := C) (B.transpMap G.base F.fiber)
          (D2SFib.pull (eqToHom (B.transp_comp F.base G.base x.2).symm)
            (D2SFib.push (F.base ≫ G.base) c))
        ≍ D2SFib.push G.base (D2SFib.pull F.fiber (D2SFib.push F.base c)) := by
      intro c
      refine (D2SFib.pull_congr_obj rfl HEq.rfl
        ((D2SFib.pull_eqToHom (C := C) (B.transp_comp F.base G.base x.2).symm
          (D2SFib.push (F.base ≫ G.base) c)).trans
          (D2SFib.push_comp_heq F.base G.base c))).trans ?_
      exact heq_of_eq (D2SFib.push_pull G.base F.fiber (D2SFib.push F.base c)).symm
    have objHeq : ∀ (c : C.Fiber x.2),
        D2SFib.pull (C := C) (F.fiber ≫ᵈ G.fiber) (D2SFib.push (F.base ≫ G.base) c)
          ≍ D2SFib.pull (C := C) G.fiber
              (D2SFib.push G.base (D2SFib.pull F.fiber (D2SFib.push F.base c))) := by
      intro c
      refine (heq_of_eq (D2SFib.pull_comp G.fiber
        (B.transpMap G.base F.fiber ≫ eqToHom (B.transp_comp F.base G.base x.2).symm)
        (D2SFib.push (F.base ≫ G.base) c))).trans ?_
      refine (D2SFib.pull_congr_obj rfl HEq.rfl (heq_of_eq (D2SFib.pull_comp
        (B.transpMap G.base F.fiber) (eqToHom (B.transp_comp F.base G.base x.2).symm)
        (D2SFib.push (F.base ≫ G.base) c)))).trans ?_
      exact D2SFib.pull_congr_obj rfl HEq.rfl (h1 c)
    refine CategoryTheory.Functor.ext (fun c => eq_of_heq (objHeq c)) (fun c c' f => ?_)
    refine (CategoryTheory.conj_eqToHom_iff_heq (C := C.Fiber x''.2) _ _
      (eq_of_heq (objHeq c)) (eq_of_heq (objHeq c'))).mpr ?_
    change D2SFib.pullMap (C := C) (F.fiber ≫ᵈ G.fiber) (D2SFib.pushMap (F.base ≫ G.base) f)
      ≍ D2SFib.pullMap (C := C) G.fiber
          (D2SFib.pushMap G.base (D2SFib.pullMap F.fiber (D2SFib.pushMap F.base f)))
    have h2 : D2SFib.pullMap (C := C) (B.transpMap G.base F.fiber)
          (D2SFib.pullMap (eqToHom (B.transp_comp F.base G.base x.2).symm)
            (D2SFib.pushMap (F.base ≫ G.base) f))
        ≍ D2SFib.pushMap G.base (D2SFib.pullMap F.fiber (D2SFib.pushMap F.base f)) := by
      refine (D2SFib.pullMap_congr rfl HEq.rfl
        ((D2SFib.pull_eqToHom (C := C) (B.transp_comp F.base G.base x.2).symm
          (D2SFib.push (F.base ≫ G.base) c)).trans (D2SFib.push_comp_heq F.base G.base c))
        ((D2SFib.pull_eqToHom (C := C) (B.transp_comp F.base G.base x.2).symm
          (D2SFib.push (F.base ≫ G.base) c')).trans (D2SFib.push_comp_heq F.base G.base c'))
        ((D2SFib.pullMap_eqToHom (C := C) (B.transp_comp F.base G.base x.2).symm
          (D2SFib.pushMap (F.base ≫ G.base) f)).trans
          (D2SFib.pushMap_comp_base F.base G.base f))).trans ?_
      exact (D2SFib.pushMap_pullMap G.base F.fiber (D2SFib.pushMap F.base f)).symm
    refine (D2SFib.pullMap_comp_base G.fiber
      (B.transpMap G.base F.fiber ≫ eqToHom (B.transp_comp F.base G.base x.2).symm)
      (D2SFib.pushMap (F.base ≫ G.base) f)).trans ?_
    refine (D2SFib.pullMap_congr rfl HEq.rfl
      (heq_of_eq (D2SFib.pull_comp (B.transpMap G.base F.fiber)
        (eqToHom (B.transp_comp F.base G.base x.2).symm) (D2SFib.push (F.base ≫ G.base) c)))
      (heq_of_eq (D2SFib.pull_comp (B.transpMap G.base F.fiber)
        (eqToHom (B.transp_comp F.base G.base x.2).symm) (D2SFib.push (F.base ≫ G.base) c')))
      (D2SFib.pullMap_comp_base (B.transpMap G.base F.fiber)
        (eqToHom (B.transp_comp F.base G.base x.2).symm)
        (D2SFib.pushMap (F.base ≫ G.base) f))).trans ?_
    exact D2SFib.pullMap_congr rfl HEq.rfl (h1 c) (h1 c') h2

/-- `Ψ` on morphisms: a D2SFib morphism `Φ` induces a natural transformation of functors into
`Cat`, with component `Φ`'s fiber functor. -/
noncomputable def toFunctorMap {E E' : D2SFibCat B} (Φ : E ⟶ E') :
    toFunctorObj E.C ⟶ toFunctorObj E'.C where
  app x := (Φ.toVertFunctor.fiber x.2).toCatHom
  naturality {x x'} F := by
    apply Cat.ext
    change (D2SFib.pushFunctor (C := E.C) F.base x.2
        ⋙ D2SFib.pullFunctor (C := E.C)
          (F.fiber : B.Hom (𝟙 x'.1) x'.2 (B.transp F.base x.2))) ⋙ Φ.toVertFunctor.fiber x'.2
      = Φ.toVertFunctor.fiber x.2 ⋙ (D2SFib.pushFunctor (C := E'.C) F.base x.2
          ⋙ D2SFib.pullFunctor (C := E'.C) (F.fiber : B.Hom (𝟙 x'.1) x'.2 (B.transp F.base x.2)))
    rw [Functor.assoc, Φ.fiber_pullFunctor, ← Functor.assoc, Φ.fiber_pushFunctor, Functor.assoc]

/-- **`Ψ`**: the functor from D2SFibs over `B` to functors `∫(Bᵈᵒ) ⥤ Cat`. -/
noncomputable def toFunctor : D2SFibCat B ⥤ (B.dualOp.Total ⥤ Cat.{v₃, u₃}) where
  obj E := toFunctorObj E.C
  map Φ := toFunctorMap Φ
  map_id E := by
    apply NatTrans.ext; funext x
    exact congrArg Functor.toCatHom rfl
  map_comp Φ Ψ := by
    apply NatTrans.ext; funext x
    rfl


/-! ### `toFunctorObj` on the chosen morphisms of `∫(Bᵈᵒ)` -/

/-- `Ψ C` sends a chosen horizontal morphism to the pushforward functor. -/
theorem toFunctorObj_map_dualHoriz (C : DoubleDisplayed B) [D2SFib C] {a a' : A} (α : a ⟶ a')
    (b : B.Ob a) :
    ((toFunctorObj C).map (dualHoriz α b)).toFunctor = pushFunctor α b := by
  change pushFunctor α b ⋙ pullFunctor (C := C) (B.id (B.transp α b)) = _
  rw [pullFunctor_id]
  exact Functor.comp_id _

/-- `Ψ C` sends a chosen vertical morphism to the pullback functor. -/
theorem toFunctorObj_map_dualVert (C : DoubleDisplayed B) [D2SFib C] {a : A} {b b' : B.Fiber a}
    (β : b ⟶ b') : ((toFunctorObj C).map (dualVert β)).toFunctor = pullFunctor β := by
  change pushFunctor (𝟙 a) b' ⋙ pullFunctor (C := C) (β ≫ eqToHom (B.transp_id b').symm) = _
  have hobj : ∀ c : C.Fiber b',
      pull (C := C) (β ≫ eqToHom (B.transp_id b').symm) (push (𝟙 a) c) = pull β c := by
    intro c
    refine eq_of_heq ?_
    refine (heq_of_eq (pull_comp β (eqToHom (B.transp_id b').symm) (push (𝟙 a) c))).trans ?_
    exact pull_congr_obj rfl HEq.rfl
      ((pull_eqToHom (B.transp_id b').symm (push (𝟙 a) c)).trans (push_id_heq c))
  refine CategoryTheory.Functor.ext hobj (fun c c' f => ?_)
  refine (CategoryTheory.conj_eqToHom_iff_heq (C := C.Fiber b) _ _ (hobj c) (hobj c')).mpr ?_
  refine (pullMap_comp_base β (eqToHom (B.transp_id b').symm) (pushMap (𝟙 a) f)).trans ?_
  exact pullMap_congr rfl HEq.rfl
    ((pull_eqToHom (B.transp_id b').symm (push (𝟙 a) c)).trans (push_id_heq c))
    ((pull_eqToHom (B.transp_id b').symm (push (𝟙 a) c')).trans (push_id_heq c'))
    ((pullMap_eqToHom (B.transp_id b').symm (pushMap (𝟙 a) f)).trans (pushMap_id_heq f))

end Nfib

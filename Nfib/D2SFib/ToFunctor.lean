import Nfib.D2SFib.Category
import Nfib.Displayed.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# `Ψ`: from D2SFibs to functors `∫(Bᵈᵒ) ⥤ Cat`

Milestone **M7** of `PLAN.md`: the functor sending a D2SFib `C` to the functor
`⟨a, b⟩ ↦ C.Fiber b` on the total category of the dual opfibration, with a morphism `⟨α, β⟩` sent
to `pushFunctor α ⋙ pullFunctor β`.

Since the functoriality and interchange of `push`/`pull` and of `pushMap`/`pullMap` hold
definitionally, `Ψ C` is a functor by `rfl`, and so is the naturality of `Ψ` on morphisms.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace Nfib

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

set_option maxHeartbeats 400000 in
-- `map_comp` holds by `rfl`, through the rules for `push`, `pull`, `pushMap` and `pullMap`; checking
-- it unfolds both composites of functors.
/-- The functor `∫(Bᵈᵒ) ⥤ Cat` underlying `Ψ C`: `⟨a, b⟩ ↦ C.Fiber b`, with a morphism `⟨α, β⟩`
sent to `pushFunctor α ⋙ pullFunctor β`. -/
noncomputable def toFunctorObj (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C] :
    B.dualOp.Total ⥤ Cat.{v₃, u₃} where
  obj x := Cat.of (C.Fiber x.2)
  map {x _} F := (pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem toFunctorObj_map_toFunctor (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]
    {x x' : B.dualOp.Total} (F : x ⟶ x') :
    ((toFunctorObj C).map F).toFunctor
      = pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber := rfl

/-- `Ψ` on morphisms: a D2SFib morphism `Φ` induces a natural transformation of functors into
`Cat`, with component `Φ`'s fiber functor. -/
noncomputable def toFunctorMap {E E' : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B} (Φ : E ⟶ E') :
    toFunctorObj E.C ⟶ toFunctorObj E'.C where
  app x := (Φ.toVertFunctor.fiber x.2).toCatHom
  naturality _ _ _ := rfl

/-- **`Ψ`**: the functor from D2SFibs over `B` to functors `∫(Bᵈᵒ) ⥤ Cat`. -/
noncomputable def toFunctor : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B ⥤ (B.dualOp.Total ⥤ Cat.{v₃, u₃})
    where
  obj E := toFunctorObj E.C
  map Φ := toFunctorMap Φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `Ψ C` sends a chosen horizontal morphism to the pushforward functor. -/
theorem toFunctorObj_map_dualHoriz (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]
    {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    ((toFunctorObj C).map (dualHoriz α b)).toFunctor = pushFunctor (C := C) α b := rfl

/-- `Ψ C` sends a chosen vertical morphism to the pullback functor. -/
theorem toFunctorObj_map_dualVert (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [D2SFib C]
    {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    ((toFunctorObj C).map (dualVert β)).toFunctor = pullFunctor (C := C) β := rfl

end Nfib

import DoubleDisplayed.D2SFib.Category
import Displayed.Opfibration.DualOp
import Mathlib.CategoryTheory.Category.Cat

/-!
# Straightening: from D2SFibs to functors `Bᵒᵖ.Total ⥤ Cat`

`straighten` sends a D2SFib `C` to the functor
`⟨a, b⟩ ↦ C.Fiber b` on the total category of the dual opfibration, with a morphism `⟨α, β⟩` sent
to `pushFunctor α ⋙ pullFunctor β`.

Since the functoriality and interchange of `push`/`pull` and of `pushMap`/`pullMap` hold
definitionally, `straightenObj C` is a functor by `rfl`, and so is the naturality of
`straightenMap`.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace DoubleDisplayed.D2SFib.Straightening

open CategoryTheory Displayed DoubleDisplayed D2SFib

open scoped Displayed DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A} [SplitOpfib B]

set_option maxHeartbeats 400000 in
-- `map_comp` holds by `rfl`, through the rules for `push`, `pull`, `pushMap` and `pullMap`;
-- checking it unfolds both composites of functors.
/-- The functor `Bᵒᵖ.Total ⥤ Cat` underlying `straighten`'s value at `C`: `⟨a, b⟩ ↦ C.Fiber b`,
with a morphism `⟨α, β⟩` sent to `pushFunctor α ⋙ pullFunctor β`. -/
def straightenObj (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [SplitD2SFib C] :
    Bᵒᵖ.Total ⥤ Cat.{v₃, u₃} where
  obj x := Cat.of (C.Fiber x.2)
  map {x _} F := (pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber).toCatHom
  map_id _ := rfl
  map_comp _ _ := rfl

theorem straightenObj_map_toFunctor (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [SplitD2SFib C]
    {x x' : Bᵒᵖ.Total} (F : x ⟶ x') :
    ((straightenObj C).map F).toFunctor
      = pushFunctor (C := C) F.base x.2 ⋙ pullFunctor (C := C) F.fiber := rfl

/-- `straighten` on morphisms: a D2SFib morphism `Φ` induces a natural transformation of functors
into `Cat`, with component `Φ`'s fiber functor. -/
def straightenMap {E E' : D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B} (Φ : E ⟶ E') :
    straightenObj E.C ⟶ straightenObj E'.C where
  app x := (Φ.toDDFunctor.fiber x.2).toCatHom
  naturality _ _ _ := rfl

/-- **`straighten`**: the functor from D2SFibs over `B` to functors `Bᵒᵖ.Total ⥤ Cat`. -/
def straighten :
    D2SFibCat.{v₁, u₁, v₂, u₂, v₃, u₃} B ⥤ (Bᵒᵖ.Total ⥤ Cat.{v₃, u₃}) where
  obj E := straightenObj E.C
  map Φ := straightenMap Φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `straightenObj C` sends a chosen horizontal morphism to the pushforward functor. -/
theorem straightenObj_map_dualHoriz (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [SplitD2SFib C]
    {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    ((straightenObj C).map (dualHoriz α b)).toFunctor = pushFunctor (C := C) α b := rfl

/-- `straightenObj C` sends a chosen vertical morphism to the pullback functor. -/
theorem straightenObj_map_dualVert (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) [SplitD2SFib C]
    {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    ((straightenObj C).map (dualVert β)).toFunctor = pullFunctor (C := C) β := rfl

end DoubleDisplayed.D2SFib.Straightening

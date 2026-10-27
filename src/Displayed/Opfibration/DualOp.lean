import Displayed.Opfibration.Basic

/-!
# The dual opfibration

Given a split opfibration `B` over `A`, its *dual opfibration* `B.dualOp` is the fiberwise
opposite: it has the same displayed objects, but a morphism over `f : a ⟶ a'` from `x` to `y` is a
*vertical* morphism `y ⟶ B.push f x` in the fiber over `a'`. This corresponds to the
Grothendieck construction of `a ↦ (B.Fiber a)ᵒᵖ`.

It is written `Bᵒᵖ`, scoped in `Displayed`. This overloads Mathlib's `Cᵒᵖ` for the opposite of
a type `C`, and the elaborator picks the reading that typechecks.

Composition is `ψ ≫ B.pushMap g φ`. Since the splitting of `B` and the functoriality of
`pushMap` hold definitionally, so do the laws of `Bᵒᵖ`, and every identity between the chosen
horizontal and vertical morphisms `dualHoriz`/`dualVert` of its total category holds by `rfl`.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitOpfib B]

/-- The fiberwise opposite of a split opfibration `B`: same objects; a morphism over `f : a ⟶ a'`
from `x` to `y` is a vertical morphism `y ⟶ B.push f x`. -/
@[reducible] def dualOp : Displayed.{v₁, u₁, v₂, u₂} A where
  Ob := B.Ob
  Hom {_ a'} f x y := @Quiver.Hom (B.Fiber a') _ y (B.push f x)
  id {a} x := 𝟙 (show B.Fiber a from x)
  comp {_ _ _} {_ g} {_ _ _} φ ψ := ψ ≫ B.pushMap g φ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- `Bᵒᵖ` is the dual opfibration `B.dualOp` of a split opfibration `B`. -/
scoped notation:max B:max "ᵒᵖ" => Displayed.dualOp B

theorem dualOp_Ob (a : A) : Bᵒᵖ.Ob a = B.Ob a := rfl

theorem dualOp_Hom {a a' : A} (f : a ⟶ a') (x : B.Ob a) (y : B.Ob a') :
    Bᵒᵖ.Hom f x y = @Quiver.Hom (B.Fiber a') _ y (B.push f x) := rfl

theorem dualOp_id {a : A} (x : B.Ob a) : Bᵒᵖ.id x = 𝟙 (show B.Fiber a from x) := rfl

theorem dualOp_comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x y z}
    (φ : Bᵒᵖ.Hom f x y) (ψ : Bᵒᵖ.Hom g y z) :
    (φ ≫ᵈ ψ) = ψ ≫ B.pushMap g φ := rfl

section Total

variable {B}

/-- The chosen horizontal morphism of `Bᵒᵖ.Total` over `α`: the total-category image of the
identity vertical morphism. -/
def dualHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    Bᵒᵖ.tot b ⟶ Bᵒᵖ.tot (B.push α b) :=
  Bᵒᵖ.totalMk α (𝟙 (B.push α b))

/-- The chosen vertical morphism of `Bᵒᵖ.Total` associated to `β : b ⟶ b'`; note it is
*contravariant* (it reverses `β`). -/
def dualVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    Bᵒᵖ.tot b' ⟶ Bᵒᵖ.tot b :=
  Bᵒᵖ.totalMk (𝟙 a) β

@[simp] theorem dualHoriz_base {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    (dualHoriz α b).base = α := rfl

@[simp] theorem dualHoriz_fiber {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    (dualHoriz α b).fiber = 𝟙 (B.push α b) := rfl

@[simp] theorem dualVert_base {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualVert β).base = 𝟙 a := rfl

@[simp] theorem dualVert_fiber {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualVert β).fiber = β := rfl

theorem π_map_dualHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a) :
    Bᵒᵖ.π.map (dualHoriz α b) = α := rfl

theorem π_map_dualVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    Bᵒᵖ.π.map (dualVert β) = 𝟙 a := rfl

theorem dualVert_id {a : A} (b : B.Fiber a) : dualVert (𝟙 b) = 𝟙 (Bᵒᵖ.tot b) := rfl

/-- `dualVert` is contravariant. -/
theorem dualVert_comp {a : A} {b₁ b₂ b₃ : B.Fiber a} (u : b₁ ⟶ b₂) (v : b₂ ⟶ b₃) :
    dualVert (u ≫ v) = dualVert v ≫ dualVert u := rfl

/-- Every morphism of `Bᵒᵖ.Total` factors as a chosen horizontal morphism followed by a
vertical one. -/
theorem dual_factor {a a' : A} {b : B.Ob a} {b' : B.Ob a'}
    (F : Bᵒᵖ.tot b ⟶ Bᵒᵖ.tot b') : F = dualHoriz F.base b ≫ dualVert F.fiber := rfl

/-- Interchange in `Bᵒᵖ.Total`: pushing a vertical morphism past a chosen horizontal morphism
transports it along `B.pushMap`. -/
theorem dualVert_comp_dualHoriz {a a' : A} (α : a ⟶ a') {b b' : B.Fiber a} (β : b ⟶ b') :
    dualVert β ≫ dualHoriz α b = dualHoriz α b' ≫ dualVert (B.pushMap α β) := rfl

/-- The chosen horizontal morphism over an identity is the identity. -/
theorem dualHoriz_id {a : A} (b : B.Ob a) : dualHoriz (𝟙 a) b = 𝟙 (Bᵒᵖ.tot b) := rfl

/-- Splitness of `Bᵒᵖ.Total`: the chosen horizontal morphism over a composite is the composite
of the chosen horizontal morphisms. -/
theorem dualHoriz_comp {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a) :
    dualHoriz α b ≫ dualHoriz α' (B.push α b) = dualHoriz (α ≫ α') b := rfl

end Total

end Displayed

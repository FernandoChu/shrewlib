import Displayed.Fibration.Basic

/-!
# The dual fibration

Given a split fibration `B` over `A`, its *dual fibration* `B.dualFib` is the fiberwise opposite:
it has the same displayed objects, but a morphism over `f : a ⟶ a'` from `x` to `y` is a
*vertical* morphism `B.pull f y ⟶ x` in the fiber over `a`. This corresponds to the Grothendieck
construction of `a ↦ (B.Fiber a)ᵒᵖ`.

Composition is `B.pullMap f ψ ≫ φ`. Since the splitting of `B` and the functoriality of `pullMap`
hold definitionally, so do the laws of `B.dualFib`, and every identity between the chosen
horizontal and vertical morphisms `dualFibHoriz`/`dualFibVert` of its total category holds by
`rfl`.

This is the dual of `Opfibration/DualOp.lean`. It has no notation: `Bᵒᵖ` is the dual opfibration,
and a displayed category that is both a split fibration and a split opfibration would make an
overloaded `Bᵒᵖ` ambiguous.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {A : Type u₁} [Category.{v₁} A] (B : Displayed.{v₁, u₁, v₂, u₂} A) [SplitFib B]

/-- The fiberwise opposite of a split fibration `B`: same objects; a morphism over `f : a ⟶ a'`
from `x` to `y` is a vertical morphism `B.pull f y ⟶ x`. -/
@[reducible] def dualFib : Displayed.{v₁, u₁, v₂, u₂} A where
  Ob := B.Ob
  Hom {a _} f x y := @Quiver.Hom (B.Fiber a) _ (B.pull f y) x
  id {a} x := 𝟙 (show B.Fiber a from x)
  comp {_ _ _} {f _} {_ _ _} φ ψ := B.pullMap f ψ ≫ φ

theorem dualFib_Ob (a : A) : B.dualFib.Ob a = B.Ob a := rfl

theorem dualFib_Hom {a a' : A} (f : a ⟶ a') (x : B.Ob a) (y : B.Ob a') :
    B.dualFib.Hom f x y = @Quiver.Hom (B.Fiber a) _ (B.pull f y) x := rfl

theorem dualFib_id {a : A} (x : B.Ob a) : B.dualFib.id x = 𝟙 (show B.Fiber a from x) := rfl

theorem dualFib_comp {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x y z}
    (φ : B.dualFib.Hom f x y) (ψ : B.dualFib.Hom g y z) :
    (φ ≫ᵈ ψ) = B.pullMap f ψ ≫ φ := rfl

section Total

variable {B}

/-- The chosen horizontal morphism of `B.dualFib.Total` over `α`: the total-category image of the
identity vertical morphism. -/
def dualFibHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a') :
    B.dualFib.tot (B.pull α b) ⟶ B.dualFib.tot b :=
  B.dualFib.totalMk α (𝟙 (B.pull α b))

/-- The chosen vertical morphism of `B.dualFib.Total` associated to `β : b ⟶ b'`; note it is
*contravariant* (it reverses `β`). -/
def dualFibVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    B.dualFib.tot b' ⟶ B.dualFib.tot b :=
  B.dualFib.totalMk (𝟙 a) β

@[simp] theorem dualFibHoriz_base {a a' : A} (α : a ⟶ a') (b : B.Ob a') :
    (dualFibHoriz α b).base = α := rfl

@[simp] theorem dualFibHoriz_fiber {a a' : A} (α : a ⟶ a') (b : B.Ob a') :
    (dualFibHoriz α b).fiber = 𝟙 (B.pull α b) := rfl

@[simp] theorem dualFibVert_base {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualFibVert β).base = 𝟙 a := rfl

@[simp] theorem dualFibVert_fiber {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    (dualFibVert β).fiber = β := rfl

theorem π_map_dualFibHoriz {a a' : A} (α : a ⟶ a') (b : B.Ob a') :
    B.dualFib.π.map (dualFibHoriz α b) = α := rfl

theorem π_map_dualFibVert {a : A} {b b' : B.Fiber a} (β : b ⟶ b') :
    B.dualFib.π.map (dualFibVert β) = 𝟙 a := rfl

theorem dualFibVert_id {a : A} (b : B.Fiber a) : dualFibVert (𝟙 b) = 𝟙 (B.dualFib.tot b) := rfl

/-- `dualFibVert` is contravariant. -/
theorem dualFibVert_comp {a : A} {b₁ b₂ b₃ : B.Fiber a} (u : b₁ ⟶ b₂) (v : b₂ ⟶ b₃) :
    dualFibVert (u ≫ v) = dualFibVert v ≫ dualFibVert u := rfl

/-- Every morphism of `B.dualFib.Total` factors as a vertical morphism followed by a chosen
horizontal one. -/
theorem dualFib_factor {a a' : A} {b : B.Ob a} {b' : B.Ob a'}
    (F : B.dualFib.tot b ⟶ B.dualFib.tot b') : F = dualFibVert F.fiber ≫ dualFibHoriz F.base b' :=
  rfl

/-- Interchange in `B.dualFib.Total`: pulling a vertical morphism back past a chosen horizontal
morphism transports it along `B.pullMap`. -/
theorem dualFibHoriz_comp_dualFibVert {a a' : A} (α : a ⟶ a') {b b' : B.Fiber a'} (β : b ⟶ b') :
    dualFibHoriz α b' ≫ dualFibVert β = dualFibVert (B.pullMap α β) ≫ dualFibHoriz α b := rfl

/-- The chosen horizontal morphism over an identity is the identity. -/
theorem dualFibHoriz_id {a : A} (b : B.Ob a) : dualFibHoriz (𝟙 a) b = 𝟙 (B.dualFib.tot b) := rfl

/-- Splitness of `B.dualFib.Total`: the chosen horizontal morphism over a composite is the
composite of the chosen horizontal morphisms. -/
theorem dualFibHoriz_comp {a a' a'' : A} (α : a ⟶ a') (α' : a' ⟶ a'') (b : B.Ob a'') :
    dualFibHoriz α (B.pull α' b) ≫ dualFibHoriz α' b = dualFibHoriz (α ≫ α') b := rfl

end Total

end Displayed

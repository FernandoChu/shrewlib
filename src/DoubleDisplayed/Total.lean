import DoubleDisplayed.Basic

/-!
# The total construction

Given `C : DoubleDisplayed B` (a category doubly displayed over `B → A`), its *total* collapses the
two-level chain `C → B → A` into a single displayed category `C.total : Displayed A`, whose objects
over `a` are dependent pairs `⟨b, c⟩` with `b : B.Ob a` and `c : C.Ob b`, and whose morphisms are
dependent pairs of a `B`-morphism and a `C`-morphism over it. Its laws are componentwise those of
`B` and `C`, which hold definitionally. Its total category is the "associated category" of the
chain.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

open CategoryTheory Displayed

open scoped Displayed DoubleDisplayed

namespace DoubleDisplayed

variable {A : Type u₁} [Category.{v₁} A] {B : Displayed.{v₁, u₁, v₂, u₂} A}

/-- A morphism of the total construction: a `B`-morphism together with a `C`-morphism over it. -/
structure Total.Hom (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) {a a' : A} (f : a ⟶ a')
    (x : Σ b : B.Ob a, C.Ob b) (y : Σ b : B.Ob a', C.Ob b) where
  /-- The `B`-component. -/
  base : x.1 ⟶[f] y.1
  /-- The `C`-component, lying over `base`. -/
  fiber : x.2 ⟶[[base]] y.2

/-- The total construction: collapses the chain `C → B → A` to a single displayed category
`C.total : Displayed A`. -/
@[reducible] def total (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B) : Displayed A where
  Ob a := Σ b : B.Ob a, C.Ob b
  Hom f x y := Total.Hom C f x y
  id x := ⟨B.id x.1, C.id x.2⟩
  comp F G := ⟨F.base ≫ᵈ G.base, F.fiber ≫ᵈᵈ G.fiber⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

variable (C : DoubleDisplayed.{v₁, u₁, v₂, u₂, v₃, u₃} B)

theorem total_Ob (a : A) : C.total.Ob a = Σ b : B.Ob a, C.Ob b := rfl

@[simp] theorem total_id_base {a : A} (x : C.total.Ob a) : (C.total.id x).base = B.id x.1 := rfl

@[simp] theorem total_id_fiber {a : A} (x : C.total.Ob a) : (C.total.id x).fiber = C.id x.2 := rfl

@[simp] theorem total_comp_base {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''}
    {x : C.total.Ob a} {y : C.total.Ob a'} {z : C.total.Ob a''} (F : x ⟶[f] y) (G : y ⟶[g] z) :
    (F ≫ᵈ G).base = F.base ≫ᵈ G.base := rfl

@[simp] theorem total_comp_fiber {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''}
    {x : C.total.Ob a} {y : C.total.Ob a'} {z : C.total.Ob a''} (F : x ⟶[f] y) (G : y ⟶[g] z) :
    (F ≫ᵈ G).fiber = F.fiber ≫ᵈᵈ G.fiber := rfl

end DoubleDisplayed

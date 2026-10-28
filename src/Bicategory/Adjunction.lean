import Bicategory.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Tactic.KernelTactic

/-!
# Adjunctions in a 2-category

Adjunctions in a 2-category are Mathlib's `Bicategory.Adjunction`. As the unitors and associators
are identities (rules), the triangle laws reduce to `η ▷ l ≫ l ◁ ε = 𝟙 l` and
`r ◁ η ≫ ε ▷ r = 𝟙 r`. An adjunction is determined by its counit: two adjunctions `l ⊣ r` with
the same counit have the same unit (`Adjunction.unit_eq_of_counit_eq`).
-/

open CategoryTheory Bicategory

namespace CategoryTheory.TwoCategory

/-- Two adjunctions `l ⊣ r` with the same counit have the same unit. -/
theorem Adjunction.unit_eq_of_counit_eq {C : Type*} [TwoCategory C] {x y : C} {l : x ⟶ y}
    {r : y ⟶ x} (adj₁ adj₂ : l ⊣ r) (h : adj₁.counit = adj₂.counit) : adj₁.unit = adj₂.unit := by
  have t₁ : r ◁ adj₁.unit ≫ adj₁.counit ▷ r = 𝟙 r := by
    kernel_exact adj₁.right_triangle
  have t₂ : adj₂.unit ▷ l ≫ l ◁ adj₂.counit = 𝟙 l := by
    kernel_exact adj₂.left_triangle
  have e₁ : adj₁.unit ≫ adj₂.unit ▷ l ▷ r ≫ l ◁ adj₂.counit ▷ r = adj₁.unit := by
    kernel_exact congrArg (fun θ => adj₁.unit ≫ θ ▷ r) t₂
  have e₂ : adj₂.unit ≫ l ◁ r ◁ adj₁.unit ≫ l ◁ adj₁.counit ▷ r = adj₂.unit := by
    kernel_exact congrArg (fun θ => adj₂.unit ≫ l ◁ θ) t₁
  have ex : adj₁.unit ≫ adj₂.unit ▷ l ▷ r = adj₂.unit ≫ l ◁ r ◁ adj₁.unit := by
    kernel_exact whisker_exchange adj₂.unit adj₁.unit
  calc adj₁.unit = _ := e₁.symm
    _ = adj₁.unit ≫ adj₂.unit ▷ l ▷ r ≫ l ◁ adj₁.counit ▷ r := by rw [h]
    _ = adj₂.unit ≫ l ◁ r ◁ adj₁.unit ≫ l ◁ adj₁.counit ▷ r := by
      kernel_exact congrArg (· ≫ l ◁ adj₁.counit ▷ r) ex
    _ = adj₂.unit := e₂

end CategoryTheory.TwoCategory

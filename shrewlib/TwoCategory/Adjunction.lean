import TwoCategory.Basic
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic
import Tactic.KernelTactic

/-!
# Adjunctions in a 2-category

Adjunctions in a 2-category are Mathlib's `Bicategory.Adjunction`. As the unitors and associators
are identities (rules), the triangle laws reduce to `η ▷ l ≫ l ◁ ε = 𝟙 l` and
`r ◁ η ≫ ε ▷ r = 𝟙 r`. An adjunction is determined by its counit: two adjunctions `l ⊣ r` with
the same counit have the same unit (`Adjunction.unit_eq_of_counit_eq`). A 2-cell out of `r ≫ g`
is determined by its whiskering with `l`, and a 2-cell into `l ≫ h` by its whiskering with `r`
(`Adjunction.hom_ext_from`, `Adjunction.hom_ext_to`), as these are their transposes.
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

variable {C : Type*} [TwoCategory C] {x y z : C} {l : x ⟶ y} {r : y ⟶ x}

/-- A 2-cell `φ : r ≫ g ⟶ f` out of a composite with a right adjoint is determined by its
whiskering `l ◁ φ` with the left adjoint, as it is its transpose `r ◁ η ▷ g ≫ r ◁ l ◁ φ ≫ ε ▷ f`. -/
theorem Adjunction.hom_ext_from (adj : l ⊣ r) {g : x ⟶ z} {f : y ⟶ z} {φ ψ : r ≫ g ⟶ f}
    (h : l ◁ φ = l ◁ ψ) : φ = ψ := by
  have t : r ◁ adj.unit ≫ adj.counit ▷ r = 𝟙 r := by
    kernel_exact adj.right_triangle
  have key (θ : r ≫ g ⟶ f) : r ◁ adj.unit ▷ g ≫ r ◁ l ◁ θ ≫ adj.counit ▷ f = θ := by
    have ex : r ◁ l ◁ θ ≫ adj.counit ▷ f = adj.counit ▷ r ▷ g ≫ θ := by
      kernel_exact whisker_exchange adj.counit θ
    have e : r ◁ adj.unit ▷ g ≫ adj.counit ▷ r ▷ g ≫ θ = θ := by
      kernel_exact congrArg (· ▷ g ≫ θ) t
    exact (congrArg (r ◁ adj.unit ▷ g ≫ ·) ex).trans e
  calc φ = _ := (key φ).symm
    _ = _ := congrArg (fun θ => r ◁ adj.unit ▷ g ≫ r ◁ θ ≫ adj.counit ▷ f) h
    _ = ψ := key ψ

/-- A 2-cell `φ : g ⟶ l ≫ h` into a composite with a left adjoint is determined by its whiskering
`r ◁ φ` with the right adjoint, as it is its transpose `η ▷ g ≫ l ◁ r ◁ φ ≫ l ◁ ε ▷ h`. -/
theorem Adjunction.hom_ext_to (adj : l ⊣ r) {g : x ⟶ z} {h : y ⟶ z} {φ ψ : g ⟶ l ≫ h}
    (e : r ◁ φ = r ◁ ψ) : φ = ψ := by
  have t : adj.unit ▷ l ≫ l ◁ adj.counit = 𝟙 l := by
    kernel_exact adj.left_triangle
  have key (θ : g ⟶ l ≫ h) : adj.unit ▷ g ≫ l ◁ r ◁ θ ≫ l ◁ adj.counit ▷ h = θ := by
    have ex : adj.unit ▷ g ≫ l ◁ r ◁ θ = θ ≫ adj.unit ▷ l ▷ h := by
      kernel_exact (whisker_exchange adj.unit θ).symm
    have e : θ ≫ adj.unit ▷ l ▷ h ≫ l ◁ adj.counit ▷ h = θ := by
      kernel_exact congrArg (θ ≫ · ▷ h) t
    exact (congrArg (· ≫ l ◁ adj.counit ▷ h) ex).trans e
  calc φ = _ := (key φ).symm
    _ = _ := congrArg (fun θ => adj.unit ▷ g ≫ l ◁ θ ≫ l ◁ adj.counit ▷ h) e
    _ = ψ := key ψ

end CategoryTheory.TwoCategory

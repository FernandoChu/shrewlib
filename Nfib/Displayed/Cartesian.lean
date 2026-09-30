import Nfib.Displayed.Basic

/-!
# (Op)cartesian morphisms in a displayed category

This file defines the (strong) opcartesian and cartesian properties of a displayed morphism and
their universal-property API: the descent operation, its factorization equation, uniqueness and a
hom-extensionality principle.

This is part of milestone **M2** of `PLAN.md`.
-/

universe v₁ u₁ v₂ u₂

namespace Nfib

open CategoryTheory

namespace Displayed

variable {A : Type u₁} [Category.{v₁} A] {D : Displayed A}

/-- `φ : x ⟶[f] y` is *opcartesian*: every displayed map out of `x` over `f ≫ g` factors uniquely
through `φ` by a displayed map over `g`. (This is the *strong* opcartesian property.) -/
def IsOpcartesian {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) : Prop :=
  ∀ {a'' : A} (g : a' ⟶ a'') (z : D.Ob a'') (χ : x ⟶[f ≫ g] z),
    ∃! ψ : y ⟶[g] z, φ ≫ᵈ ψ = χ

/-- `φ : x ⟶[f] y` is *cartesian*: every displayed map into `y` over `g ≫ f` factors uniquely
through `φ` by a displayed map over `g`. (This is the *strong* cartesian property.) -/
def IsCartesian {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y) : Prop :=
  ∀ {a₀ : A} (g : a₀ ⟶ a) (z : D.Ob a₀) (χ : z ⟶[g ≫ f] y),
    ∃! ψ : z ⟶[g] x, ψ ≫ᵈ φ = χ

namespace IsOpcartesian

variable {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}

/-- The unique factorization of `χ` through an opcartesian `φ`. -/
noncomputable def desc (H : IsOpcartesian φ) {a'' : A} (g : a' ⟶ a'') {z : D.Ob a''}
    (χ : x ⟶[f ≫ g] z) : y ⟶[g] z :=
  (H g z χ).choose

@[simp]
theorem desc_fac (H : IsOpcartesian φ) {a'' : A} (g : a' ⟶ a'') {z : D.Ob a''}
    (χ : x ⟶[f ≫ g] z) : φ ≫ᵈ H.desc g χ = χ :=
  (H g z χ).choose_spec.1

/-- Any factorization of `χ` through `φ` agrees with `desc`. -/
theorem desc_uniq (H : IsOpcartesian φ) {a'' : A} {g : a' ⟶ a''} {z : D.Ob a''}
    {χ : x ⟶[f ≫ g] z} (ψ : y ⟶[g] z) (hψ : φ ≫ᵈ ψ = χ) : ψ = H.desc g χ :=
  (H g z χ).choose_spec.2 ψ hψ

/-- Two maps out of `y` that agree after precomposition with an opcartesian `φ` are equal. -/
theorem hom_ext (H : IsOpcartesian φ) {a'' : A} {g : a' ⟶ a''} {z : D.Ob a''}
    {ψ ψ' : y ⟶[g] z} (h : φ ≫ᵈ ψ = φ ≫ᵈ ψ') : ψ = ψ' :=
  (H.desc_uniq ψ rfl).trans (H.desc_uniq ψ' h.symm).symm

end IsOpcartesian

namespace IsCartesian

variable {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} {φ : x ⟶[f] y}

/-- The unique factorization of `χ` through a cartesian `φ`. -/
noncomputable def lift (H : IsCartesian φ) {a₀ : A} (g : a₀ ⟶ a) {z : D.Ob a₀}
    (χ : z ⟶[g ≫ f] y) : z ⟶[g] x :=
  (H g z χ).choose

@[simp]
theorem lift_fac (H : IsCartesian φ) {a₀ : A} (g : a₀ ⟶ a) {z : D.Ob a₀}
    (χ : z ⟶[g ≫ f] y) : H.lift g χ ≫ᵈ φ = χ :=
  (H g z χ).choose_spec.1

/-- Any factorization of `χ` through `φ` agrees with `lift`. -/
theorem lift_uniq (H : IsCartesian φ) {a₀ : A} {g : a₀ ⟶ a} {z : D.Ob a₀}
    {χ : z ⟶[g ≫ f] y} (ψ : z ⟶[g] x) (hψ : ψ ≫ᵈ φ = χ) : ψ = H.lift g χ :=
  (H g z χ).choose_spec.2 ψ hψ

/-- Two maps into `x` that agree after postcomposition with a cartesian `φ` are equal. -/
theorem hom_ext (H : IsCartesian φ) {a₀ : A} {g : a₀ ⟶ a} {z : D.Ob a₀}
    {ψ ψ' : z ⟶[g] x} (h : ψ ≫ᵈ φ = ψ' ≫ᵈ φ) : ψ = ψ' :=
  (H.lift_uniq ψ rfl).trans (H.lift_uniq ψ' h.symm).symm

end IsCartesian

end Displayed

end Nfib

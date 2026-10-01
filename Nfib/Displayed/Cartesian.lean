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

/-- Precomposing an opcartesian morphism with a vertical isomorphism gives an opcartesian
morphism. -/
theorem iso_comp {x' : D.Ob a} (H : IsOpcartesian φ) (ι : x' ⟶[𝟙 a] x) (ι' : x ⟶[𝟙 a] x')
    (h : ι' ≫ᵈ ι = 𝟙ᵈ x) (h' : ι ≫ᵈ ι' = 𝟙ᵈ x') : IsOpcartesian (ι ≫ᵈ φ) := by
  intro a'' g z χ
  refine ⟨H.desc g (ι' ≫ᵈ χ :), ?_, fun ψ hψ => H.desc_uniq ψ ?_⟩
  · exact ((congrArg (ι ≫ᵈ ·) (H.desc_fac g (ι' ≫ᵈ χ :))).trans (congrArg (· ≫ᵈ χ) h') :)
  · exact ((congrArg (fun t => t ≫ᵈ (φ ≫ᵈ ψ)) h).symm.trans (congrArg (ι' ≫ᵈ ·) hψ) :)

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

/-- Postcomposing a cartesian morphism with a vertical isomorphism gives a cartesian morphism. -/
theorem comp_iso {y' : D.Ob a'} (H : IsCartesian φ) (ι : y ⟶[𝟙 a'] y') (ι' : y' ⟶[𝟙 a'] y)
    (h : ι' ≫ᵈ ι = 𝟙ᵈ y') (h' : ι ≫ᵈ ι' = 𝟙ᵈ y) : IsCartesian (φ ≫ᵈ ι) := by
  intro a₀ g z χ
  refine ⟨H.lift g (χ ≫ᵈ ι' :), ?_, fun ψ hψ => H.lift_uniq ψ ?_⟩
  · exact ((congrArg (· ≫ᵈ ι) (H.lift_fac g (χ ≫ᵈ ι' :))).trans (congrArg (χ ≫ᵈ ·) h) :)
  · exact ((congrArg (fun t => ψ ≫ᵈ (φ ≫ᵈ t)) h').symm.trans (congrArg (· ≫ᵈ ι') hψ) :)

end IsCartesian

end Displayed

end Nfib

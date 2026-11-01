import Rules.Category
import Tactic.KernelRfl
import Mathlib.CategoryTheory.Bicategory.Strict.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# 2-categories

A 2-category is a strict bicategory: a `Bicategory` whose unitors and associators are given by the
equalities `𝟙 a ≫ f = f`, `f ≫ 𝟙 b = f` and `(f ≫ g) ≫ h = f ≫ g ≫ h` (Mathlib's
`Bicategory.Strict`). `TwoCategory B` bundles the two, so that its instance occurs in the laws
below, which are rules:

* the laws of 1-cells, so that composites of 1-cells are right-associated, without identities;
* the unitors and associators are identities, `λ_ f ↦ Iso.refl f`, and so on;
* whiskering is functorial, `f ◁ (η ≫ θ) ↦ f ◁ η ≫ f ◁ θ` and so on;
* whiskering is strictly unital and associative: `𝟙 a ◁ η ↦ η`, `(f ≫ g) ◁ η ↦ f ◁ g ◁ η`,
  `η ▷ 𝟙 b ↦ η`, `η ▷ (g ≫ h) ↦ η ▷ g ▷ h` and `(f ◁ η) ▷ h ↦ f ◁ η ▷ h`.

Together with the category laws for 2-cells (`Rules.Category`), whiskered 2-cells have a normal
form `f₁ ◁ ⋯ ◁ fₙ ◁ η ▷ g₁ ▷ ⋯ ▷ gₘ`, and the coherence laws of the bicategory hold by `rfl`.
Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory

/-- A 2-category: a bicategory whose unitors and associators are identities. -/
class TwoCategory (B : Type u) extends Bicategory.{w, v} B, Bicategory.Strict B

namespace TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] {a b c d : B}

/-! ## 1-cells -/

@[rewrite_rule]
theorem id_comp' (f : a ⟶ b) : 𝟙 a ≫ f = f :=
  Strict.id_comp f

@[rewrite_rule]
theorem comp_id' (f : a ⟶ b) : f ≫ 𝟙 b = f :=
  Strict.comp_id f

@[rewrite_rule]
theorem assoc' (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (f ≫ g) ≫ h = f ≫ g ≫ h :=
  Strict.assoc f g h

/-! ## Unitors and associators -/

@[rewrite_rule]
theorem leftUnitor_eq (f : a ⟶ b) : λ_ f = Iso.refl f :=
  Strict.leftUnitor_eqToIso f

@[rewrite_rule]
theorem rightUnitor_eq (f : a ⟶ b) : ρ_ f = Iso.refl f :=
  Strict.rightUnitor_eqToIso f

@[rewrite_rule]
theorem associator_eq (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : α_ f g h = Iso.refl (f ≫ g ≫ h) :=
  Strict.associator_eqToIso f g h

/-! ## Whiskering -/

@[rewrite_rule]
theorem whiskerLeft_id' (f : a ⟶ b) (g : b ⟶ c) : f ◁ 𝟙 g = 𝟙 (f ≫ g) :=
  Bicategory.whiskerLeft_id f g

@[rewrite_rule]
theorem whiskerLeft_comp' (f : a ⟶ b) {g h i : b ⟶ c} (η : g ⟶ h) (θ : h ⟶ i) :
    f ◁ (η ≫ θ) = f ◁ η ≫ f ◁ θ :=
  Bicategory.whiskerLeft_comp f η θ

@[rewrite_rule]
theorem id_whiskerRight' (f : a ⟶ b) (g : b ⟶ c) : 𝟙 f ▷ g = 𝟙 (f ≫ g) :=
  Bicategory.id_whiskerRight f g

@[rewrite_rule]
theorem comp_whiskerRight' {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    (η ≫ θ) ▷ i = η ▷ i ≫ θ ▷ i :=
  Bicategory.comp_whiskerRight η θ i

@[rewrite_rule]
theorem id_whiskerLeft' {f g : a ⟶ b} (η : f ⟶ g) : 𝟙 a ◁ η = η :=
  Bicategory.id_whiskerLeft η

@[rewrite_rule]
theorem comp_whiskerLeft' (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
    (f ≫ g) ◁ η = f ◁ g ◁ η :=
  Bicategory.comp_whiskerLeft f g η

@[rewrite_rule]
theorem whiskerRight_id' {f g : a ⟶ b} (η : f ⟶ g) : η ▷ 𝟙 b = η :=
  Bicategory.whiskerRight_id η

@[rewrite_rule]
theorem whiskerRight_comp' {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
    η ▷ (g ≫ h) = η ▷ g ▷ h :=
  Bicategory.whiskerRight_comp η g h

@[rewrite_rule]
theorem whisker_assoc' (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
    (f ◁ η) ▷ h = f ◁ η ▷ h :=
  Bicategory.whisker_assoc f η h

/-! ## Whiskering with equal 1-cells

A rule `f ≫ g ↦ h` on 1-cells overlaps with the rules for whiskering with a composite: the 2-cells
`(f ≫ g) ◁ η` and `θ ▷ (f ≫ g)` rewrite both to `f ◁ g ◁ η`, `θ ▷ f ▷ g` and to `h ◁ η`, `θ ▷ h`.
Such rules come with the whiskered forms `f ◁ g ◁ η ↦ h ◁ η` and `θ ▷ f ▷ g ↦ θ ▷ h`, which are
proved from the following, and with the reassociated form `f ≫ g ≫ k ↦ h ≫ k`. -/

theorem whiskerLeft_congr {f f' : a ⟶ b} (e : f = f') {g h : b ⟶ c} (η : g ⟶ h) :
    HEq (f ◁ η) (f' ◁ η) := by
  cases e; rfl

theorem whiskerRight_congr {f g : a ⟶ b} (η : f ⟶ g) {h h' : b ⟶ c} (e : h = h') :
    HEq (η ▷ h) (η ▷ h') := by
  cases e; rfl

/-! ## Tests -/

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) : (α_ f g h).hom = 𝟙 (f ≫ g ≫ h) := rfl

example {f f' : a ⟶ b} {g g' : b ⟶ c} (η : f ⟶ f') (θ : g ⟶ g') :
    η ▷ g ≫ f' ◁ θ = f ◁ θ ≫ η ▷ g' :=
  (whisker_exchange η θ).symm

example (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom ▷ 𝟙 d ≫ (𝟙 a ≫ f) ◁ (λ_ (g ≫ h)).inv = 𝟙 (f ≫ g ≫ h) := rfl

end TwoCategory

/-! ## `Cat` -/

/-- `Cat` is a 2-category. -/
instance Cat.twoCategory : TwoCategory Cat.{v, u} :=
  { Cat.bicategory, Cat.bicategory.strict with }

end CategoryTheory

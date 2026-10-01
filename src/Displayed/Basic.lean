import Rules.Category
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Displayed categories

This file defines `Displayed A`, a category displayed over a base category `A`: objects are
indexed by objects of `A`, and morphisms lying over `f : a ⟶ a'` form their own type `Hom f x y`.

A displayed hom-type depends on the base morphism it lies over, so the coherence laws relate
morphisms whose types differ by the category laws of `A`: `𝟙ᵈ x ≫ᵈ φ` lies over `𝟙 a ≫ f`, while
`φ` lies over `f`. The category laws of `A` are rewrite rules, so these types are definitionally
equal and the laws are plain equations, with no cast or `HEq`. The laws are rewrite rules in turn,
so that the same holds one level up, for categories displayed over a displayed category.

We provide:

* the structure `Displayed` and scoped notation `𝟙ᵈ x`, `φ ≫ᵈ ψ` and `x ⟶[f] y`;
* the fiber category `Displayed.Fiber D a`, whose laws hold by `rfl`.

The total category is in `Displayed/Total.lean`.

Requires the `rewrite-rules` fork of Lean.
-/

universe v₁ u₁ v₂ u₂

open CategoryTheory

variable {A : Type u₁} [Category.{v₁} A]

/-- A category displayed over `A`: objects over each `a : A`, and morphisms lying over each base
morphism `f : a ⟶ a'`. The two sides of each law have definitionally equal types by the rewrite
rules for the category laws of `A`. -/
structure Displayed (A : Type u₁) [Category.{v₁} A] where
  /-- The type of objects lying over `a : A`. -/
  Ob : A → Type u₂
  /-- The type of displayed morphisms lying over `f : a ⟶ a'`. -/
  Hom : {a a' : A} → (a ⟶ a') → Ob a → Ob a' → Type v₂
  /-- The displayed identity over `𝟙 a`. -/
  id : {a : A} → (x : Ob a) → Hom (𝟙 a) x x
  /-- Displayed composition, lying over `f ≫ g`. -/
  comp : {a a' a'' : A} → {f : a ⟶ a'} → {g : a' ⟶ a''} → {x : Ob a} → {y : Ob a'} →
    {z : Ob a''} → Hom f x y → Hom g y z → Hom (f ≫ g) x z
  id_comp : ∀ {a a' : A} {f : a ⟶ a'} {x : Ob a} {y : Ob a'} (φ : Hom f x y), comp (id x) φ = φ
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {x : Ob a} {y : Ob a'} (φ : Hom f x y), comp φ (id y) = φ
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {h : a'' ⟶ a'''}
    {x : Ob a} {y : Ob a'} {z : Ob a''} {w : Ob a'''} (φ : Hom f x y) (ψ : Hom g y z)
    (χ : Hom h z w), comp (comp φ ψ) χ = comp φ (comp ψ χ)

attribute [rewrite_rule] Displayed.id_comp Displayed.comp_id Displayed.assoc

namespace Displayed

/-- Notation for the displayed identity morphism, mirroring `𝟙` for categories. -/
scoped notation "𝟙ᵈ" => Displayed.id _

/-- Notation for displayed composition, mirroring `≫` for categories. -/
scoped notation:80 φ:81 " ≫ᵈ " ψ:80 => Displayed.comp _ φ ψ

/-- Notation for a displayed hom-type: `x ⟶[f] y` is the type of displayed morphisms from `x` to
`y` lying over the base morphism `f`. -/
scoped notation:10 x " ⟶[" f "] " y => Displayed.Hom _ f x y

variable (D : Displayed.{v₁, u₁, v₂, u₂} A)

section Fiber

/-- The fiber of `D` over `a`: objects lying over `a`, with vertical morphisms (over `𝟙 a`). -/
abbrev Fiber (D : Displayed.{v₁, u₁, v₂, u₂} A) (a : A) : Type u₂ := D.Ob a

/-- The fiber over `a` is a category: composition is displayed composition, which lies over
`𝟙 a ≫ 𝟙 a`, that is over `𝟙 a`. -/
instance (a : A) : Category.{v₂} (D.Fiber a) where
  Hom x y := x ⟶[𝟙 a] y
  id x := 𝟙ᵈ x
  comp φ ψ := φ ≫ᵈ ψ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

theorem Fiber.hom_def (a : A) (x y : D.Fiber a) : (x ⟶ y) = (x ⟶[𝟙 a] y) := rfl

theorem Fiber.id_def (a : A) (x : D.Fiber a) : 𝟙 x = 𝟙ᵈ x := rfl

theorem Fiber.comp_def {a : A} {x y z : D.Fiber a} (φ : x ⟶ y) (ψ : y ⟶ z) :
    φ ≫ ψ = φ ≫ᵈ ψ := rfl

end Fiber

end Displayed

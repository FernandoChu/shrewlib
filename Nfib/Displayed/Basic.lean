import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic

/-!
# Displayed categories

This file defines `Nfib.Displayed A`, a category displayed over a base category `A`: objects are
indexed by objects of `A`, and morphisms lying over `f : a ⟶ a'` form their own type `Hom f x y`.

A displayed hom-type depends on the base morphism it lies over, so the coherence laws relate
morphisms whose types differ by the category laws of `A`: `𝟙ᵈ x ≫ᵈ φ` lies over `𝟙 a ≫ f`, while
`φ` lies over `f`. The category laws of `A` are rewrite rules, so these types are definitionally
equal and the laws are plain equations, with no cast or `HEq`. The laws are rewrite rules in turn,
so that the same holds one level up, for categories displayed over a displayed category.

We provide:

* the structure `Displayed` and scoped notation `𝟙ᵈ x`, `φ ≫ᵈ ψ` and `x ⟶[f] y`;
* the fiber category `Displayed.Fiber D a`, whose laws hold by `rfl`;
* the total category `Displayed.Total D`, whose laws hold by `rfl`, with the projection `π` and
  the fiber inclusions `ι`.

This is milestone **M1** of `PLAN.md`. Requires the `rewrite-rules` fork of Lean.
-/

universe v₁ u₁ v₂ u₂

namespace Nfib

open CategoryTheory

attribute [rewrite_rule] Category.id_comp Category.comp_id Category.assoc

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
scoped notation "𝟙ᵈ" => Nfib.Displayed.id _

/-- Notation for displayed composition, mirroring `≫` for categories. -/
scoped notation:80 φ:81 " ≫ᵈ " ψ:80 => Nfib.Displayed.comp _ φ ψ

/-- Notation for a displayed hom-type: `x ⟶[f] y` is the type of displayed morphisms from `x` to
`y` lying over the base morphism `f`. -/
scoped notation:10 x " ⟶[" f "] " y => Nfib.Displayed.Hom _ f x y

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

section Total

/-- The total category of `D`: pairs `⟨a, x⟩` with `a : A` and `x : D.Ob a`. -/
def Total (D : Displayed.{v₁, u₁, v₂, u₂} A) := Σ a : A, D.Ob a

/-- An object of the total category. Its type is syntactically `D.Total`, so that `⟶`, `≫` and
`𝟙` elaborate on it. -/
def tot {a : A} (x : D.Ob a) : D.Total := ⟨a, x⟩

@[simp] theorem tot_fst {a : A} (x : D.Ob a) : (D.tot x).1 = a := rfl
@[simp] theorem tot_snd {a : A} (x : D.Ob a) : (D.tot x).2 = x := rfl

/-- A morphism in the total category of `D`: a base morphism together with a displayed morphism
lying over it. -/
structure Total.Hom {D : Displayed.{v₁, u₁, v₂, u₂} A} (x y : D.Total) where
  /-- The base component. -/
  base : x.1 ⟶ y.1
  /-- The displayed component, lying over `base`. -/
  fiber : x.2 ⟶[base] y.2

/-- The total category: its laws are those of `A` and `D`, which hold definitionally. -/
instance : Category D.Total where
  Hom x y := Total.Hom x y
  id x := ⟨𝟙 x.1, 𝟙ᵈ x.2⟩
  comp F G := ⟨F.base ≫ G.base, F.fiber ≫ᵈ G.fiber⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem Total.id_base (x : D.Total) : (𝟙 x : x ⟶ x).base = 𝟙 x.1 := rfl

@[simp] theorem Total.id_fiber (x : D.Total) : (𝟙 x : x ⟶ x).fiber = 𝟙ᵈ x.2 := rfl

@[simp] theorem Total.comp_base {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).base = F.base ≫ G.base := rfl

@[simp] theorem Total.comp_fiber {x y z : D.Total} (F : x ⟶ y) (G : y ⟶ z) :
    (F ≫ G).fiber = F.fiber ≫ᵈ G.fiber := rfl

/-- A morphism of the total category, assembled from a base morphism and a displayed morphism over
it. Unlike the anonymous constructor, its type is syntactically `_ ⟶ _`. -/
def totalMk {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a') (φ : x ⟶[f] y) :
    D.tot x ⟶ D.tot y := ⟨f, φ⟩

@[simp] theorem totalMk_base {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).base = f := rfl

@[simp] theorem totalMk_fiber {a a' : A} {x : D.Ob a} {y : D.Ob a'} (f : a ⟶ a')
    (φ : x ⟶[f] y) : (D.totalMk f φ).fiber = φ := rfl

theorem totalMk_comp {a a' a'' : A} {x : D.Ob a} {y : D.Ob a'} {z : D.Ob a''}
    (f : a ⟶ a') (φ : x ⟶[f] y) (g : a' ⟶ a'') (ψ : y ⟶[g] z) :
    D.totalMk f φ ≫ D.totalMk g ψ = D.totalMk (f ≫ g) (φ ≫ᵈ ψ) := rfl

/-- A *vertical* morphism of the total category: the image of a fiber morphism. -/
def totalVert {a : A} {x y : D.Fiber a} (β : x ⟶ y) : D.tot x ⟶ D.tot y := D.totalMk (𝟙 a) β

theorem totalVert_id {a : A} (x : D.Fiber a) : D.totalVert (𝟙 x) = 𝟙 (D.tot x) := rfl

theorem totalVert_comp {a : A} {x y z : D.Fiber a} (β : x ⟶ y) (γ : y ⟶ z) :
    D.totalVert (β ≫ γ) = D.totalVert β ≫ D.totalVert γ := rfl

/-- The projection of the total category to the base. -/
def π : D.Total ⥤ A where
  obj x := x.1
  map F := F.base
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem π_obj (x : D.Total) : D.π.obj x = x.1 := rfl
@[simp] theorem π_map {x y : D.Total} (F : x ⟶ y) : D.π.map F = F.base := rfl

/-- The inclusion of the fiber over `a` into the total category. -/
def ι (a : A) : D.Fiber a ⥤ D.Total where
  obj x := D.tot x
  map β := D.totalVert β
  map_id _ := rfl
  map_comp _ _ := rfl

@[simp] theorem ι_obj (a : A) (x : D.Fiber a) : (D.ι a).obj x = D.tot x := rfl
@[simp] theorem ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) : (D.ι a).map β = D.totalVert β := rfl

theorem π_map_ι_map {a : A} {x y : D.Fiber a} (β : x ⟶ y) :
    D.π.map ((D.ι a).map β) = 𝟙 a := rfl

end Total

end Displayed

end Nfib

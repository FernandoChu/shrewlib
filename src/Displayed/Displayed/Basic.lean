import Rules.Category
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Iso

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
* the fiber category `Displayed.Fiber D a`, whose laws hold by `rfl`;
* vertical functors `VertFunctor D E` (functors over the identity of `A`), whose laws are rewrite
  rules, and vertical natural transformations `VertNatTrans F G` (with components over identities),
  forming the category `VertFunctor D E`. As in Mathlib's functor categories, vertical natural
  isomorphisms are the isomorphisms `F ≅ G` of this category; the `VertNatIso` namespace has their
  components (`VertNatIso.app`, `VertNatIso.hom_inv_id_app`, …) and `VertNatIso.ofComponents`.

The cancellation lemmas of vertical natural isomorphisms are not rewrite rules: they are keyed on
displayed composition, and trying them on every displayed composite is too slow.

The total category is in `Displayed/Displayed/Total.lean`, and equivalences over `A` are in
`Displayed/Displayed/Equivalence.lean`.

Requires the `rewrite-rules` fork of Lean.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

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


/-! ## Vertical functors -/

section VertFunctor

/-- A vertical functor: a displayed functor over the identity of `A`, i.e. a functor over `A`
between the total categories. -/
structure VertFunctor (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) where
  /-- The action on objects, fiberwise. -/
  obj : {a : A} → D.Ob a → E.Ob a
  /-- The action on morphisms, over the same base morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : D.Ob a} → {y : D.Ob a'} → (x ⟶[f] y) →
    (obj x ⟶[f] obj y)
  map_id : ∀ {a : A} (x : D.Ob a), map (𝟙ᵈ x) = 𝟙ᵈ (obj x)
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z), map (φ ≫ᵈ ψ) = map φ ≫ᵈ map ψ

attribute [rewrite_rule] VertFunctor.map_id VertFunctor.map_comp

variable {E : Displayed.{v₁, u₁, v₃, u₃} A} {E' : Displayed.{v₁, u₁, v₂, u₂} A}

/-- The identity vertical functor. -/
def VertFunctor.id (D : Displayed.{v₁, u₁, v₂, u₂} A) : VertFunctor D D where
  obj x := x
  map φ := φ
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Composition of vertical functors. -/
def VertFunctor.comp {D : Displayed.{v₁, u₁, v₂, u₂} A} (F : VertFunctor D E)
    (G : VertFunctor E E') : VertFunctor D E' where
  obj x := G.obj (F.obj x)
  map φ := G.map (F.map φ)
  map_id _ := rfl
  map_comp _ _ := rfl

end VertFunctor

/-! ## Vertical natural transformations -/

section VertNatTrans

variable {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₁, u₁, v₃, u₃} A}

/-- A vertical natural transformation between vertical functors: its components lie over
identities, and it is natural with respect to displayed morphisms over arbitrary base morphisms. -/
@[ext]
structure VertNatTrans (F G : VertFunctor D E) where
  /-- The components. -/
  app : ∀ {a : A} (x : D.Ob a), F.obj x ⟶[𝟙 a] G.obj x
  naturality : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
    F.map φ ≫ᵈ app y = app x ≫ᵈ G.map φ

namespace VertNatTrans

/-- The identity vertical natural transformation. -/
protected def id (F : VertFunctor D E) : VertNatTrans F F where
  app x := 𝟙ᵈ (F.obj x)
  naturality _ := rfl

/-- Vertical composition of vertical natural transformations. -/
def vcomp {F G H : VertFunctor D E} (η : VertNatTrans F G) (θ : VertNatTrans G H) :
    VertNatTrans F H where
  app x := η.app x ≫ᵈ θ.app x
  naturality {_ _ _ x y} φ :=
    ((congrArg (· ≫ᵈ θ.app y) (η.naturality φ)).trans
      (congrArg (η.app x ≫ᵈ ·) (θ.naturality φ)) :)

end VertNatTrans

/-- Vertical functors and vertical natural transformations form a category. -/
instance VertFunctor.category : Category (VertFunctor D E) where
  Hom F G := VertNatTrans F G
  id F := VertNatTrans.id F
  comp η θ := VertNatTrans.vcomp η θ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

namespace VertNatTrans

variable {F G H : VertFunctor D E}

@[ext]
theorem ext' {η θ : F ⟶ G} (h : ∀ {a : A} (x : D.Ob a), η.app x = θ.app x) : η = θ :=
  VertNatTrans.ext (by funext a x; exact h x)

@[simp] theorem id_app {a : A} (x : D.Ob a) : VertNatTrans.app (𝟙 F) x = 𝟙ᵈ (F.obj x) := rfl

@[simp] theorem comp_app (η : F ⟶ G) (θ : G ⟶ H) {a : A} (x : D.Ob a) :
    VertNatTrans.app (η ≫ θ) x = η.app x ≫ᵈ θ.app x := rfl

end VertNatTrans

namespace VertNatIso

variable {F G : VertFunctor D E} (η : F ≅ G)

/-- The component of a vertical natural isomorphism, an isomorphism of the fiber. -/
@[simps]
def app {a : A} (x : D.Ob a) : (F.obj x : E.Fiber a) ≅ G.obj x where
  hom := η.hom.app x
  inv := η.inv.app x
  hom_inv_id := congrArg (fun t => VertNatTrans.app t x) η.hom_inv_id
  inv_hom_id := congrArg (fun t => VertNatTrans.app t x) η.inv_hom_id

theorem hom_inv_id_app {a : A} (x : D.Ob a) : η.hom.app x ≫ᵈ η.inv.app x = 𝟙ᵈ (F.obj x) :=
  (VertNatIso.app η x).hom_inv_id

theorem inv_hom_id_app {a : A} (x : D.Ob a) : η.inv.app x ≫ᵈ η.hom.app x = 𝟙ᵈ (G.obj x) :=
  (VertNatIso.app η x).inv_hom_id

theorem hom_inv_id_app_assoc {a a' : A} {g : a ⟶ a'} (x : D.Ob a) {z : E.Ob a'}
    (h : F.obj x ⟶[g] z) : η.hom.app x ≫ᵈ (η.inv.app x ≫ᵈ h) = h :=
  (congrArg (· ≫ᵈ h) (hom_inv_id_app η x) :)

theorem inv_hom_id_app_assoc {a a' : A} {g : a ⟶ a'} (x : D.Ob a) {z : E.Ob a'}
    (h : G.obj x ⟶[g] z) : η.inv.app x ≫ᵈ (η.hom.app x ≫ᵈ h) = h :=
  (congrArg (· ≫ᵈ h) (inv_hom_id_app η x) :)

/-- A vertical natural isomorphism from isomorphisms of the fibers, natural in displayed
morphisms. -/
def ofComponents (app : ∀ {a : A} (x : D.Ob a), (F.obj x : E.Fiber a) ≅ G.obj x)
    (naturality : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
      F.map φ ≫ᵈ (app y).hom = (app x).hom ≫ᵈ G.map φ) : F ≅ G where
  hom := ⟨fun x => (app x).hom, naturality⟩
  inv :=
    { app := fun x => (app x).inv
      naturality := fun {_ _ _ x y} φ =>
        ((congrArg (· ≫ᵈ (G.map φ ≫ᵈ (app y).inv)) (app x).inv_hom_id).symm.trans
          ((congrArg (fun t => (app x).inv ≫ᵈ (t ≫ᵈ (app y).inv)) (naturality φ)).symm.trans
            (congrArg (fun t => (app x).inv ≫ᵈ (F.map φ ≫ᵈ t)) (app y).hom_inv_id)) :) }
  hom_inv_id := VertNatTrans.ext' fun x => (app x).hom_inv_id
  inv_hom_id := VertNatTrans.ext' fun x => (app x).inv_hom_id

end VertNatIso

end VertNatTrans

end Displayed

import Rules.Functor
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
* displayed functors `DispFunctor u D E` over a functor `u : A ⥤ B`, whose laws are rewrite rules
  and are stated with the functor laws of `u` as rules (this file imports `Rules.Functor`), with
  identities and composites over the identity and composite functors;
* vertical functors `VertFunctor D E`, the displayed functors over `𝟭 A`, with scoped notation
  `F ⋙ᵥ G` for their composite, and vertical natural transformations `VertNatTrans F G` (with
  components over identities), forming the category `VertFunctor D E`. As in Mathlib's functor
  categories, vertical natural isomorphisms are the isomorphisms `F ≅ G` of this category; the
  `VertNatIso` namespace has their components (`VertNatIso.app`, `VertNatIso.hom_inv_id_app`, …)
  and `VertNatIso.ofComponents`.

A vertical functor sends a morphism over `f` to one over `(𝟭 A).map f`, which is `f` by unfolding
`𝟭 A`. The composite of two vertical functors lies over `𝟭 A ⋙ 𝟭 A`, which is `𝟭 A` by the rule
`Functor.id_comp`, so it is again a vertical functor.

The cancellation lemmas of vertical natural isomorphisms are not rewrite rules: they are keyed on
displayed composition, and trying them on every displayed composite is too slow.

The total category is in `Displayed/Displayed/Total.lean`, and equivalences over `A` are in
`Displayed/Displayed/Equivalence.lean`.

Requires the `rewrite-rules` fork of Lean.
-/

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆ v₇ u₇

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
    := by intros; rfl
  comp_id : ∀ {a a' : A} {f : a ⟶ a'} {x : Ob a} {y : Ob a'} (φ : Hom f x y), comp φ (id y) = φ
    := by intros; rfl
  assoc : ∀ {a a' a'' a''' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {h : a'' ⟶ a'''}
    {x : Ob a} {y : Ob a'} {z : Ob a''} {w : Ob a'''} (φ : Hom f x y) (ψ : Hom g y z)
    (χ : Hom h z w), comp (comp φ ψ) χ = comp φ (comp ψ χ) := by intros; rfl

attribute [rewrite_rule] Displayed.id_comp Displayed.comp_id Displayed.assoc

namespace Displayed

/-- Notation for the displayed identity morphism, mirroring `𝟙` for categories. -/
scoped notation "𝟙ᵈ" => Displayed.id _

/-- Notation for displayed composition, mirroring `≫` for categories. -/
scoped notation:80 φ:81 " ≫ᵈ " ψ:80 => Displayed.comp _ φ ψ

/-- Notation for a displayed hom-type: `x ⟶[f] y` is the type of displayed morphisms from `x` to
`y` lying over the base morphism `f`. -/
scoped notation:10 x " ⟶[" f "] " y => Displayed.Hom _ f x y

/-- Displayed categories are determined by their objects, morphisms, identities and composition,
compared heterogeneously since their types depend on the objects and morphisms. (The kernel can
reject an `rfl` between two displayed categories that it accepts on each component.) -/
theorem ext_heq {D E : Displayed.{v₁, u₁, v₂, u₂} A} (hOb : D.Ob = E.Ob) (hHom : @D.Hom ≍ @E.Hom)
    (hid : @D.id ≍ @E.id) (hcomp : @D.comp ≍ @E.comp) : D = E := by
  obtain ⟨Ob, Hom, id, comp, _, _, _⟩ := D
  obtain ⟨Ob', Hom', id', comp', _, _, _⟩ := E
  -- Restated on the fields, so that the substitutions do not go through projections of `mk`,
  -- which the rules on `Displayed.comp` and `Displayed.id` would rewrite.
  change Ob = Ob' at hOb
  subst hOb
  change @Hom ≍ @Hom' at hHom
  obtain rfl := eq_of_heq hHom
  change @id ≍ @id' at hid
  obtain rfl := eq_of_heq hid
  change @comp ≍ @comp' at hcomp
  obtain rfl := eq_of_heq hcomp
  rfl

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

variable {D} in
/-- Cancellation of a vertical isomorphism `i : x ≅ y` before a displayed morphism. -/
theorem _root_.CategoryTheory.Iso.inv_hom_id_displayed {a a' : A} {g : a ⟶ a'}
    {x y : D.Fiber a} (i : x ≅ y) {z : D.Ob a'} (ψ : y ⟶[g] z) :
    i.inv ≫ᵈ (i.hom ≫ᵈ ψ) = ψ :=
  (congrArg (· ≫ᵈ ψ) i.inv_hom_id :)

end Fiber

/-! ## Displayed functors -/

section DispFunctor

variable {B : Type u₄} [Category.{v₄} B]

/-- A displayed functor over `u : A ⥤ B`: objects over `a` go to objects over `u a`, and
morphisms over `f` to morphisms over `u f`. Its laws are stated with the functor laws of `u` as
rules, so that `u (𝟙 a)` is `𝟙 (u a)` and `u (f ≫ g)` is `u f ≫ u g`. -/
structure DispFunctor (u : A ⥤ B) (D : Displayed.{v₁, u₁, v₂, u₂} A)
    (E : Displayed.{v₄, u₄, v₅, u₅} B) where
  /-- The action on objects. -/
  obj : {a : A} → D.Ob a → E.Ob (u.obj a)
  /-- The action on morphisms, over the image of the base morphism. -/
  map : {a a' : A} → {f : a ⟶ a'} → {x : D.Ob a} → {y : D.Ob a'} → (x ⟶[f] y) →
    (obj x ⟶[u.map f] obj y)
  map_id : ∀ {a : A} (x : D.Ob a), map (𝟙ᵈ x) = 𝟙ᵈ (obj x) := by intros; rfl
  map_comp : ∀ {a a' a'' : A} {f : a ⟶ a'} {g : a' ⟶ a''} {x : D.Ob a} {y : D.Ob a'}
    {z : D.Ob a''} (φ : x ⟶[f] y) (ψ : y ⟶[g] z), map (φ ≫ᵈ ψ) = map φ ≫ᵈ map ψ := by intros; rfl

attribute [rewrite_rule] DispFunctor.map_id DispFunctor.map_comp

namespace DispFunctor

variable {u : A ⥤ B} {D : Displayed.{v₁, u₁, v₂, u₂} A} {E : Displayed.{v₄, u₄, v₅, u₅} B}

/-- Displayed functors are determined by their actions on objects and morphisms. -/
theorem ext {H K : DispFunctor u D E} (hobj : ∀ {a : A} (x : D.Ob a), H.obj x = K.obj x)
    (hmap : ∀ {a a' : A} {f : a ⟶ a'} {x : D.Ob a} {y : D.Ob a'} (φ : x ⟶[f] y),
      H.map φ ≍ K.map φ) : H = K := by
  obtain ⟨obj, map, _, _⟩ := H
  obtain ⟨obj', map', _, _⟩ := K
  obtain rfl : @obj = @obj' := by
    funext a x
    exact hobj x
  obtain rfl : @map = @map' := by
    funext a a' f x y φ
    exact eq_of_heq (hmap φ)
  rfl

/-- The identity displayed functor, over the identity functor. -/
protected def id (D : Displayed.{v₁, u₁, v₂, u₂} A) : DispFunctor (𝟭 A) D D where
  obj x := x
  map φ := φ

/-- Composition of displayed functors, over the composite functor. -/
def comp {C : Type u₆} [Category.{v₆} C] {v : B ⥤ C} {E' : Displayed.{v₆, u₆, v₇, u₇} C}
    (H : DispFunctor u D E) (K : DispFunctor v E E') : DispFunctor (u ⋙ v) D E' where
  obj x := K.obj (H.obj x)
  map φ := K.map (H.map φ)

end DispFunctor

end DispFunctor

/-! ## Vertical functors -/

section VertFunctor

/-- A vertical functor: a displayed functor over the identity of `A`, i.e. a functor over `A`
between the total categories. -/
abbrev VertFunctor (D : Displayed.{v₁, u₁, v₂, u₂} A) (E : Displayed.{v₁, u₁, v₃, u₃} A) :=
  DispFunctor (𝟭 A) D E

variable {E : Displayed.{v₁, u₁, v₃, u₃} A} {E' : Displayed.{v₁, u₁, v₄, u₄} A}

/-- The identity vertical functor. -/
abbrev VertFunctor.id (D : Displayed.{v₁, u₁, v₂, u₂} A) : VertFunctor D D :=
  DispFunctor.id D

/-- Composition of vertical functors, their composite as displayed functors: it lies over
`𝟭 A ⋙ 𝟭 A`, which is `𝟭 A` by the rule `Functor.id_comp`. -/
abbrev VertFunctor.comp {D : Displayed.{v₁, u₁, v₂, u₂} A} (F : VertFunctor D E)
    (G : VertFunctor E E') : VertFunctor D E' :=
  DispFunctor.comp F G

/-- Notation for composition of vertical functors, mirroring `⋙` for functors: `F ⋙ᵥ G` is `F`
followed by `G`. -/
scoped infixr:80 " ⋙ᵥ " => Displayed.VertFunctor.comp

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

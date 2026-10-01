import Rules.Category
import Mathlib.CategoryTheory.Bicategory.Basic

/-!
# Pseudo double categories

A (pseudo) double category, following the presentation of van der Weide, Rasekh, Ahrens and
North, *Univalent double categories* (CPP 2024), without the univalence conditions. It consists
of

* a category `C` of objects and vertical morphisms;
* a two-sided displayed category `TwoSidedDispCat C C` over `C` and `C`, whose objects over
  `(x, y)` are the horizontal morphisms `x ⇸ y` and whose morphisms over `(f, g)` are the squares
  ```
      h
   x ──⇸ y
   │f     │g
   ↓      ↓
   x' ─⇸ y'
      k
  ```
  written `Sq f g h k`, composed vertically by `s ≫ᵥ t`;
* horizontal identities `hId x : x ⇸ x` and a functorial action `hIdSq f` on vertical
  morphisms (the paper's `hor_id`);
* horizontal composition `h ⊙ k` of horizontal morphisms and `s ⊡ t` of squares, functorial for
  vertical composition (the paper's `hor_comp`);
* left and right unitors `lunitor h : Sq (𝟙 x) (𝟙 y) (hId x ⊙ h) h`, `runitor h`, and an
  associator `associator h k l : Sq (𝟙 w) (𝟙 z) ((h ⊙ k) ⊙ l) (h ⊙ (k ⊙ l))`, each invertible and
  natural in squares (the paper's `double_cat_lunitor`, `double_cat_runitor`,
  `double_cat_associator`);
* the triangle and pentagon laws.

In the paper the laws of a displayed category live over the laws of the base, so stating them
requires transporting along `𝟙 x ≫ f = f` and friends. Here the category laws of `C` are rewrite
rules, so the two sides of, say, `𝟙ᵥ h ≫ᵥ s = s` have definitionally equal types `Sq (𝟙 x ≫ f)
(𝟙 y ≫ g) h k ≡ Sq f g h k`, and all laws are stated as plain equations without transport. The
laws of the displayed category, the functoriality of `hIdSq` and the preservation of identities by
`⊡` are rules too. The interchange law `(s ≫ᵥ s') ⊡ (t ≫ᵥ t') = (s ⊡ t) ≫ᵥ (s' ⊡ t')` is not:
it overlaps with `vid_vcomp`, so `(𝟙ᵥ h ≫ᵥ 𝟙ᵥ h) ⊡ (η ≫ᵥ θ)` and `𝟙ᵥ h ⊡ (η ≫ᵥ θ)` would stop being
definitionally equal, which breaks the whiskering laws below.

As an application, the horizontal morphisms and globular squares of a double category form a
bicategory, `DoubleCategory.Horizontal C`. Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory

universe w₁ w₂ v₁ v₂ v u₁ u₂ u

/-! ## Two-sided displayed categories -/

/-- A two-sided displayed category over `C` and `D`: for `x : C` and `y : D` a type `Hor x y` of
objects over `(x, y)`, and for `f : x ⟶ x'`, `g : y ⟶ y'` a type `Sq f g h k` of morphisms over
`(f, g)`, with identities and composition over those of `C` and `D`. -/
class TwoSidedDispCat (C : Type u₁) [Category.{v₁} C] (D : Type u₂) [Category.{v₂} D] where
  /-- The objects over `(x, y)`; in a double category, the horizontal morphisms `x ⇸ y`. -/
  Hor : C → D → Type w₁
  /-- The morphisms from `h` to `k` over `(f, g)`; in a double category, the squares. -/
  Sq {x x' : C} {y y' : D} (f : x ⟶ x') (g : y ⟶ y') : Hor x y → Hor x' y' → Type w₂
  /-- The identity square over `(𝟙 x, 𝟙 y)`. -/
  vid {x : C} {y : D} (h : Hor x y) : Sq (𝟙 x) (𝟙 y) h h
  /-- Vertical composition of squares, over the composites in `C` and `D`. -/
  vcomp {x x' x'' : C} {y y' y'' : D} {f : x ⟶ x'} {f' : x' ⟶ x''} {g : y ⟶ y'}
    {g' : y' ⟶ y''} {h : Hor x y} {k : Hor x' y'} {l : Hor x'' y''} :
    Sq f g h k → Sq f' g' k l → Sq (f ≫ f') (g ≫ g') h l
  vid_vcomp {x x' : C} {y y' : D} {f : x ⟶ x'} {g : y ⟶ y'} {h : Hor x y} {k : Hor x' y'}
    (s : Sq f g h k) : vcomp (vid h) s = s
  vcomp_vid {x x' : C} {y y' : D} {f : x ⟶ x'} {g : y ⟶ y'} {h : Hor x y} {k : Hor x' y'}
    (s : Sq f g h k) : vcomp s (vid k) = s
  vcomp_assoc {x₀ x₁ x₂ x₃ : C} {y₀ y₁ y₂ y₃ : D} {f₁ : x₀ ⟶ x₁} {f₂ : x₁ ⟶ x₂} {f₃ : x₂ ⟶ x₃}
    {g₁ : y₀ ⟶ y₁} {g₂ : y₁ ⟶ y₂} {g₃ : y₂ ⟶ y₃} {h₀ : Hor x₀ y₀} {h₁ : Hor x₁ y₁}
    {h₂ : Hor x₂ y₂} {h₃ : Hor x₃ y₃} (s : Sq f₁ g₁ h₀ h₁) (t : Sq f₂ g₂ h₁ h₂)
    (r : Sq f₃ g₃ h₂ h₃) : vcomp (vcomp s t) r = vcomp s (vcomp t r)

attribute [rewrite_rule] TwoSidedDispCat.vid_vcomp TwoSidedDispCat.vcomp_vid
  TwoSidedDispCat.vcomp_assoc

namespace TwoSidedDispCat

@[inherit_doc] scoped infixr:10 " ⇸ " => TwoSidedDispCat.Hor
@[inherit_doc] scoped prefix:max "𝟙ᵥ " => TwoSidedDispCat.vid
@[inherit_doc] scoped infixr:80 " ≫ᵥ " => TwoSidedDispCat.vcomp

end TwoSidedDispCat

open TwoSidedDispCat

/-! ## Double categories -/

/-- A pseudo double category with objects and vertical morphisms `C`. -/
class DoubleCategory (C : Type u) [Category.{v} C] extends TwoSidedDispCat.{w₁, w₂} C C where
  -- Horizontal identities
  /-- The horizontal identity `x ⇸ x`. -/
  hId (x : C) : x ⇸ x
  /-- The horizontal identity square on a vertical morphism. -/
  hIdSq {x y : C} (f : x ⟶ y) : Sq f f (hId x) (hId y)
  hIdSq_id (x : C) : hIdSq (𝟙 x) = vid (hId x)
  hIdSq_comp {x y z : C} (f : x ⟶ y) (g : y ⟶ z) : hIdSq (f ≫ g) = vcomp (hIdSq f) (hIdSq g)
  -- Horizontal composition
  /-- Horizontal composition of horizontal morphisms, in diagrammatic order. -/
  hComp {x y z : C} : (x ⇸ y) → (y ⇸ z) → (x ⇸ z)
  /-- Horizontal composition of squares. -/
  hCompSq {x x' y y' z z' : C} {f : x ⟶ x'} {g : y ⟶ y'} {k : z ⟶ z'} {h : x ⇸ y}
    {h' : x' ⇸ y'} {l : y ⇸ z} {l' : y' ⇸ z'} :
    Sq f g h h' → Sq g k l l' → Sq f k (hComp h l) (hComp h' l')
  hCompSq_id {x y z : C} (h : x ⇸ y) (l : y ⇸ z) : hCompSq (vid h) (vid l) = vid (hComp h l)
  hCompSq_comp {x x' x'' y y' y'' z z' z'' : C} {f : x ⟶ x'} {f' : x' ⟶ x''} {g : y ⟶ y'}
    {g' : y' ⟶ y''} {k : z ⟶ z'} {k' : z' ⟶ z''} {h : x ⇸ y} {h' : x' ⇸ y'} {h'' : x'' ⇸ y''}
    {l : y ⇸ z} {l' : y' ⇸ z'} {l'' : y'' ⇸ z''} (s : Sq f g h h') (s' : Sq f' g' h' h'')
    (t : Sq g k l l') (t' : Sq g' k' l' l'') :
    hCompSq (vcomp s s') (vcomp t t') = vcomp (hCompSq s t) (hCompSq s' t')
  -- Left unitor
  /-- The left unitor `hId x ⊙ h ⇒ h`. -/
  lunitor {x y : C} (h : x ⇸ y) : Sq (𝟙 x) (𝟙 y) (hComp (hId x) h) h
  /-- The inverse of the left unitor. -/
  lunitorInv {x y : C} (h : x ⇸ y) : Sq (𝟙 x) (𝟙 y) h (hComp (hId x) h)
  lunitor_hom_inv {x y : C} (h : x ⇸ y) : vcomp (lunitor h) (lunitorInv h) = vid _
  lunitor_inv_hom {x y : C} (h : x ⇸ y) : vcomp (lunitorInv h) (lunitor h) = vid h
  lunitor_naturality {x x' y y' : C} {f : x ⟶ x'} {g : y ⟶ y'} {h : x ⇸ y} {h' : x' ⇸ y'}
    (s : Sq f g h h') : vcomp (lunitor h) s = vcomp (hCompSq (hIdSq f) s) (lunitor h')
  -- Right unitor
  /-- The right unitor `h ⊙ hId y ⇒ h`. -/
  runitor {x y : C} (h : x ⇸ y) : Sq (𝟙 x) (𝟙 y) (hComp h (hId y)) h
  /-- The inverse of the right unitor. -/
  runitorInv {x y : C} (h : x ⇸ y) : Sq (𝟙 x) (𝟙 y) h (hComp h (hId y))
  runitor_hom_inv {x y : C} (h : x ⇸ y) : vcomp (runitor h) (runitorInv h) = vid _
  runitor_inv_hom {x y : C} (h : x ⇸ y) : vcomp (runitorInv h) (runitor h) = vid h
  runitor_naturality {x x' y y' : C} {f : x ⟶ x'} {g : y ⟶ y'} {h : x ⇸ y} {h' : x' ⇸ y'}
    (s : Sq f g h h') : vcomp (runitor h) s = vcomp (hCompSq s (hIdSq g)) (runitor h')
  -- Associator
  /-- The associator `(h ⊙ k) ⊙ l ⇒ h ⊙ (k ⊙ l)`. -/
  associator {w x y z : C} (h : w ⇸ x) (k : x ⇸ y) (l : y ⇸ z) :
    Sq (𝟙 w) (𝟙 z) (hComp (hComp h k) l) (hComp h (hComp k l))
  /-- The inverse of the associator. -/
  associatorInv {w x y z : C} (h : w ⇸ x) (k : x ⇸ y) (l : y ⇸ z) :
    Sq (𝟙 w) (𝟙 z) (hComp h (hComp k l)) (hComp (hComp h k) l)
  associator_hom_inv {w x y z : C} (h : w ⇸ x) (k : x ⇸ y) (l : y ⇸ z) :
    vcomp (associator h k l) (associatorInv h k l) = vid _
  associator_inv_hom {w x y z : C} (h : w ⇸ x) (k : x ⇸ y) (l : y ⇸ z) :
    vcomp (associatorInv h k l) (associator h k l) = vid _
  associator_naturality {w w' x x' y y' z z' : C} {f : w ⟶ w'} {g : x ⟶ x'} {i : y ⟶ y'}
    {j : z ⟶ z'} {h : w ⇸ x} {h' : w' ⇸ x'} {k : x ⇸ y} {k' : x' ⇸ y'} {l : y ⇸ z}
    {l' : y' ⇸ z'} (s : Sq f g h h') (t : Sq g i k k') (r : Sq i j l l') :
    vcomp (associator h k l) (hCompSq s (hCompSq t r)) =
      vcomp (hCompSq (hCompSq s t) r) (associator h' k' l')
  -- Coherence
  triangle {x y z : C} (h : x ⇸ y) (k : y ⇸ z) :
    vcomp (associator h (hId y) k) (hCompSq (vid h) (lunitor k)) = hCompSq (runitor h) (vid k)
  pentagon {v w x y z : C} (h : v ⇸ w) (k : w ⇸ x) (l : x ⇸ y) (m : y ⇸ z) :
    vcomp (hCompSq (associator h k l) (vid m))
        (vcomp (associator h (hComp k l) m) (hCompSq (vid h) (associator k l m))) =
      vcomp (associator (hComp h k) l m) (associator h k (hComp l m))

attribute [rewrite_rule] DoubleCategory.hIdSq_id DoubleCategory.hIdSq_comp
  DoubleCategory.hCompSq_id

namespace DoubleCategory

@[inherit_doc] scoped infixr:81 " ⊙ " => DoubleCategory.hComp
@[inherit_doc] scoped infixr:81 " ⊡ " => DoubleCategory.hCompSq

variable {C : Type u} [Category.{v} C] [DoubleCategory.{w₁, w₂} C]

/-! ## Definitional laws -/

example {x y : C} {f : y ⟶ y} (h : x ⇸ y) (k : x ⇸ y) (s : Sq (𝟙 x) f h k) :
    𝟙ᵥ h ≫ᵥ s ≫ᵥ 𝟙ᵥ k = s := rfl

example {x y z w : C} (f : x ⟶ y) (g : y ⟶ z) (i : z ⟶ w) :
    hIdSq ((𝟙 x ≫ f) ≫ g ≫ i) = hIdSq f ≫ᵥ hIdSq g ≫ᵥ hIdSq i := rfl

example {x y z : C} (h : x ⇸ y) (k : y ⇸ z) : hIdSq (𝟙 x) ⊡ 𝟙ᵥ h ⊡ 𝟙ᵥ k = 𝟙ᵥ (hId x ⊙ h ⊙ k) :=
  rfl

/-! ## The horizontal bicategory -/

section Horizontal

variable {x y z w : C}

theorem hId_hCompSq {f g : x ⇸ y} (η : Sq (𝟙 x) (𝟙 y) f g) :
    𝟙ᵥ (hId x) ⊡ η = lunitor f ≫ᵥ η ≫ᵥ lunitorInv g :=
  calc 𝟙ᵥ (hId x) ⊡ η = (𝟙ᵥ (hId x) ⊡ η) ≫ᵥ lunitor g ≫ᵥ lunitorInv g := by
        rw [lunitor_hom_inv]
    _ = (lunitor f ≫ᵥ η) ≫ᵥ lunitorInv g := by rw [lunitor_naturality η]

theorem hCompSq_hId {f g : x ⇸ y} (η : Sq (𝟙 x) (𝟙 y) f g) :
    η ⊡ 𝟙ᵥ (hId y) = runitor f ≫ᵥ η ≫ᵥ runitorInv g :=
  calc η ⊡ 𝟙ᵥ (hId y) = (η ⊡ 𝟙ᵥ (hId y)) ≫ᵥ runitor g ≫ᵥ runitorInv g := by
        rw [runitor_hom_inv]
    _ = (runitor f ≫ᵥ η) ≫ᵥ runitorInv g := by rw [runitor_naturality η]

theorem hComp_hCompSq (f : x ⇸ y) (g : y ⇸ z) {h h' : z ⇸ w} (η : Sq (𝟙 z) (𝟙 w) h h') :
    𝟙ᵥ (f ⊙ g) ⊡ η = associator f g h ≫ᵥ (𝟙ᵥ f ⊡ 𝟙ᵥ g ⊡ η) ≫ᵥ associatorInv f g h' :=
  calc 𝟙ᵥ (f ⊙ g) ⊡ η
      = ((𝟙ᵥ f ⊡ 𝟙ᵥ g) ⊡ η) ≫ᵥ associator f g h' ≫ᵥ associatorInv f g h' := by
        rw [associator_hom_inv]
    _ = (associator f g h ≫ᵥ (𝟙ᵥ f ⊡ 𝟙ᵥ g ⊡ η)) ≫ᵥ associatorInv f g h' := by
        rw [associator_naturality (𝟙ᵥ f) (𝟙ᵥ g) η]

theorem hCompSq_hComp {f f' : x ⇸ y} (η : Sq (𝟙 x) (𝟙 y) f f') (g : y ⇸ z) (h : z ⇸ w) :
    η ⊡ 𝟙ᵥ (g ⊙ h) = associatorInv f g h ≫ᵥ ((η ⊡ 𝟙ᵥ g) ⊡ 𝟙ᵥ h) ≫ᵥ associator f' g h :=
  calc η ⊡ 𝟙ᵥ (g ⊙ h)
      = (associatorInv f g h ≫ᵥ associator f g h) ≫ᵥ (η ⊡ 𝟙ᵥ g ⊡ 𝟙ᵥ h) := by
        rw [associator_inv_hom]
    _ = associatorInv f g h ≫ᵥ (associator f g h ≫ᵥ (η ⊡ 𝟙ᵥ g ⊡ 𝟙ᵥ h)) := rfl
    _ = associatorInv f g h ≫ᵥ ((η ⊡ 𝟙ᵥ g) ⊡ 𝟙ᵥ h) ≫ᵥ associator f' g h := by
        rw [associator_naturality η (𝟙ᵥ g) (𝟙ᵥ h)]

theorem hCompSq_assoc (f : x ⇸ y) {g g' : y ⇸ z} (η : Sq (𝟙 y) (𝟙 z) g g') (h : z ⇸ w) :
    (𝟙ᵥ f ⊡ η) ⊡ 𝟙ᵥ h = associator f g h ≫ᵥ (𝟙ᵥ f ⊡ η ⊡ 𝟙ᵥ h) ≫ᵥ associatorInv f g' h :=
  calc (𝟙ᵥ f ⊡ η) ⊡ 𝟙ᵥ h
      = ((𝟙ᵥ f ⊡ η) ⊡ 𝟙ᵥ h) ≫ᵥ associator f g' h ≫ᵥ associatorInv f g' h := by
        rw [associator_hom_inv]
    _ = (associator f g h ≫ᵥ (𝟙ᵥ f ⊡ η ⊡ 𝟙ᵥ h)) ≫ᵥ associatorInv f g' h := by
        rw [associator_naturality (𝟙ᵥ f) η (𝟙ᵥ h)]

variable (C) in
/-- A copy of the objects of `C`, carrying the horizontal bicategory. -/
structure Horizontal where
  /-- An object of `Horizontal C` from an object of `C`. -/
  of ::
  /-- The underlying object of `C`. -/
  as : C

/-- The category of horizontal morphisms `x ⇸ y` and globular squares, those whose vertical
boundaries are identities.

The composite `η ≫ᵥ θ` is used at `Sq (𝟙 x) (𝟙 y) f h`, so in `(η ≫ᵥ θ) ≫ᵥ ι` the implicit
boundary of the outer `vcomp` is `𝟙 x` rather than the `𝟙 x ≫ 𝟙 x` of the left-hand side of the
rule `vcomp_assoc`. Rules match implicit arguments up to definitional equality, so associativity
still holds by `rfl`. -/
@[instance_reducible]
def globular (x y : C) : Category (x ⇸ y) where
  Hom f g := Sq (𝟙 x) (𝟙 y) f g
  id f := 𝟙ᵥ f
  comp η θ := η ≫ᵥ θ
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

attribute [local instance] globular

/-- The associator as an isomorphism of globular squares. -/
def associatorIso (f : x ⇸ y) (g : y ⇸ z) (h : z ⇸ w) : (f ⊙ g) ⊙ h ≅ f ⊙ g ⊙ h where
  hom := associator f g h
  inv := associatorInv f g h
  hom_inv_id := associator_hom_inv f g h
  inv_hom_id := associator_inv_hom f g h

/-- The left unitor as an isomorphism of globular squares. -/
def lunitorIso (f : x ⇸ y) : hId x ⊙ f ≅ f where
  hom := lunitor f
  inv := lunitorInv f
  hom_inv_id := lunitor_hom_inv f
  inv_hom_id := lunitor_inv_hom f

/-- The right unitor as an isomorphism of globular squares. -/
def runitorIso (f : x ⇸ y) : f ⊙ hId y ≅ f where
  hom := runitor f
  inv := runitorInv f
  hom_inv_id := runitor_hom_inv f
  inv_hom_id := runitor_inv_hom f

/-- The horizontal bicategory of a double category: its 1-cells are horizontal morphisms and its
2-cells are globular squares, those whose vertical boundaries are identities. -/
instance : Bicategory (Horizontal C) where
  Hom x y := x.as ⇸ y.as
  id x := hId x.as
  comp f g := f ⊙ g
  homCategory x y := globular x.as y.as
  whiskerLeft f _ _ η := 𝟙ᵥ f ⊡ η
  whiskerRight η h := η ⊡ 𝟙ᵥ h
  associator := associatorIso
  leftUnitor := lunitorIso
  rightUnitor := runitorIso
  whiskerLeft_id _ _ := rfl
  whiskerLeft_comp f _ _ _ η θ := hCompSq_comp (𝟙ᵥ f) (𝟙ᵥ f) η θ
  id_whiskerLeft η := hId_hCompSq η
  comp_whiskerLeft f g _ _ η := hComp_hCompSq f g η
  id_whiskerRight _ _ := rfl
  comp_whiskerRight η θ i := hCompSq_comp η θ (𝟙ᵥ i) (𝟙ᵥ i)
  whiskerRight_id η := hCompSq_hId η
  whiskerRight_comp η g h := hCompSq_hComp η g h
  whisker_assoc f _ _ η h := hCompSq_assoc f η h
  whisker_exchange {_ _ _ f g h i} η θ :=
    (hCompSq_comp (𝟙ᵥ f) η θ (𝟙ᵥ i)).symm.trans (hCompSq_comp η (𝟙ᵥ g) (𝟙ᵥ h) θ)
  pentagon f g h i := pentagon f g h i
  triangle f g := triangle f g

end Horizontal

end DoubleCategory

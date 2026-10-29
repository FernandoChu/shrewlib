import Bicategory.Arrow
import Bicategory.Comma
import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor

/-!
# The comma factorization in a 2-category

In a 2-category `B` with comma objects, every 1-cell `f : A ⟶ B` factors as
`f = Lf ≫ Rf : A ⟶ f/B ⟶ B`, through the comma object `f/B` of `f` and `𝟙 B`, with legs
`q_f : f/B ⟶ A` and `Rf : f/B ⟶ B` and universal 2-cell `ν_f : q_f ≫ f ⟶ Rf`:
```
   A ──────𝟙──────╮
   │ ╲            ▼
   │  Lf   f/B ─q_f─▶ A
   f    ╲  │    ⇙ν_f  │
   │     ▶ Rf         f
   ▼       ▼          ▼
   B ═════ B ════════ B
```
`Lf : A ⟶ f/B` is induced by the identity 2-cell of `f`, so `Lf ≫ q_f = 𝟙 A` and `Lf ≫ Rf = f`,
by `rfl` since the universal property of comma objects is a rule.

This is a 2-functorial factorization. A square `m : f ⟶ g` of the arrow 2-category `Arr B`
induces `commaMap m : f/B ⟶ g/D` by the 1-dimensional universal property, and a 2-cell of squares
`α : m ⟶ n` induces `commaMap₂ α : commaMap m ⟶ commaMap n` by the 2-dimensional one. They are
strictly functorial and preserve whiskerings, which are rules. So `L` and `R` are strict
2-functors `Arr B ⥤ Arr B` (Mathlib's `StrictPseudofunctor`):

* `L` sends `f` to `Lf`, `m` to the square `(m.left, commaMap m)` and `α` to
  `(α.left, commaMap₂ α)`;
* `R` sends `f` to `Rf`, `m` to the square `(commaMap m, m.right)` and `α` to
  `(commaMap₂ α, α.right)`.

They compose to the identity: `(L.obj f).hom ≫ (R.obj f).hom = f.hom`, and the middle components of
`L` and `R` agree on objects, 1-cells and 2-cells (`L_obj_cod`, `L_map_right`, `L_map₂_right`), all
by `rfl`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] [HasCommas B]

open HasCommas

namespace Arr

variable (f : Arr B)

/-- The comma object `f/B` of `f` and the identity of its codomain. -/
abbrev commaObj : B :=
  comma f.hom (𝟙 f.cod)

/-- The first map of the factorization, `Lf : A ⟶ f/B`, induced by the identity 2-cell of `f`. -/
def lMap : f.dom ⟶ f.commaObj :=
  (isComma f.hom (𝟙 f.cod)).lift ⟨𝟙 f.dom, f.hom, 𝟙 f.hom⟩

/-- `Lf` is a section of the projection `q_f : f/B ⟶ A`. -/
theorem lMap_comp_left : f.lMap ≫ (commaCone f.hom (𝟙 f.cod)).left = 𝟙 f.dom :=
  rfl

/-- The factorization `f = Lf ≫ Rf`. -/
theorem lMap_comp_right : f.lMap ≫ (commaCone f.hom (𝟙 f.cod)).right = f.hom :=
  rfl

variable {f} {g h : Arr B}

/-- The 1-cell between comma objects induced by a square, by the 1-dimensional universal property
of `g/D`: the universal 2-cell of `f/B` whiskered with `m.right`. -/
def commaMap (m : f ⟶ g) : f.commaObj ⟶ g.commaObj :=
  (isComma g.hom (𝟙 g.cod)).lift
    ⟨(commaCone f.hom (𝟙 f.cod)).left ≫ m.left, (commaCone f.hom (𝟙 f.cod)).right ≫ m.right,
      (commaCone f.hom (𝟙 f.cod)).hom ▷ m.right⟩

/-- The 2-cell between induced 1-cells induced by a 2-cell of squares, by the 2-dimensional
universal property of `g/D`. -/
def commaMap₂ {m n : f ⟶ g} (α : m ⟶ n) : commaMap m ⟶ commaMap n :=
  (isComma g.hom (𝟙 g.cod)).lift₂
    (CommaCone.homMk ((commaCone f.hom (𝟙 f.cod)).left ◁ α.left)
      ((commaCone f.hom (𝟙 f.cod)).right ◁ α.right)
      (whisker_exchange (commaCone f.hom (𝟙 f.cod)).hom α.right))

/-! ## Functoriality

The induced 1- and 2-cells are functorial, by the universal property of comma objects. These
equations are rules, so that the functors `L` and `R` below are strictly functorial by `rfl`. -/

@[rewrite_rule]
theorem commaMap_id : commaMap (𝟙 f) = 𝟙 f.commaObj :=
  (isComma _ _).ext (by kernel_rfl)

@[rewrite_rule]
theorem commaMap_comp (m : f ⟶ g) (n : g ⟶ h) : commaMap (m ≫ n) = commaMap m ≫ commaMap n :=
  (isComma _ _).ext (by kernel_rfl)

@[rewrite_rule]
theorem commaMap₂_id (m : f ⟶ g) : commaMap₂ (𝟙 m) = 𝟙 (commaMap m) :=
  (isComma _ _).hom_ext (by kernel_rfl) (by kernel_rfl)

@[rewrite_rule]
theorem commaMap₂_comp {m n o : f ⟶ g} (α : m ⟶ n) (β : n ⟶ o) :
    commaMap₂ (α ≫ β) = commaMap₂ α ≫ commaMap₂ β :=
  (isComma _ _).hom_ext (by kernel_rfl) (by kernel_rfl)

@[rewrite_rule]
theorem commaMap₂_whiskerLeft (m : f ⟶ g) {n n' : g ⟶ h} (α : n ⟶ n') :
    commaMap₂ (m ◁ α) = commaMap m ◁ commaMap₂ α :=
  (isComma _ _).hom_ext (by kernel_rfl) (by kernel_rfl)

@[rewrite_rule]
theorem commaMap₂_whiskerRight {m m' : f ⟶ g} (α : m ⟶ m') (n : g ⟶ h) :
    commaMap₂ (α ▷ n) = commaMap₂ α ▷ commaMap n :=
  (isComma _ _).hom_ext (by kernel_rfl) (by kernel_rfl)

/-- Whiskering with `commaMap m` and the legs of comma objects, from the universal property. -/
@[rewrite_rule]
theorem whiskerRight_commaMap_left {f g : Arr B} (m : f ⟶ g) {x : B} {u v : x ⟶ f.commaObj}
    (θ : u ⟶ v) : θ ▷ commaMap m ▷ (commaCone g.hom (𝟙 g.cod)).left =
      θ ▷ (commaCone f.hom (𝟙 f.cod)).left ▷ m.left := by
  kernel_rfl

@[rewrite_rule]
theorem whiskerRight_commaMap_right {f g : Arr B} (m : f ⟶ g) {x : B} {u v : x ⟶ f.commaObj}
    (θ : u ⟶ v) : θ ▷ commaMap m ▷ (commaCone g.hom (𝟙 g.cod)).right =
      θ ▷ (commaCone f.hom (𝟙 f.cod)).right ▷ m.right := by
  kernel_rfl

end Arr

open Arr

/-! ## The factorization 2-functors -/

/-- The left factor `L : Arr B ⥤ Arr B`, sending `f` to `Lf : A ⟶ f/B`. -/
def L : StrictPseudofunctor (Arr B) (Arr B) :=
  StrictPseudofunctor.mk''
    { obj f := ⟨f.dom, f.commaObj, f.lMap⟩
      map m := ⟨m.left, commaMap m, (isComma _ _).ext (by kernel_rfl)⟩
      map₂ α := ⟨α.left, commaMap₂ α, (isComma _ _).hom_ext (by kernel_rfl) (by kernel_rfl)⟩
      map₂_id := by intros; kernel_rfl
      map₂_comp := by intros; kernel_rfl
      map_id := by intros; kernel_rfl
      map_comp := by intros; kernel_rfl
      map₂_whisker_left := by intros; kernel_rfl
      map₂_whisker_right := by intros; kernel_rfl }

/-- The right factor `R : Arr B ⥤ Arr B`, sending `f` to `Rf : f/B ⟶ B`. -/
def R : StrictPseudofunctor (Arr B) (Arr B) :=
  StrictPseudofunctor.mk''
    { obj f := ⟨f.commaObj, f.cod, (commaCone f.hom (𝟙 f.cod)).right⟩
      map m := ⟨commaMap m, m.right, by kernel_rfl⟩
      map₂ α := ⟨commaMap₂ α, α.right, by kernel_rfl⟩
      map₂_id := by intros; kernel_rfl
      map₂_comp := by intros; kernel_rfl
      map_id := by intros; kernel_rfl
      map_comp := by intros; kernel_rfl
      map₂_whisker_left := by intros; kernel_rfl
      map₂_whisker_right := by intros; kernel_rfl }

/-! ## The factorization

The components of `L` and `R` are rules, as the matcher of rules does not unfold their
definitions to find them. -/

section

variable {f g : Arr B} {m n : f ⟶ g}

@[rewrite_rule] theorem L_obj_hom' (f : Arr B) : (L.obj f).hom = f.lMap := rfl
@[rewrite_rule] theorem R_obj_hom' (f : Arr B) :
    (R.obj f).hom = (commaCone f.hom (𝟙 f.cod)).right := rfl
@[rewrite_rule] theorem L_map_left' (m : f ⟶ g) : (L.map m).left = m.left := rfl
@[rewrite_rule] theorem L_map_right' (m : f ⟶ g) : (L.map m).right = commaMap m := rfl
@[rewrite_rule] theorem R_map_left' (m : f ⟶ g) : (R.map m).left = commaMap m := rfl
@[rewrite_rule] theorem R_map_right' (m : f ⟶ g) : (R.map m).right = m.right := rfl
@[rewrite_rule] theorem L_map₂_left' (α : m ⟶ n) : (L.map₂ α).left = α.left := rfl
@[rewrite_rule] theorem L_map₂_right' (α : m ⟶ n) : (L.map₂ α).right = commaMap₂ α := rfl
@[rewrite_rule] theorem R_map₂_left' (α : m ⟶ n) : (R.map₂ α).left = commaMap₂ α := rfl
@[rewrite_rule] theorem R_map₂_right' (α : m ⟶ n) : (R.map₂ α).right = α.right := rfl

end

variable (f : Arr B)

theorem L_obj_dom : (L.obj f).dom = f.dom :=
  rfl

theorem L_obj_cod : (L.obj f).cod = (R.obj f).dom :=
  rfl

theorem R_obj_cod : (R.obj f).cod = f.cod :=
  rfl

/-- `L` and `R` factor every arrow. -/
theorem L_obj_hom_comp_R_obj_hom : (L.obj f).hom ≫ (R.obj f).hom = f.hom :=
  rfl

variable {f} {g : Arr B}

theorem L_map_left (m : f ⟶ g) : (L.map m).left = m.left :=
  rfl

theorem L_map_right (m : f ⟶ g) : (L.map m).right = (R.map m).left :=
  rfl

theorem R_map_right (m : f ⟶ g) : (R.map m).right = m.right :=
  rfl

theorem L_map₂_left {m n : f ⟶ g} (α : m ⟶ n) : (L.map₂ α).left = α.left :=
  rfl

theorem L_map₂_right {m n : f ⟶ g} (α : m ⟶ n) : (L.map₂ α).right = (R.map₂ α).left :=
  rfl

theorem R_map₂_right {m n : f ⟶ g} (α : m ⟶ n) : (R.map₂ α).right = α.right :=
  rfl

end CategoryTheory.TwoCategory

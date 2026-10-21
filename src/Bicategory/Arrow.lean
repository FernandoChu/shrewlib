import Bicategory.Basic

/-!
# The arrow 2-category

The arrows of a 2-category `B` form a 2-category `Arr B`:

* an object `f : Arr B` is a 1-cell `f.hom : f.dom ⟶ f.cod` of `B`;
* a 1-cell `m : f ⟶ g` is a commutative square: 1-cells `m.left : f.dom ⟶ g.dom` and
  `m.right : f.cod ⟶ g.cod` with `m.left ≫ g.hom = f.hom ≫ m.right`;
* a 2-cell `α : m ⟶ n` is a pair of 2-cells `α.left : m.left ⟶ n.left` and
  `α.right : m.right ⟶ n.right` with `α.left ▷ g.hom = f.hom ◁ α.right`.

The equations of squares are rules (also reassociated and whiskered), so the two sides of the
equation of 2-cells have the same type `m.left ≫ g.hom ⟶ n.left ≫ g.hom`, and it is stated without
transport. It is a rule too. Composites and whiskerings are computed componentwise, and the laws of
the 2-category hold by `rfl`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable (B : Type u) [TwoCategory.{w, v} B]

/-- An arrow of `B`: a 1-cell `hom : dom ⟶ cod`. -/
structure Arr where
  /-- The domain of the arrow. -/
  dom : B
  /-- The codomain of the arrow. -/
  cod : B
  /-- The arrow. -/
  hom : dom ⟶ cod

namespace Arr

variable {B}

/-- A 1-cell of arrows: a commutative square. -/
@[ext]
structure Hom (f g : Arr B) where
  /-- The 1-cell between the domains. -/
  left : f.dom ⟶ g.dom
  /-- The 1-cell between the codomains. -/
  right : f.cod ⟶ g.cod
  w : left ≫ g.hom = f.hom ≫ right

attribute [rewrite_rule] Hom.w

namespace Hom

variable {f g : Arr B} (m : Hom f g)

@[rewrite_rule]
theorem w_assoc {d : B} (k : g.cod ⟶ d) : m.left ≫ g.hom ≫ k = f.hom ≫ m.right ≫ k :=
  congrArg (· ≫ k) m.w

@[rewrite_rule]
theorem whiskerLeft_w {d : B} {k k' : g.cod ⟶ d} (η : k ⟶ k') :
    m.left ◁ g.hom ◁ η = f.hom ◁ m.right ◁ η :=
  eq_of_heq (whiskerLeft_congr m.w η)

@[rewrite_rule]
theorem whiskerRight_w {x : B} {u u' : x ⟶ f.dom} (θ : u ⟶ u') :
    θ ▷ m.left ▷ g.hom = θ ▷ f.hom ▷ m.right :=
  eq_of_heq (whiskerRight_congr θ m.w)

end Hom

/-- A 2-cell of arrows: a pair of 2-cells between the sides of two squares, compatible with the
arrows. -/
@[ext]
structure Hom₂ {f g : Arr B} (m n : Hom f g) where
  /-- The 2-cell between the 1-cells of the domains. -/
  left : m.left ⟶ n.left
  /-- The 2-cell between the 1-cells of the codomains. -/
  right : m.right ⟶ n.right
  w : left ▷ g.hom = f.hom ◁ right

attribute [rewrite_rule] Hom₂.w

instance categoryStruct : CategoryStruct.{v} (Arr B) where
  Hom := Hom
  id f := ⟨𝟙 f.dom, 𝟙 f.cod, rfl⟩
  comp m n := ⟨m.left ≫ n.left, m.right ≫ n.right, rfl⟩

instance homCategory (f g : Arr B) : Category.{w} (f ⟶ g) where
  Hom := Hom₂
  id m := ⟨𝟙 m.left, 𝟙 m.right, rfl⟩
  comp α β := ⟨α.left ≫ β.left, α.right ≫ β.right, rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom₂_ext {f g : Arr B} {m n : f ⟶ g} {α β : m ⟶ n} (h₁ : α.left = β.left)
    (h₂ : α.right = β.right) : α = β :=
  Hom₂.ext h₁ h₂

instance bicategory : Bicategory.{w, v} (Arr B) where
  homCategory := homCategory
  whiskerLeft m _ _ α := ⟨m.left ◁ α.left, m.right ◁ α.right, rfl⟩
  whiskerRight α n := ⟨α.left ▷ n.left, α.right ▷ n.right, rfl⟩
  associator _ _ _ := Iso.refl _
  leftUnitor _ := Iso.refl _
  rightUnitor _ := Iso.refl _
  whiskerLeft_id := by intros; rfl
  whiskerLeft_comp := by intros; rfl
  id_whiskerLeft := by intros; rfl
  comp_whiskerLeft := by intros; rfl
  id_whiskerRight := by intros; rfl
  comp_whiskerRight := by intros; rfl
  whiskerRight_id := by intros; rfl
  whiskerRight_comp := by intros; rfl
  whisker_assoc := by intros; rfl
  whisker_exchange := by intros; ext <;> exact whisker_exchange _ _
  pentagon := by intros; rfl
  triangle := by intros; rfl

/-- The arrows of a 2-category form a 2-category. -/
instance twoCategory : TwoCategory.{w, v} (Arr B) where
  toBicategory := bicategory
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  leftUnitor_eqToIso := by intros; rfl
  rightUnitor_eqToIso := by intros; rfl
  associator_eqToIso := by intros; rfl

/-! The components of the operations of `Arr B` hold by `rfl`. They are rules, as the matcher of
rules does not unfold the instances of `Arr B` to find them. -/

section

variable {f g h : Arr B}

@[simp, rewrite_rule]
theorem id_left' : (𝟙 f : f ⟶ f).left = 𝟙 f.dom := rfl
@[simp, rewrite_rule]
theorem id_right' : (𝟙 f : f ⟶ f).right = 𝟙 f.cod := rfl
@[simp, rewrite_rule]
theorem comp_left (m : f ⟶ g) (n : g ⟶ h) : (m ≫ n).left = m.left ≫ n.left := rfl
@[simp, rewrite_rule]
theorem comp_right (m : f ⟶ g) (n : g ⟶ h) : (m ≫ n).right = m.right ≫ n.right := rfl

variable {m n o : f ⟶ g}

@[simp, rewrite_rule]
theorem id₂_left : (𝟙 m : m ⟶ m).left = 𝟙 m.left := rfl
@[simp, rewrite_rule]
theorem id₂_right : (𝟙 m : m ⟶ m).right = 𝟙 m.right := rfl
@[simp, rewrite_rule]
theorem comp₂_left (α : m ⟶ n) (β : n ⟶ o) : (α ≫ β).left = α.left ≫ β.left := rfl
@[simp, rewrite_rule]
theorem comp₂_right (α : m ⟶ n) (β : n ⟶ o) : (α ≫ β).right = α.right ≫ β.right := rfl

@[simp, rewrite_rule]
theorem whiskerLeft_left (k : h ⟶ f) (α : m ⟶ n) : (k ◁ α).left = k.left ◁ α.left := rfl
@[simp, rewrite_rule]
theorem whiskerLeft_right (k : h ⟶ f) (α : m ⟶ n) : (k ◁ α).right = k.right ◁ α.right :=
  rfl
@[simp, rewrite_rule]
theorem whiskerRight_left (α : m ⟶ n) (k : g ⟶ h) : (α ▷ k).left = α.left ▷ k.left := rfl
@[simp, rewrite_rule]
theorem whiskerRight_right (α : m ⟶ n) (k : g ⟶ h) : (α ▷ k).right = α.right ▷ k.right :=
  rfl

end

end Arr

end CategoryTheory.TwoCategory

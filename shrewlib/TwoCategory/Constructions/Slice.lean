import TwoCategory.Basic

/-!
# The strict slice 2-category

For an object `b` of a 2-category `B`, the strict slice 2-category `Slice b` has:

* as objects, 1-cells `x.hom : x.obj ⟶ b`;
* as 1-cells `m : x ⟶ y`, 1-cells `m.hom : x.obj ⟶ y.obj` with `m.hom ≫ y.hom = x.hom`;
* as 2-cells `α : m ⟶ n`, 2-cells `α.hom : m.hom ⟶ n.hom` with `α.hom ▷ y.hom = 𝟙 x.hom`.

The equations of 1- and 2-cells are rules, so the equation of 2-cells is stated without transport:
both sides have type `x.hom ⟶ x.hom`. Composites and whiskerings are computed on the underlying
cells, and the laws of the 2-category hold by `rfl`.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B]

variable (b : B) in
/-- An object of the slice over `b`: a 1-cell into `b`. -/
structure Slice where
  /-- The underlying object. -/
  obj : B
  /-- The 1-cell into `b`. -/
  hom : obj ⟶ b

namespace Slice

variable {b : B}

/-- A 1-cell of the slice over `b`: a commutative triangle. -/
@[ext]
structure Hom (x y : Slice b) where
  /-- The underlying 1-cell. -/
  hom : x.obj ⟶ y.obj
  w : hom ≫ y.hom = x.hom

attribute [rewrite_rule] Hom.w

namespace Hom

variable {x y : Slice b} (m : Hom x y)

@[rewrite_rule]
theorem w_assoc {d : B} (k : b ⟶ d) : m.hom ≫ y.hom ≫ k = x.hom ≫ k :=
  congrArg (· ≫ k) m.w

@[rewrite_rule]
theorem whiskerLeft_w {d : B} {k k' : b ⟶ d} (η : k ⟶ k') : m.hom ◁ y.hom ◁ η = x.hom ◁ η :=
  eq_of_heq (whiskerLeft_congr m.w η)

@[rewrite_rule]
theorem whiskerRight_w {z : B} {u u' : z ⟶ x.obj} (θ : u ⟶ u') :
    θ ▷ m.hom ▷ y.hom = θ ▷ x.hom :=
  eq_of_heq (whiskerRight_congr θ m.w)

end Hom

/-- A 2-cell of the slice over `b`: a 2-cell between the underlying 1-cells lying over the
identity of `b`. -/
@[ext]
structure Hom₂ {x y : Slice b} (m n : Hom x y) where
  /-- The underlying 2-cell. -/
  hom : m.hom ⟶ n.hom
  w : hom ▷ y.hom = 𝟙 x.hom

attribute [rewrite_rule] Hom₂.w

instance : CategoryStruct.{v} (Slice b) where
  Hom := Hom
  id x := ⟨𝟙 x.obj, by kernel_rfl⟩
  comp m n := ⟨m.hom ≫ n.hom, by kernel_rfl⟩

instance homCategory (x y : Slice b) : Category.{w} (x ⟶ y) where
  Hom := Hom₂
  id m := ⟨𝟙 m.hom, by kernel_rfl⟩
  comp α β := ⟨α.hom ≫ β.hom, by kernel_rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom₂_ext {x y : Slice b} {m n : x ⟶ y} {α β : m ⟶ n} (h : α.hom = β.hom) : α = β :=
  Hom₂.ext h

instance bicategory : Bicategory.{w, v} (Slice b) where
  homCategory := homCategory
  whiskerLeft m _ _ α := ⟨m.hom ◁ α.hom, by kernel_rfl⟩
  whiskerRight α n := ⟨α.hom ▷ n.hom, by kernel_rfl⟩
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
  whisker_exchange := by intros; ext; exact whisker_exchange _ _
  pentagon := by intros; rfl
  triangle := by intros; rfl

/-- The strict slice over `b` is a 2-category. -/
instance twoCategory : TwoCategory.{w, v} (Slice b) where
  toBicategory := bicategory
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  leftUnitor_eqToIso := by intros; rfl
  rightUnitor_eqToIso := by intros; rfl
  associator_eqToIso := by intros; rfl

/-! The underlying cells of the operations of `Slice b` hold by `rfl`. They are rules, as the
matcher of rules does not unfold the instances of `Slice b` to find them. -/

section

variable {x y z : Slice b}

@[simp, rewrite_rule]
theorem id_hom' : (𝟙 x : x ⟶ x).hom = 𝟙 x.obj := rfl
@[simp, rewrite_rule]
theorem comp_hom (m : x ⟶ y) (n : y ⟶ z) : (m ≫ n).hom = m.hom ≫ n.hom := rfl

variable {m n o : x ⟶ y}

@[simp, rewrite_rule]
theorem id₂_hom : (𝟙 m : m ⟶ m).hom = 𝟙 m.hom := rfl
@[simp, rewrite_rule]
theorem comp₂_hom (α : m ⟶ n) (β : n ⟶ o) : (α ≫ β).hom = α.hom ≫ β.hom := rfl
@[simp, rewrite_rule]
theorem whiskerLeft_hom (k : z ⟶ x) (α : m ⟶ n) : (k ◁ α).hom = k.hom ◁ α.hom := rfl
@[simp, rewrite_rule]
theorem whiskerRight_hom (α : m ⟶ n) (k : y ⟶ z) : (α ▷ k).hom = α.hom ▷ k.hom := rfl

end

end Slice

end CategoryTheory.TwoCategory

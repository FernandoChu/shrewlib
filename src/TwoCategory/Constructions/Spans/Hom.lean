import TwoCategory.Basic

/-!
# Spans in a 2-category

A span from `a` to `b` in a 2-category `B` is an object `apex` with 1-cells `left : apex ⟶ a` and
`right : apex ⟶ b`. The spans from `a` to `b` form a 2-category (`Span.twoCategory`):

* a 1-cell `m : s ⟶ t` is a 1-cell `m.hom : s.apex ⟶ t.apex` of `B` with `m.hom ≫ t.left = s.left`
  and `m.hom ≫ t.right = s.right`;
* a 2-cell `α : m ⟶ n` is a 2-cell `α.hom : m.hom ⟶ n.hom` of `B` with `α.hom ▷ t.left = 𝟙 s.left`
  and `α.hom ▷ t.right = 𝟙 s.right`.

These equations are rules (the former also reassociated and whiskered), so the conditions on
2-cells are stated without transport, and composites and whiskerings of 1- and 2-cells of spans are
those of `B`, with their conditions by `rfl`.

If `B` has pullbacks, these are the hom-categories of the bicategory of spans `Spans B`
(`TwoCategory.Constructions.Spans.Basic`). Mathlib's spans `Span Wₗ Wᵣ a b` are not used: the
matcher of rules does not see through the instances of their category, so composites of their
morphisms do not compute.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B]

/-- A span from `a` to `b`: an object `apex` with 1-cells `left : apex ⟶ a`, `right : apex ⟶ b`. -/
structure Span (a b : B) where
  /-- The apex of the span. -/
  apex : B
  /-- The left leg. -/
  left : apex ⟶ a
  /-- The right leg. -/
  right : apex ⟶ b

namespace Span

variable {a b : B}

/-- A morphism of spans: a 1-cell between their apexes commuting with the legs. -/
@[ext]
structure Hom (s t : Span a b) where
  /-- The 1-cell between the apexes. -/
  hom : s.apex ⟶ t.apex
  hom_left : hom ≫ t.left = s.left
  hom_right : hom ≫ t.right = s.right

attribute [rewrite_rule] Hom.hom_left Hom.hom_right

namespace Hom

variable {s t : Span a b} (m : Hom s t)

@[rewrite_rule]
theorem hom_left_assoc {d : B} (k : a ⟶ d) : m.hom ≫ t.left ≫ k = s.left ≫ k :=
  congrArg (· ≫ k) m.hom_left

@[rewrite_rule]
theorem hom_right_assoc {d : B} (k : b ⟶ d) : m.hom ≫ t.right ≫ k = s.right ≫ k :=
  congrArg (· ≫ k) m.hom_right

@[rewrite_rule]
theorem hom_whiskerLeft_left {d : B} {k k' : a ⟶ d} (η : k ⟶ k') :
    m.hom ◁ t.left ◁ η = s.left ◁ η :=
  eq_of_heq (whiskerLeft_congr m.hom_left η)

@[rewrite_rule]
theorem hom_whiskerLeft_right {d : B} {k k' : b ⟶ d} (η : k ⟶ k') :
    m.hom ◁ t.right ◁ η = s.right ◁ η :=
  eq_of_heq (whiskerLeft_congr m.hom_right η)

@[rewrite_rule]
theorem whiskerRight_hom_left {x : B} {u u' : x ⟶ s.apex} (θ : u ⟶ u') :
    θ ▷ m.hom ▷ t.left = θ ▷ s.left :=
  eq_of_heq (whiskerRight_congr θ m.hom_left)

@[rewrite_rule]
theorem whiskerRight_hom_right {x : B} {u u' : x ⟶ s.apex} (θ : u ⟶ u') :
    θ ▷ m.hom ▷ t.right = θ ▷ s.right :=
  eq_of_heq (whiskerRight_congr θ m.hom_right)

end Hom

/-- A 2-cell between morphisms of spans: a 2-cell between the 1-cells of their apexes, which is
the identity after whiskering with the legs. -/
@[ext]
structure Hom₂ {s t : Span a b} (m n : Hom s t) where
  /-- The 2-cell between the 1-cells of the apexes. -/
  hom : m.hom ⟶ n.hom
  left : hom ▷ t.left = 𝟙 s.left
  right : hom ▷ t.right = 𝟙 s.right

attribute [rewrite_rule] Hom₂.left Hom₂.right

instance : CategoryStruct.{v} (Span a b) where
  Hom := Hom
  id s := ⟨𝟙 s.apex, rfl, rfl⟩
  comp m n := ⟨m.hom ≫ n.hom, rfl, rfl⟩

instance homCategory (s t : Span a b) : Category.{w} (s ⟶ t) where
  Hom := Hom₂
  id m := ⟨𝟙 m.hom, rfl, rfl⟩
  comp α β := ⟨α.hom ≫ β.hom, rfl, rfl⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[ext]
theorem hom₂_ext {s t : Span a b} {m n : s ⟶ t} {α β : m ⟶ n} (h : α.hom = β.hom) : α = β :=
  Hom₂.ext h

instance bicategory : Bicategory.{w, v} (Span a b) where
  homCategory := homCategory
  whiskerLeft m _ _ α := ⟨m.hom ◁ α.hom, rfl, rfl⟩
  whiskerRight α n := ⟨α.hom ▷ n.hom, rfl, rfl⟩
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

/-- The spans from `a` to `b` form a 2-category, whose 1-cells are the morphisms of spans and
whose 2-cells are the 2-cells between them. -/
instance twoCategory : TwoCategory.{w, v} (Span a b) where
  toBicategory := bicategory
  id_comp := by intros; rfl
  comp_id := by intros; rfl
  assoc := by intros; rfl
  leftUnitor_eqToIso := by intros; rfl
  rightUnitor_eqToIso := by intros; rfl
  associator_eqToIso := by intros; rfl

@[simp]
theorem id_hom (s : Span a b) : (𝟙 s : s ⟶ s).hom = 𝟙 s.apex :=
  rfl

@[simp]
theorem comp_hom {s t r : Span a b} (m : s ⟶ t) (n : t ⟶ r) : (m ≫ n).hom = m.hom ≫ n.hom :=
  rfl

end Span

end CategoryTheory.TwoCategory

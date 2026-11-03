import TwoCategory.Basic
import Rules.Pullback

/-!
# Pullbacks in a 2-category

A 2-category `B` has an underlying 1-category (`StrictBicategory.category`), so Mathlib's pullback
cones `PullbackCone f g` and limit cones `IsLimit t` apply to it. A (strict 2-)pullback is a limit
pullback cone with the 2-dimensional universal property as well (`IsPullback`): a 2-cell
`u ⟶ v` into its apex is the same as a pair of 2-cells `u ≫ t.fst ⟶ v ≫ t.fst` and
`u ≫ t.snd ⟶ v ≫ t.snd` that agree after whiskering with `f` and `g`.

The equation `t.fst ≫ f = t.snd ≫ g` of a pullback cone is a rule (`Rules.Pullback`), so this
agreement `θ₁ ▷ f = θ₂ ▷ g` is stated without transport. So are the equations of the 1-cells
induced by a limit cone, `lift h k w ≫ t.fst = h`. Here they get their whiskered forms
`t.fst ◁ f ◁ η = t.snd ◁ g ◁ η` and `θ ▷ t.fst ▷ f = θ ▷ t.snd ▷ g`, which make them confluent with
the rules of 2-categories.

Chosen pullbacks are in `TwoCategory.Limits.ChosenPullbacks`.
-/

open CategoryTheory Bicategory Limits

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] {a b c d : B} {f : a ⟶ c} {g : b ⟶ c}

/-! ## Whiskered forms of the rules for pullback cones -/

@[rewrite_rule]
theorem whiskerLeft_condition (t : PullbackCone f g) {k k' : c ⟶ d} (η : k ⟶ k') :
    t.fst ◁ f ◁ η = t.snd ◁ g ◁ η :=
  eq_of_heq (whiskerLeft_congr t.condition η)

@[rewrite_rule]
theorem whiskerRight_condition (t : PullbackCone f g) {x : B} {u v : x ⟶ t.pt} (θ : u ⟶ v) :
    θ ▷ t.fst ▷ f = θ ▷ t.snd ▷ g :=
  eq_of_heq (whiskerRight_congr θ t.condition)

section

variable {t : PullbackCone f g} (ht : IsLimit t) {x : B} (h : x ⟶ a) (k : x ⟶ b)
  (w : h ≫ f = k ≫ g)

@[rewrite_rule]
theorem lift_whiskerLeft_fst {k' k'' : a ⟶ d} (η : k' ⟶ k'') :
    PullbackCone.IsLimit.lift ht h k w ◁ t.fst ◁ η = h ◁ η :=
  eq_of_heq (whiskerLeft_congr (PullbackCone.IsLimit.lift_fst ht h k w) η)

@[rewrite_rule]
theorem lift_whiskerLeft_snd {k' k'' : b ⟶ d} (η : k' ⟶ k'') :
    PullbackCone.IsLimit.lift ht h k w ◁ t.snd ◁ η = k ◁ η :=
  eq_of_heq (whiskerLeft_congr (PullbackCone.IsLimit.lift_snd ht h k w) η)

@[rewrite_rule]
theorem whiskerRight_lift_fst {y : B} {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ PullbackCone.IsLimit.lift ht h k w ▷ t.fst = θ ▷ h :=
  eq_of_heq (whiskerRight_congr θ (PullbackCone.IsLimit.lift_fst ht h k w))

@[rewrite_rule]
theorem whiskerRight_lift_snd {y : B} {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ PullbackCone.IsLimit.lift ht h k w ▷ t.snd = θ ▷ k :=
  eq_of_heq (whiskerRight_congr θ (PullbackCone.IsLimit.lift_snd ht h k w))

end

/-! ## 2-pullbacks -/

/-- A (strict 2-)pullback: a limit pullback cone in the underlying category, whose 2-cells are
induced by pairs of 2-cells into the legs that agree after whiskering. -/
structure IsPullback (t : PullbackCone f g) extends IsLimit t where
  /-- The 2-cell induced by 2-cells into the legs. -/
  lift₂ {x : B} {u v : x ⟶ t.pt} (θ₁ : u ≫ t.fst ⟶ v ≫ t.fst) (θ₂ : u ≫ t.snd ⟶ v ≫ t.snd)
    (w : θ₁ ▷ f = θ₂ ▷ g) : u ⟶ v
  lift₂_fst {x : B} {u v : x ⟶ t.pt} (θ₁ : u ≫ t.fst ⟶ v ≫ t.fst) (θ₂ : u ≫ t.snd ⟶ v ≫ t.snd)
    (w : θ₁ ▷ f = θ₂ ▷ g) : lift₂ θ₁ θ₂ w ▷ t.fst = θ₁
  lift₂_snd {x : B} {u v : x ⟶ t.pt} (θ₁ : u ≫ t.fst ⟶ v ≫ t.fst) (θ₂ : u ≫ t.snd ⟶ v ≫ t.snd)
    (w : θ₁ ▷ f = θ₂ ▷ g) : lift₂ θ₁ θ₂ w ▷ t.snd = θ₂
  hom_ext₂ {x : B} {u v : x ⟶ t.pt} {θ θ' : u ⟶ v} (h₁ : θ ▷ t.fst = θ' ▷ t.fst)
    (h₂ : θ ▷ t.snd = θ' ▷ t.snd) : θ = θ'

namespace IsPullback

variable {t : PullbackCone f g}

/-- 1-cells into a pullback are determined by their composites with the legs. -/
theorem hom_ext (ht : IsPullback t) {x : B} {u v : x ⟶ t.pt} (h₁ : u ≫ t.fst = v ≫ t.fst)
    (h₂ : u ≫ t.snd = v ≫ t.snd) : u = v :=
  PullbackCone.IsLimit.hom_ext ht.toIsLimit h₁ h₂

end IsPullback

end CategoryTheory.TwoCategory

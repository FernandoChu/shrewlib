import Bicategory.Basic
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

`HasPullbacks B` adds to Mathlib's `Limits.HasPullbacks B` the 2-dimensional universal property of
the chosen pullbacks `pullback f g`.
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

variable (B) in
/-- A 2-category whose chosen pullbacks, in the underlying category, are 2-pullbacks. -/
class HasPullbacks [Limits.HasPullbacks B] where
  /-- The chosen pullbacks are 2-pullbacks. -/
  isPullback {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : IsPullback (pullback.cone f g)

/-! ## Chosen pullbacks -/

section

variable [Limits.HasPullbacks B]

@[rewrite_rule]
theorem pullback_whiskerLeft_condition (f : a ⟶ c) (g : b ⟶ c) {k k' : c ⟶ d} (η : k ⟶ k') :
    pullback.fst f g ◁ f ◁ η = pullback.snd f g ◁ g ◁ η :=
  eq_of_heq (whiskerLeft_congr pullback.condition η)

@[rewrite_rule]
theorem pullback_whiskerRight_condition (f : a ⟶ c) (g : b ⟶ c) {x : B} {u v : x ⟶ pullback f g}
    (θ : u ⟶ v) : θ ▷ pullback.fst f g ▷ f = θ ▷ pullback.snd f g ▷ g :=
  eq_of_heq (whiskerRight_congr θ pullback.condition)

section

variable {f : a ⟶ c} {g : b ⟶ c} {x : B} (h : x ⟶ a) (k : x ⟶ b) (w : h ≫ f = k ≫ g)

@[rewrite_rule]
theorem pullback.lift_whiskerLeft_fst {k' k'' : a ⟶ d} (η : k' ⟶ k'') :
    pullback.lift h k w ◁ pullback.fst f g ◁ η = h ◁ η :=
  eq_of_heq (whiskerLeft_congr (pullback.lift_fst h k w) η)

@[rewrite_rule]
theorem pullback.lift_whiskerLeft_snd {k' k'' : b ⟶ d} (η : k' ⟶ k'') :
    pullback.lift h k w ◁ pullback.snd f g ◁ η = k ◁ η :=
  eq_of_heq (whiskerLeft_congr (pullback.lift_snd h k w) η)

@[rewrite_rule]
theorem pullback.whiskerRight_lift_fst {y : B} {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ pullback.lift h k w ▷ pullback.fst f g = θ ▷ h :=
  eq_of_heq (whiskerRight_congr θ (pullback.lift_fst h k w))

@[rewrite_rule]
theorem pullback.whiskerRight_lift_snd {y : B} {u v : y ⟶ x} (θ : u ⟶ v) :
    θ ▷ pullback.lift h k w ▷ pullback.snd f g = θ ▷ k :=
  eq_of_heq (whiskerRight_congr θ (pullback.lift_snd h k w))

end

/-! For the pullback of `𝟙 a` and `g`, `pullback.fst ≫ 𝟙 a` rewrites both to `pullback.fst` and
to `pullback.snd ≫ g`, so `pullback.snd ≫ g ↦ pullback.fst` is a rule too, with its reassociated
and whiskered forms. -/

section

variable (g : b ⟶ a)

@[rewrite_rule]
theorem pullback.condition_id : pullback.snd (𝟙 a) g ≫ g = pullback.fst (𝟙 a) g :=
  pullback.condition.symm.trans (Category.comp_id _)

@[rewrite_rule]
theorem pullback.condition_id_assoc (k : a ⟶ d) :
    pullback.snd (𝟙 a) g ≫ g ≫ k = pullback.fst (𝟙 a) g ≫ k :=
  congrArg (· ≫ k) (pullback.condition_id g)

@[rewrite_rule]
theorem pullback.whiskerLeft_condition_id {k k' : a ⟶ d} (η : k ⟶ k') :
    pullback.snd (𝟙 a) g ◁ g ◁ η = pullback.fst (𝟙 a) g ◁ η :=
  eq_of_heq (whiskerLeft_congr (pullback.condition_id g) η)

@[rewrite_rule]
theorem pullback.whiskerRight_condition_id {x : B} {u v : x ⟶ pullback (𝟙 a) g} (θ : u ⟶ v) :
    θ ▷ pullback.snd (𝟙 a) g ▷ g = θ ▷ pullback.fst (𝟙 a) g :=
  eq_of_heq (whiskerRight_congr θ (pullback.condition_id g))

end

/-! The identity `𝟙 a` can be the one of the bicategory, as above, or the one of its underlying
category, as in Mathlib's identity spans `Span.id`. The two are definitionally equal but different
terms, so the rules are stated for both. -/

section

variable (g : b ⟶ a)

local notation "𝟙ᶜ" => @CategoryStruct.id B Category.toCategoryStruct

@[rewrite_rule]
theorem pullback.condition_id' : pullback.snd (𝟙ᶜ a) g ≫ g = pullback.fst (𝟙ᶜ a) g :=
  pullback.condition.symm.trans (Category.comp_id _)

@[rewrite_rule]
theorem pullback.condition_id'_assoc (k : a ⟶ d) :
    pullback.snd (𝟙ᶜ a) g ≫ g ≫ k = pullback.fst (𝟙ᶜ a) g ≫ k :=
  congrArg (· ≫ k) (pullback.condition_id' g)

@[rewrite_rule]
theorem pullback.whiskerLeft_condition_id' {k k' : a ⟶ d} (η : k ⟶ k') :
    pullback.snd (𝟙ᶜ a) g ◁ g ◁ η = pullback.fst (𝟙ᶜ a) g ◁ η :=
  eq_of_heq (whiskerLeft_congr (pullback.condition_id' g) η)

@[rewrite_rule]
theorem pullback.whiskerRight_condition_id' {x : B} {u v : x ⟶ pullback (𝟙ᶜ a) g}
    (θ : u ⟶ v) : θ ▷ pullback.snd (𝟙ᶜ a) g ▷ g = θ ▷ pullback.fst (𝟙ᶜ a) g :=
  eq_of_heq (whiskerRight_congr θ (pullback.condition_id' g))

end

open Lean Meta Elab Tactic in
/-- Applies `pullback.hom_ext` to an equation of 1-cells into a chosen pullback `pullback f g`,
reading `f` and `g` off the goal: unifying them with those in the statement of `hom_ext` is slow
when the codomain is the result of a computation. -/
elab "pullback_ext" : tactic => withMainContext do
  let some (ty, _, _) := (← whnfR (← getMainTarget)).eq? |
    throwError "pullback_ext: the goal is not an equation"
  let some P ← whnfUntil ty.appArg! ``Limits.limit |
    throwError "pullback_ext: not a 1-cell into a chosen pullback"
  let some F := P.getAppArgs[4]? |
    throwError "pullback_ext: not a 1-cell into a chosen pullback"
  unless F.isAppOf ``Limits.cospan do
    throwError "pullback_ext: not a 1-cell into a chosen pullback"
  let f ← Term.exprToSyntax (F.getArg! (F.getAppNumArgs - 2))
  let g ← Term.exprToSyntax (F.getArg! (F.getAppNumArgs - 1))
  evalTactic (← `(tactic| refine pullback.hom_ext (f := $f) (g := $g) ?_ ?_))

end

end CategoryTheory.TwoCategory

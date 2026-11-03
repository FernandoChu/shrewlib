import TwoCategory.Limits.Pullback
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.ChosenPullback

/-!
# Chosen pullbacks in a 2-category

`ChosenPullbacks B` chooses a pullback (Mathlib's `ChosenPullback`) of every cospan in the
underlying category of a 2-category `B`, with apex `pullback f g`, projections `pullback.fst f g`
and `pullback.snd f g`, and induced 1-cells `pullback.lift h k w`. Unlike Mathlib's
`Limits.HasPullbacks`, which only asserts that pullbacks exist, this is data, so constructions
with the chosen pullbacks, such as the bicategory of spans, are computable. Mathlib's
`ChosenPullbacks` is data too, but it is unsuited to rules: its projections are `abbrev`s for
components of an adjunction `Over.map g ⊣ pullback g`, so they unfold and rules stated on them
stop firing, and its equations are the triangle laws of that adjunction.

The equation of the pullback square and those of the induced 1-cells are rules, also reassociated
and whiskered, so 2-cells over `pullback.fst f g ≫ f = pullback.snd f g ≫ g` need no transport.
`pullback_ext` applies extensionality. `HasPullbacks B` adds the 2-dimensional universal property
of the chosen pullbacks (`TwoCategory.Limits.Pullback`).

These rules are in their own file, imported only where chosen pullbacks are used: every rule
headed by `≫` or a whiskering is tried on every composite or whiskering.
-/

open CategoryTheory Bicategory Limits

universe w v u

namespace CategoryTheory.TwoCategory

variable {B : Type u} [TwoCategory.{w, v} B] {a b c d : B} {f : a ⟶ c} {g : b ⟶ c}

variable (B) in
/-- A 2-category with a chosen pullback (Mathlib's `ChosenPullback`) of every cospan in its
underlying category. -/
class ChosenPullbacks where
  /-- The chosen pullback of `f` and `g`. -/
  chosenPullback {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : ChosenPullback f g

open ChosenPullbacks

section

variable [ChosenPullbacks B]

/-- The apex of the chosen pullback of `f` and `g`. -/
def pullback (f : a ⟶ c) (g : b ⟶ c) : B :=
  (chosenPullback f g).pullback

/-- The first projection of the chosen pullback. -/
def pullback.fst (f : a ⟶ c) (g : b ⟶ c) : pullback f g ⟶ a :=
  (chosenPullback f g).p₁

/-- The second projection of the chosen pullback. -/
def pullback.snd (f : a ⟶ c) (g : b ⟶ c) : pullback f g ⟶ b :=
  (chosenPullback f g).p₂

@[rewrite_rule]
theorem pullback.condition (f : a ⟶ c) (g : b ⟶ c) :
    pullback.fst f g ≫ f = pullback.snd f g ≫ g :=
  (chosenPullback f g).condition

@[rewrite_rule]
theorem pullback.condition_assoc (f : a ⟶ c) (g : b ⟶ c) (k : c ⟶ d) :
    pullback.fst f g ≫ f ≫ k = pullback.snd f g ≫ g ≫ k :=
  congrArg (· ≫ k) (pullback.condition f g)

/-- The chosen pullback cone of `f` and `g`. -/
abbrev pullback.cone (f : a ⟶ c) (g : b ⟶ c) : PullbackCone f g :=
  PullbackCone.mk (pullback.fst f g) (pullback.snd f g) (pullback.condition f g)

/-- The chosen pullback cone is a limit cone. -/
def pullback.isLimit (f : a ⟶ c) (g : b ⟶ c) : IsLimit (pullback.cone f g) :=
  (chosenPullback f g).isLimit

/-- The 1-cell into the chosen pullback induced by a commutative square. -/
def pullback.lift {x : B} (h : x ⟶ a) (k : x ⟶ b) (w : h ≫ f = k ≫ g) : x ⟶ pullback f g :=
  PullbackCone.IsLimit.lift (pullback.isLimit f g) h k w

section

variable {x : B} (h : x ⟶ a) (k : x ⟶ b) (w : h ≫ f = k ≫ g)

@[rewrite_rule]
theorem pullback.lift_fst : pullback.lift h k w ≫ pullback.fst f g = h :=
  PullbackCone.IsLimit.lift_fst _ h k w

@[rewrite_rule]
theorem pullback.lift_snd : pullback.lift h k w ≫ pullback.snd f g = k :=
  PullbackCone.IsLimit.lift_snd _ h k w

@[rewrite_rule]
theorem pullback.lift_fst_assoc (k' : a ⟶ d) :
    pullback.lift h k w ≫ pullback.fst f g ≫ k' = h ≫ k' :=
  congrArg (· ≫ k') (pullback.lift_fst h k w)

@[rewrite_rule]
theorem pullback.lift_snd_assoc (k' : b ⟶ d) :
    pullback.lift h k w ≫ pullback.snd f g ≫ k' = k ≫ k' :=
  congrArg (· ≫ k') (pullback.lift_snd h k w)

end

/-- 1-cells into the chosen pullback are determined by their composites with the projections. -/
theorem pullback.hom_ext {x : B} {u v : x ⟶ pullback f g}
    (h₁ : u ≫ pullback.fst f g = v ≫ pullback.fst f g)
    (h₂ : u ≫ pullback.snd f g = v ≫ pullback.snd f g) : u = v :=
  (chosenPullback f g).hom_ext h₁ h₂

end

variable (B) in
/-- A 2-category whose chosen pullbacks, in the underlying category, are 2-pullbacks. -/
class HasPullbacks [ChosenPullbacks B] where
  /-- The chosen pullbacks are 2-pullbacks. -/
  isPullback {a b c : B} (f : a ⟶ c) (g : b ⟶ c) : IsPullback (pullback.cone f g)

section

variable [ChosenPullbacks B]

/-! The rules for the chosen pullbacks get their whiskered forms. -/

@[rewrite_rule]
theorem pullback_whiskerLeft_condition (f : a ⟶ c) (g : b ⟶ c) {k k' : c ⟶ d} (η : k ⟶ k') :
    pullback.fst f g ◁ f ◁ η = pullback.snd f g ◁ g ◁ η :=
  eq_of_heq (whiskerLeft_congr (pullback.condition f g) η)

@[rewrite_rule]
theorem pullback_whiskerRight_condition (f : a ⟶ c) (g : b ⟶ c) {x : B} {u v : x ⟶ pullback f g}
    (θ : u ⟶ v) : θ ▷ pullback.fst f g ▷ f = θ ▷ pullback.snd f g ▷ g :=
  eq_of_heq (whiskerRight_congr θ (pullback.condition f g))

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
  (pullback.condition _ g).symm.trans (Category.comp_id _)

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
  (pullback.condition _ g).symm.trans (Category.comp_id _)

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
  let some P ← whnfUntil ty.appArg! ``TwoCategory.pullback |
    throwError "pullback_ext: not a 1-cell into a chosen pullback"
  let f ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 2))
  let g ← Term.exprToSyntax (P.getArg! (P.getAppNumArgs - 1))
  evalTactic (← `(tactic| refine pullback.hom_ext (f := $f) (g := $g) ?_ ?_))

end

end CategoryTheory.TwoCategory

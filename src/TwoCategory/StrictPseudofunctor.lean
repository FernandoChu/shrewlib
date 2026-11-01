import TwoCategory.Basic
import Rules.StrictPseudofunctor

/-!
# Strict pseudofunctors between 2-categories

The laws of Mathlib's strict pseudofunctors are rules (`Rules.StrictPseudofunctor`). Between
2-categories, they get their whiskered forms `F.map₂ (f ◁ η) ↦ F.map f ◁ F.map₂ η` and
`F.map₂ (η ▷ f) ↦ F.map₂ η ▷ F.map f`, which are rules too.
-/

open CategoryTheory Bicategory

universe w v u

namespace CategoryTheory

namespace StrictPseudofunctor

variable {C : Type u} [TwoCategory.{w, v} C] (F : StrictPseudofunctor C C)

@[rewrite_rule]
theorem map₂_whiskerLeft' {a b c : C} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    F.map₂ (f ◁ η) = F.map f ◁ F.map₂ η :=
  (F.map₂_whisker_left f η).trans (by kernel_rfl)

@[rewrite_rule]
theorem map₂_whiskerRight' {a b c : C} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    F.map₂ (η ▷ h) = F.map₂ η ▷ F.map h :=
  (F.map₂_whisker_right η h).trans (by kernel_rfl)

end StrictPseudofunctor

end CategoryTheory

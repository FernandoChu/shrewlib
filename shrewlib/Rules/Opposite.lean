import Rules.Functor
import Mathlib.CategoryTheory.Opposites

/-!
# The functor laws on opposites as rewrite rules

For a functor `F : Aᵒᵖ ⥤ B`, `F.map (𝟙 a).op ↦ 𝟙 (F.obj (op a))` and
`F.map (f ≫ g).op ↦ F.map g.op ≫ F.map f.op`: the rules of `Rules.Functor` do not see `(𝟙 a).op`
and `(f ≫ g).op` as an identity and a composite. Mathlib's `op_id` and `op_comp` cannot be rules
instead: `𝟙 (op a)` unfolds to `(𝟙 a).op`, so `op_id` would loop.

They are tried on every application of `Functor.map`, where matching the source category against
`Aᵒᵖ` is expensive, so they are imported only where functors out of opposites are used.
-/

open CategoryTheory Opposite

namespace CategoryTheory.Functor

variable {A : Type*} [Category A] {B : Type*} [Category B] (F : Aᵒᵖ ⥤ B)

@[rewrite_rule]
theorem map_op_id (a : A) : F.map (𝟙 a).op = 𝟙 (F.obj (op a)) :=
  F.map_id (op a)

@[rewrite_rule]
theorem map_op_comp {a a' a'' : A} (f : a ⟶ a') (g : a' ⟶ a'') :
    F.map (f ≫ g).op = F.map g.op ≫ F.map f.op :=
  F.map_comp g.op f.op

end CategoryTheory.Functor

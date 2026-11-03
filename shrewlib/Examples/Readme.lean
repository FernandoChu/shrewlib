import Examples.FunctorId

/-!
# Examples

Small examples of the rewrite rules.

* `FunctorId`: `F.map (𝟙 a) x = x` by `rfl` for any functor `F : A ⥤ Type`, after making Mathlib's
  `Functor.map_id` a rule.
-/

universe w v u

open CategoryTheory

/-! ## Main results -/

recall map_id_apply' {A : Type u} [Category.{v} A] (F : A ⥤ Type w) (a : A) (x : F.obj a) :
    ConcreteCategory.hom (F.map (𝟙 a)) x = x

import Mathlib.CategoryTheory.Types.Basic

/-!
Turns Mathlib's functor law `F.map (𝟙 X) = 𝟙 (F.obj X)` into a definitional reduction rule, so that
for a functor into the category of types, `F.map (𝟙 a) x = x` holds by `rfl`.
Requires the `rewrite-rules` fork of Lean.
-/

open CategoryTheory

universe v u w

-- Before the rule: `F.map (𝟙 a)` is stuck, since `F` is a variable.
/--
error: Type mismatch
  Eq.refl x
has type
  x = x
but is expected to have type
  (ConcreteCategory.hom (F.map (𝟙 a))) x = x
-/
#guard_msgs in
example {A : Type u} [Category.{v} A] (F : A ⥤ Type w) (a : A) (x : F.obj a) :
    F.map (𝟙 a) x = x := Eq.refl x

attribute [rewrite_rule] Functor.map_id

-- After the rule: `F.map (𝟙 a) ↦ 𝟙 (F.obj a)`, which computes to the identity function in `Type w`.
theorem map_id_apply' {A : Type u} [Category.{v} A] (F : A ⥤ Type w) (a : A) (x : F.obj a) :
    F.map (𝟙 a) x = x := rfl

-- The axioms come from Mathlib's `types` instance and `FunLike` coercion in the statement, as for
-- Mathlib's own propositional version.
/-- info: 'map_id_apply'' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms map_id_apply'

/-- info: 'CategoryTheory.Functor.map_id_apply' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Functor.map_id_apply

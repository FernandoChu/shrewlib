import CategoryTheory.Opposite.OpFunctor

/-!
# Opposite categories

In this folder we define the opposite of a category that is involutive on the nose, unlike Mathlib's
`Cᵒᵖ`, whose double opposite is the type `Opposite (Opposite C)`.

* `OpFunctor`: the opposite category structure `opCategory'` on the objects of a category, and the
  opposite functor `opFunctor' : Cat ⥤ Cat`, with `opFunctor' ⋙ opFunctor' = 𝟭 Cat` by `rfl`. It
  is Mathlib's `Cat.opFunctor` up to a natural isomorphism. The file imports no rewrite rules.
-/

universe v u

open CategoryTheory

/-! ## Main results -/

/-- The opposite functor is involutive on the nose, and is Mathlib's `Cat.opFunctor` up to
isomorphism. -/
recall CategoryTheory.opFunctor'_comp_opFunctor' : opFunctor'.{v, u} ⋙ opFunctor' = 𝟭 _

recall CategoryTheory.opFunctor'Iso : opFunctor'.{v, u} ≅ Cat.opFunctor

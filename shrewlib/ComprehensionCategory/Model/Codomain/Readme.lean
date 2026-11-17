import ComprehensionCategory.Model.Codomain.Basic

/-!
# The codomain model

A category `C` with chosen pullbacks is a full comprehension category over itself, by the
codomain fibration `cod C` and the identity: types in context `Γ` are morphisms into `Γ`, and
substitution is pullback.

* `Basic`: the comprehension structure on `cod C`, and the comprehension functor of any
  comprehension category as a pseudo map to it.
-/

universe v u v₂ u₂

open CategoryTheory Limits Displayed

/-! ## Main results -/

/-- With chosen pullbacks, the codomain fibration is a full comprehension category. -/
recall ComprehensionCategory.CodomainModel.fullComprehension {C : Type u} [Category.{v} C]
    [ChosenPullbacks C] : FullComprehension (cod C)

/-- The comprehension functor of a comprehension category over `C` is a pseudo map to `cod C`. -/
recall ComprehensionCategory.CodomainModel.comprMap {C : Type u} [Category.{v} C]
    [ChosenPullbacks C] (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] :
    PseudoComprehensionMap (𝟭 C) D (cod C)

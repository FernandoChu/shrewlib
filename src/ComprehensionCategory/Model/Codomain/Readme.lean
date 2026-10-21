import ComprehensionCategory.Model.Codomain.Basic

/-!
# The codomain model

A category `C` with chosen pullbacks is a full comprehension category over itself, by the
codomain fibration `cod C` and the identity: types in context `Γ` are morphisms into `Γ`, and
substitution is pullback.

* `Basic`: the comprehension structure on `cod C`.
-/

universe v u

open CategoryTheory Limits Displayed

/-! ## Main results -/

/-- With chosen pullbacks, the codomain fibration is a full comprehension category. -/
recall ComprehensionCategory.CodomainModel.fullComprehension {C : Type u} [Category.{v} C]
    [ChosenPullbacks C] : FullComprehension (cod C)

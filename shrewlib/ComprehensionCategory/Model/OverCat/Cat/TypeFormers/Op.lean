import ComprehensionCategory.Model.OverCat.Cat.Basic
import CategoryTheory.Opposite.OpFunctor

/-!
# Opposite types in the category model

The opposite of a type `A : Γ ⥤ Cat` is the pointwise opposite, `Aᵒᵖ = A ⋙ opFunctor'`, where
`opFunctor' : Cat ⥤ Cat` is the strictly involutive opposite functor of `OpFunctor`. It is
involutive and stable under substitution by `rfl`: `(A ⋙ opFunctor') ⋙ opFunctor'` is `A`, since
`opFunctor' ⋙ opFunctor'` is the identity on the nose (`op_op`), and the substitution
`σ ⋙ (A ⋙ opFunctor')` is `(σ ⋙ A) ⋙ opFunctor'` (`pull_op`).

The notation `Aᵒᵖ` for `CatModel.op A` is scoped in `ComprehensionCategory.CatModel`. It overloads
Mathlib's `Cᵒᵖ` for opposite categories, and the opposite types of the discrete model, which are
told apart by the type of `A`.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

open scoped Displayed

/-- The opposite type of `A : Γ ⥤ Cat`, pointwise: `A ⋙ opFunctor'`. -/
def op {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) : ICatLax.{u, u}.Ty Γ :=
  A ⋙ opFunctor'

/-- `Aᵒᵖ` is the opposite type `CatModel.op A`. -/
scoped notation:max A:max "ᵒᵖ" => CatModel.op A

/-- Displays `CatModel.op A` as `Aᵒᵖ`. -/
@[scoped app_unexpander CatModel.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($Aᵒᵖ)
  | _ => throw ()

/-- **The opposite is involutive**, by `rfl`. -/
theorem op_op {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) : (Aᵒᵖ)ᵒᵖ = A :=
  rfl

/-- **The opposite is stable under substitution**, by `rfl`. -/
theorem pull_op {Δ Γ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatLax.{u, u}.Ty Γ) :
    (Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ :=
  rfl

end ComprehensionCategory.CatModel

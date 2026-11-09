import ComprehensionCategory.Model.OverCat.CatOp.Basic
import CategoryTheory.Opposite.OpFunctor

/-!
# Opposite types in the contravariant category model

The opposite of a type `A : Γᵒᵖ ⥤ Cat` is the pointwise opposite, `Aᵒᵖ = A ⋙ opFunctor'`, where
`opFunctor' : Cat ⥤ Cat` is the strictly involutive opposite functor of `OpFunctor`. As in the
category model (`OverCat/Cat/TypeFormers/Op.lean`), it is involutive and stable under substitution
by `rfl`.

The notation `Aᵒᵖ` for `CatOpModel.op A` is scoped in `ComprehensionCategory.CatOpModel`.
-/

universe u

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Displayed Displayed.Fibration.Straightening

open scoped Displayed

/-- The opposite type of `A : Γᵒᵖ ⥤ Cat`, pointwise: `A ⋙ opFunctor'`. -/
def op {Γ : Cat.{u, u}} (A : ICatOpLax.{u, u}.Ty Γ) : ICatOpLax.{u, u}.Ty Γ :=
  A ⋙ opFunctor'

/-- `Aᵒᵖ` is the opposite type `CatOpModel.op A`. -/
scoped notation:max A:max "ᵒᵖ" => CatOpModel.op A

/-- Displays `CatOpModel.op A` as `Aᵒᵖ`. -/
@[scoped app_unexpander CatOpModel.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($Aᵒᵖ)
  | _ => throw ()

/-- **The opposite is involutive**, by `rfl`. -/
theorem op_op {Γ : Cat.{u, u}} (A : ICatOpLax.{u, u}.Ty Γ) : (Aᵒᵖ)ᵒᵖ = A :=
  rfl

/-- **The opposite is stable under substitution**, by `rfl`. -/
theorem pull_op {Δ Γ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : ICatOpLax.{u, u}.Ty Γ) :
    (Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ :=
  rfl

end ComprehensionCategory.CatOpModel

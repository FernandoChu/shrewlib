import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Op
import ComprehensionCategory.Model.OverCat.Discrete.Basic
import ComprehensionCategory.Model.OverCat.Discrete.OpFunctor

/-!
# Opposite types in the discrete model

The opposite types of the discrete model are those of the category model, the pointwise opposites
`A ⋙ opFunctor'`, which take values in discrete categories since the opposite of a discrete
category is (`isDiscrete_opFunctor'_obj`). They are involutive and stable under substitution by
`rfl`, as in the category model.

The notation `Aᵒᵖ` for `DiscreteModel.op A` is scoped in `ComprehensionCategory.DiscreteModel`. It
overloads Mathlib's `Cᵒᵖ` and the opposite types of the category model, which are told apart by
the type of `A`.
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete.Straightening

open scoped Displayed

/-- The opposite type of `A`: that of the category model. -/
def op {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) : IDisc.{u, u}.Ty Γ where
  toFunctor := CatModel.op A.toFunctor
  isDiscrete γ := @isDiscrete_opFunctor'_obj (A.toFunctor.obj γ) (A.isDiscrete γ)

/-- `Aᵒᵖ` is the opposite type `DiscreteModel.op A`. -/
scoped notation:max A:max "ᵒᵖ" => DiscreteModel.op A

/-- Displays `DiscreteModel.op A` as `Aᵒᵖ`. -/
@[scoped app_unexpander DiscreteModel.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $A) => `($Aᵒᵖ)
  | _ => throw ()

/-- **The opposite is involutive**, by `rfl`. -/
theorem op_op {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) : (Aᵒᵖ)ᵒᵖ = A :=
  rfl

/-- **The opposite is stable under substitution**, by `rfl`. -/
theorem pull_op {Δ Γ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : IDisc.{u, u}.Ty Γ) : (Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ :=
  rfl

end ComprehensionCategory.DiscreteModel

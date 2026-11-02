import ComprehensionCategory.Model.Cat.Basic
import ComprehensionCategory.Model.Cat.OpFunctor
import ComprehensionCategory.TypeFormers.Op

/-!
# Opposite types in the category model

The opposite of a type `A : Γ ⥤ Cat` is the pointwise opposite, `A ⋙ opFunctor'`, where
`opFunctor' : Cat ⥤ Cat` is the strictly involutive opposite functor of
`ComprehensionCategory/Model/Cat/OpFunctor`. Both rules hold by `rfl`:
`(A ⋙ opFunctor') ⋙ opFunctor'` is `A`, since `opFunctor' ⋙ opFunctor'` is the identity on the
nose, and the substitution `σ ⋙ (A ⋙ opFunctor')` is `(σ ⋙ A) ⋙ opFunctor'`.
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening

/-- The opposite type of `A : Γ ⥤ Cat`, pointwise: `A ⋙ opFunctor'`. -/
def op {Γ : Cat.{u, u}} (A : Γ ⥤ Cat.{u, u}) : Γ ⥤ Cat.{u, u} :=
  A ⋙ opFunctor'

/-- **The category model has opposite types**, involutive and stable under substitution by `rfl`. -/
instance hasOp : HasOp ICat.{u} where
  op A := CatModel.op A
  op_op _ := rfl
  pull_op _ _ := rfl

end ComprehensionCategory.CatModel

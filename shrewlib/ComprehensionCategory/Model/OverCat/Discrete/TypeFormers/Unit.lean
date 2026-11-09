import ComprehensionCategory.Model.OverCat.Discrete.Basic
import ComprehensionCategory.Model.OverCat.Cat.TypeFormers.Unit

/-!
# Unit types in the discrete model

The unit types of the discrete model are those of the category model, the constant types at the
terminal category `discrete' PUnit`, which is discrete. The star is that of the category model,
and η holds by `rfl`, as there.

So forgetting the discreteness preserves unit types strictly, by `rfl`
(`OverCat/Maps/DiscreteToCat`).
-/

universe u

namespace ComprehensionCategory.DiscreteModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete
  Displayed.Discrete.Straightening

open scoped Displayed

/-- The unit type of the discrete model: that of the category model. -/
def unit (Γ : Cat.{u, u}) : IDisc.{u, u}.Ty Γ where
  toFunctor := CatModel.unit Γ
  isDiscrete _ := isDiscrete_discrete' PUnit.{u + 1}

/-- The unit types of the discrete model, closed by `rfl`. -/
instance preUnit : PreUnit IDisc.{u, u, u, u} where
  unit Γ := DiscreteModel.unit Γ
  pull_unit _ := rfl

/-- **The discrete model has unit types**, with the stars of the category model. -/
instance hasUnit : HasUnit IDisc.{u, u, u, u} where
  star Γ := ⟨(CatModel.star Γ).sec, rfl⟩
  proj_star _ := rfl

end ComprehensionCategory.DiscreteModel

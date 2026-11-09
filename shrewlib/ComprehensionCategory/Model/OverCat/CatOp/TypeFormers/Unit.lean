import ComprehensionCategory.Model.OverCat.CatOp.Term
import ComprehensionCategory.TypeFormers.Unit
import Displayed.Discrete.DiscreteCat

/-!
# Unit types in the contravariant category model

As in the category model (`OverCat/Cat/TypeFormers/Unit`), the unit type in context `Γ` is the
constant type at the terminal category `discrete' PUnit`, closed by `rfl`. Its star is the constant
section `γ ↦ (γ, ⟨⟩)`, and η holds by `rfl`, by eta for `PUnit`, `ULift` and `PLift` and proof
irrelevance.

This is the dual of `OverCat/Cat/TypeFormers/Unit.lean`.
-/

universe u

namespace ComprehensionCategory.CatOpModel

open CategoryTheory Displayed Displayed.Fibration.Straightening Displayed.Discrete

open scoped Displayed

/-- The unit type in context `Γ`: the constant type at the terminal category `discrete' PUnit`. -/
def unit (Γ : Cat.{u, u}) : ICatOpLax.{u, u}.Ty Γ :=
  constTy Γ (discrete' PUnit.{u + 1})

/-- The unit types of the contravariant category model, closed by `rfl`. -/
instance preUnit : PreUnit ICatOpLax.{u, u, u, u} where
  unit Γ := CatOpModel.unit Γ
  pull_unit _ := rfl

/-- The star `γ ↦ (γ, ⟨⟩)`, the unique term of the unit type. -/
def star (Γ : Cat.{u, u}) : Tm(Γ, CatOpModel.unit Γ) :=
  tmMk (A := CatOpModel.unit Γ) (fun _ => PUnit.unit) (fun _ => ⟨⟨rfl⟩⟩) (fun _ => rfl)
    fun _ _ => rfl

/-- **The contravariant category model has unit types**, whose η holds by `rfl`. -/
instance hasUnit : HasUnit ICatOpLax.{u, u, u, u} where
  star Γ := CatOpModel.star Γ
  proj_star _ := rfl

end ComprehensionCategory.CatOpModel

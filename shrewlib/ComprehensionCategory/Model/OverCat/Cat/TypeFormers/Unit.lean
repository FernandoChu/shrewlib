import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.TypeFormers.Unit
import Displayed.Discrete.DiscreteCat

/-!
# Unit types in the category model

The unit type in context `Γ` is the constant type at the terminal category `discrete' PUnit`, the
discrete category on one object (`Displayed/Discrete/DiscreteCat`). It is closed by `rfl`, since
the constant types are. Its star is the constant section `γ ↦ (γ, ⟨⟩)`, and η,
`𝐩 (unit Γ) ≫ star.sec = 𝟙`, holds by `rfl`: an object of `Γ ⋉ unit Γ` is a pair `(γ, x)` with
`x : PUnit`, which is `(γ, ⟨⟩)` by eta for `PUnit`, and the second component of a morphism is a
proof of an equality wrapped in `ULift` and `PLift`, unique by eta and proof irrelevance.

The terminal category is `discrete' PUnit` rather than Mathlib's `Discrete PUnit` so that it is a
type of the discrete model, whose unit types are these (`OverCat/Discrete/TypeFormers/Unit`), and
its own opposite, by `propext` (`opFunctor'_obj_discrete'`).
-/

universe u

namespace ComprehensionCategory.CatModel

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete

open scoped Displayed

/-- The unit type in context `Γ`: the constant type at the terminal category `discrete' PUnit`. -/
def unit (Γ : Cat.{u, u}) : ICatLax.{u, u}.Ty Γ :=
  constTy Γ (discrete' PUnit.{u + 1})

/-- The unit types of the category model, closed by `rfl`. -/
instance preUnit : PreUnit ICatLax.{u, u, u, u} where
  unit Γ := CatModel.unit Γ
  pull_unit _ := rfl

/-- The star `γ ↦ (γ, ⟨⟩)`, the unique term of the unit type. -/
def star (Γ : Cat.{u, u}) : Tm(Γ, CatModel.unit Γ) :=
  tmMk (A := CatModel.unit Γ) (fun _ => PUnit.unit) (fun _ => ⟨⟨rfl⟩⟩) (fun _ => rfl)
    fun _ _ => rfl

/-- **The category model has unit types**, whose η holds by `rfl`. -/
instance hasUnit : HasUnit ICatLax.{u, u, u, u} where
  star Γ := CatModel.star Γ
  proj_star _ := rfl

end ComprehensionCategory.CatModel

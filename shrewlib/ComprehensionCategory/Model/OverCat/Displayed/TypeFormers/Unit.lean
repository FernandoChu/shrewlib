import ComprehensionCategory.Model.OverCat.Displayed.Term
import ComprehensionCategory.TypeFormers.Unit

/-!
# Unit types in the displayed category model

The unit type in context `Γ` is the straightening of the terminal displayed category over `Γ`,
`unitDisp Γ`, with one object over each object of `Γ` and one morphism over each morphism. It is
closed by `rfl`: substitution is the straightening of the reindexing (`straightenObj_pull`), and
the reindexing of `unitDisp Γ` along `σ` is `unitDisp Δ`, by eta for `PUnit`. The context extension
`Γ ▹ unit Γ` is the total category of `unitDisp Γ`, by `rfl`. Its star is the section
`γ ↦ (γ, ⟨⟩)` (`tmMk`), and η, `𝐩 (unit Γ) ≫ star.sec = 𝟙`, holds by `rfl`, by eta for `PUnit`.

The morphisms of `unitDisp Γ` from `x` to `y` are the proofs of `x = y`, wrapped in `ULift` and
`PLift`, as in the discrete category `discrete' PUnit`: so `unitDisp Γ` is, by `rfl`, the
unstraightening of the constant functor at `discrete' PUnit`, both covariant and contravariant, the
unit types of the other models, and the maps from them preserve unit types by `rfl`
(`OverCat/Maps/CatToDisplayed`, `OverCat/Maps/CatOpToDisplayed`). With `PUnit` as morphisms,
they would be different types.
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

open scoped Displayed

/-- The terminal displayed category over `Γ`: one object over each object, and one morphism over
each morphism, a proof of `x = y`. Its laws hold by `rfl`. -/
def unitDisp (Γ : Cat.{u, u}) : Displayed.{u, u} Γ where
  Ob _ := PUnit
  Hom _ x y := ULift.{u} (PLift (x = y))
  id _ := ⟨⟨rfl⟩⟩
  comp φ ψ := ⟨⟨φ.down.down.trans ψ.down.down⟩⟩

/-- The unit type in context `Γ`: the straightening of the terminal displayed category. -/
def unit (Γ : Cat.{u, u}) : IProf.{u, u, u}.Ty Γ :=
  straightenObj (unitDisp Γ)

/-- The unit types of the displayed category model, closed by `rfl`. -/
instance preUnit : PreUnit IProf.{u, u, u} where
  unit Γ := DisplayedModel.unit Γ
  pull_unit _ := rfl

/-- The star `γ ↦ (γ, ⟨⟩)`, the unique term of the unit type. -/
def star (Γ : Cat.{u, u}) : Tm(Γ, DisplayedModel.unit Γ) :=
  tmMk (D := unitDisp Γ) (fun _ => PUnit.unit) (fun _ => ⟨⟨rfl⟩⟩) (fun _ => rfl)
    fun _ _ => rfl

/-- **The displayed category model has unit types**, whose η holds by `rfl`. -/
instance hasUnit : HasUnit IProf.{u, u, u} where
  star Γ := DisplayedModel.star Γ
  proj_star _ := rfl

end ComprehensionCategory.DisplayedModel

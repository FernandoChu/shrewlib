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
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

open scoped Displayed

/-- The terminal displayed category over `Γ`: one object over each object, and one morphism over
each morphism. Its laws hold by `rfl`. -/
def unitDisp (Γ : Cat.{u, u}) : Displayed.{u, u} Γ where
  Ob _ := PUnit
  Hom _ _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- The unit type in context `Γ`: the straightening of the terminal displayed category. -/
def unit (Γ : Cat.{u, u}) : LaxNormalCat.{u, u, u}.Ty Γ :=
  straightenObj (unitDisp Γ)

/-- The unit types of the displayed category model, closed by `rfl`. -/
instance preUnit : PreUnit LaxNormalCat.{u, u, u} where
  unit Γ := DisplayedModel.unit Γ
  pull_unit _ := rfl

/-- The star `γ ↦ (γ, ⟨⟩)`, the unique term of the unit type. -/
def star (Γ : Cat.{u, u}) : Tm(Γ, DisplayedModel.unit Γ) :=
  tmMk (D := unitDisp Γ) (fun _ => PUnit.unit) (fun _ => PUnit.unit) (fun _ => rfl)
    fun _ _ => rfl

/-- **The displayed category model has unit types**, whose η holds by `rfl`. -/
instance hasUnit : HasUnit LaxNormalCat.{u, u, u} where
  star Γ := DisplayedModel.star Γ
  proj_star _ := rfl

end ComprehensionCategory.DisplayedModel

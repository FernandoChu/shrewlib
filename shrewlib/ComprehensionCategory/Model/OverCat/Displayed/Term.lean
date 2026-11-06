import ComprehensionCategory.Model.OverCat.Displayed.Basic
import ComprehensionCategory.Term

/-!
# Terms in the displayed category model

A term `t : Tm(Γ, F)` of a type `F` of the displayed category model is a section of the projection
of the context extension `Γ ▹ F`, the total category of the unstraightening of `F`. For the type
`straightenObj D` of a displayed category `D` over `Γ`, the context extension is the total
category of `D` itself, by `rfl`, and the term `tmMk obj map _ _` is the section `γ ↦ (γ, obj γ)`,
from objects `obj γ` of `D` over `γ` and morphisms `map f : obj γ ⟶[f] obj γ'` of `D`, compatible
with identities and composites. Its equation `sec ≫ 𝐩 F = 𝟙 Γ` holds by `rfl`. The substitution
of `straightenObj E` is the straightening of the reindexing of `E`, by `rfl` (`straightenObj_pull`).
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The substitution of the type `straightenObj E` along `u` is the type of the reindexing of `E`
along `u`, by `rfl`. -/
theorem straightenObj_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (E : Displayed.{u, u} Γ) :
    LaxNormalCat.pull σ (straightenObj E) = straightenObj (DisplayedCat.pull σ E) :=
  rfl

/-- **The term of `straightenObj D` with values `obj γ`** over `γ` and transports
`map f : obj γ ⟶[f] obj γ'`: the section `γ ↦ (γ, obj γ)` of the total category of `D`, which is a
section by `rfl`. -/
def tmMk {D : Displayed.{u, u} Γ} (obj : ∀ γ : Γ, D.Ob γ)
    (map : ∀ {γ γ' : Γ} (f : γ ⟶ γ'), obj γ ⟶[f] obj γ')
    (map_id : ∀ γ : Γ, map (𝟙 γ) = 𝟙ᵈ (obj γ))
    (map_comp : ∀ {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ''), map (f ≫ g) = map f ≫ᵈ map g) :
    LaxNormalCat.Tm (Γ := Γ) (straightenObj D) where
  sec := (show Γ ⥤ D.Total from
    { obj γ := D.tot (obj γ)
      map f := D.totalMk f (map f)
      map_id γ := congrArg (D.totalMk (𝟙 γ)) (map_id γ)
      map_comp f g := congrArg (D.totalMk (f ≫ g)) (map_comp f g) }).toCatHom
  sec_proj := rfl

end ComprehensionCategory.DisplayedModel

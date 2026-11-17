import ComprehensionCategory.Model.OverCat.Displayed.Basic
import ComprehensionCategory.Term
import Displayed.Displayed.Section

/-!
# Terms in the displayed category model

A term `t : Tm(Γ, F)` of a type `F` of the displayed category model is a section of the projection
of the context extension `Γ ▹ F`, the total category of the unstraightening of `F`. For the type
`straightenObj D` of a displayed category `D` over `Γ`, the context extension is the total
category of `D` itself, by `rfl`, so that the terms are the sections of `D` (`Tm.sectionEquiv`),
and the term `tmMk obj map _ _` is the section `γ ↦ (γ, obj γ)`,
from objects `obj γ` of `D` over `γ` and morphisms `map f : obj γ ⟶[f] obj γ'` of `D`, compatible
with identities and composites. Its equation `sec ≫ 𝐩 F = 𝟙 Γ` holds by `rfl`. The substitution
of `straightenObj E` is the straightening of the reindexing of `E`, by `rfl` (`straightenObj_pull`),
and the substitution of the term of a section is the term of its reindexing (`Tm.ofSection_pull`).
A section of `D` reindexed along two morphisms is so a term of `straightenObj D` substituted along
them (`Tm.ofSectionPull₂`).
The projection of `straightenObj D` is that of the total category of `D` (`proj_straightenObj`),
and the extension of `σ` by a term of `straightenObj (DisplayedCat.pull σ D)` is its section
followed by the chosen lift (`consSec_straightenObj`), by `rfl`. They are stated for any `D`, so
that they are checked without unfolding a particular `D`, which can be slow, as for twists.
-/

universe u

namespace ComprehensionCategory.DisplayedModel

open CategoryTheory Displayed Displayed.Straightening

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The substitution of the type `straightenObj E` along `u` is the type of the reindexing of `E`
along `u`, by `rfl`. -/
theorem straightenObj_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (E : Displayed.{u, u} Γ) :
    IProf.pull σ (straightenObj E) = straightenObj (DisplayedCat.pull σ E) :=
  rfl

/-- The projection of the context extension by `straightenObj D` is the projection of the total
category of `D`, by `rfl`. -/
theorem proj_straightenObj (D : Displayed.{u, u} Γ) :
    IProf.proj (a := Γ) (straightenObj D) =
      (D.π.toCatHom : IProf.ext (a := Γ) (straightenObj D) ⟶ Γ) :=
  rfl

/-- The extension of `σ` by a term of `straightenObj (DisplayedCat.pull σ D)`, a section of the
reindexing of `D`, is that section followed by the functor of the chosen lift
`DisplayedCat.pull σ D ⟶[σ] D`, by `rfl`. Stated for any `D`, it is checked without unfolding a
particular `D`. -/
theorem consSec_straightenObj {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (D : Displayed.{u, u} Γ)
    (t : IProf.Tm (Γ := Δ) (straightenObj (DisplayedCat.pull σ D))) :
    consSec σ (t.castTy (straightenObj_pull σ D).symm) =
      t.sec ≫ ((DisplayedCat.clift σ D).total.toCatHom :
        Cat.of (DisplayedCat.pull σ D).Total ⟶ IProf.ext (a := Γ) (straightenObj D)) :=
  rfl

/-- **The term of `straightenObj D` with values `obj γ`** over `γ` and transports
`map f : obj γ ⟶[f] obj γ'`: the section `γ ↦ (γ, obj γ)` of the total category of `D`, which is a
section by `rfl`. -/
def tmMk {D : Displayed.{u, u} Γ} (obj : ∀ γ : Γ, D.Ob γ)
    (map : ∀ {γ γ' : Γ} (f : γ ⟶ γ'), obj γ ⟶[f] obj γ')
    (map_id : ∀ γ : Γ, map (𝟙 γ) = 𝟙ᵈ (obj γ))
    (map_comp : ∀ {γ γ' γ'' : Γ} (f : γ ⟶ γ') (g : γ' ⟶ γ''), map (f ≫ g) = map f ≫ᵈ map g) :
    IProf.Tm (Γ := Γ) (straightenObj D) where
  sec := (show Γ ⥤ D.Total from
    { obj γ := D.tot (obj γ)
      map f := D.totalMk f (map f)
      map_id γ := congrArg (D.totalMk (𝟙 γ)) (map_id γ)
      map_comp f g := congrArg (D.totalMk (f ≫ g)) (map_comp f g) }).toCatHom
  sec_proj := rfl

/-- The section of `D` given by a term of `straightenObj D`: its values, transported along the
equalities of their first components with the points of `Γ`. -/
def Tm.toSection {D : Displayed.{u, u} Γ} (t : IProf.Tm (Γ := Γ) (straightenObj D)) :
    D.Section :=
  Section.ofFunctor t.sec.toFunctor (congrArg Cat.Hom.toFunctor t.sec_proj)

/-- The term of `straightenObj D` of a section of `D`. -/
def Tm.ofSection {D : Displayed.{u, u} Γ} (S : D.Section) :
    IProf.Tm (Γ := Γ) (straightenObj D) where
  sec := S.total.toCatHom
  sec_proj := rfl

/-- The term of `straightenObj D` substituted along `σ` and then `τ`, of a section of `D` reindexed
along them: its type is that of the reindexed category by `rfl` (`straightenObj_pull`). Stated for
any `D`, the type is checked without unfolding a particular `D`. -/
def Tm.ofSectionPull₂ {Θ Δ : Cat.{u, u}} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (D : Displayed.{u, u} Γ)
    (S : (DisplayedCat.pull τ (DisplayedCat.pull σ D)).Section) :
    IProf.Tm (Γ := Θ) (IProf.pull τ (IProf.pull σ (straightenObj D))) :=
  Tm.ofSection S

/-- **The terms of `straightenObj D` are the sections of `D`.** -/
def Tm.sectionEquiv {D : Displayed.{u, u} Γ} :
    IProf.Tm (Γ := Γ) (straightenObj D) ≃ D.Section where
  toFun := Tm.toSection
  invFun := Tm.ofSection
  left_inv _ := Displayed.Tm.ext (Cat.Hom.ext (Section.total_ofFunctor _ _))
  right_inv S := Section.ofFunctor_total S

/-- The section of the term of a section is that section. -/
theorem Tm.toSection_ofSection {D : Displayed.{u, u} Γ} (S : D.Section) :
    Tm.toSection (Tm.ofSection S) = S :=
  Section.ofFunctor_total S

/-- **The substitution of the term of a section is the term of its reindexing**, of type
`straightenObj (DisplayedCat.pull σ D)`, which is that of the substitution by `rfl`. -/
theorem Tm.ofSection_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {D : Displayed.{u, u} Γ} (S : D.Section) :
    (Tm.ofSection S)⦃σ⦄ ≍ Tm.ofSection (S.pull σ) :=
  heq_of_eq (Displayed.Tm.pull_unique σ (Tm.ofSection S) (Tm.ofSection (S.pull σ)) rfl).symm

/-- The terms of heterogeneously equal sections of equal displayed categories are heterogeneously
equal. -/
theorem Tm.ofSection_hext {D D' : Displayed.{u, u} Γ} (hD : D = D') {S : D.Section}
    {S' : D'.Section} (h : S ≍ S') : Tm.ofSection S ≍ Tm.ofSection S' := by
  subst hD
  cases h
  rfl

end ComprehensionCategory.DisplayedModel

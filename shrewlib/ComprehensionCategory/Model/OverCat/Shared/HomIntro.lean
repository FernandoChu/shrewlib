import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Cat.Term
import ComprehensionCategory.Model.OverCat.Displayed.Term

/-!
# Hom-introduction

For a type `A` of the category model in context `Γ`, twisting its Hom-type makes it a type of the
displayed model that depends covariantly on both of its variables, so that it can be substituted
along the diagonal, and the identities are a term of it:

```
         Γ ⊢ A type
  ----------------------------------- Hom-Form
    Γ ▹ a : Aᵒᵖ ▹ b : A ⊢ Homₐ(a, b) type
  ----------------------------------- Exchange
    Γ ▹ b : A ▹ a : Aᵒᵖ ⊢ Homₐ(a, b) type
  ----------------------------------- Twist
    Γ ▹ b : A ▹ a : A ⊢ Homₐ(ā, b) type
  ----------------------------------- Subst
    Γ ▹ a : A ⊢ Homₐ(ā, a) type

         Γ ⊢ A type
  ----------------------------------- Hom-Intro
    Γ ▹ a : A ⊢ refl a : Homₐ(ā, a)
```

* Exchange: `Hom[A]` lives in context `Γ ▹ Aᵒᵖ ▹ A⦃𝐩 Aᵒᵖ⦄`, and the twist takes types whose
  contravariant variable comes last. Along the exchange `homExch A`, `((γ, b), a) ↦ ((γ, a), b)`,
  from `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ`, it is the dependent profunctor `homProf A` over `A⦃𝐩 A⦄`
  (`homProf_obj`, `homProf_map`). This is stated pointwise: as a composite with `homExch A`, the
  rules `Functor.id_comp` and `Functor.comp_id` would compare the two contexts, which is slow.
* Twist: the twist of `homProf A` is a type of the displayed model in context
  `Γ ▹ A ▹ A⦃𝐩 A⦄` (`Shared/Twist.lean`).
* Subst: its substitution along the diagonal `diag A : Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄` is the displayed
  type `twistedHom A` in context `Γ ▹ A` (`twistedHom_eq`).

Concretely, `twistedHom A` is the straightening of the displayed category `twistedHomDisp A` over
`Γ ▹ A` whose objects over `(γ, a)` are the endomorphisms `e : a ⟶ a` of `A γ`, and whose
morphisms over `(θ, α) : (γ, a) ⟶ (γ', a')`, with `α : A θ a ⟶ a'`, from `e` to `e'` are the proofs
of `A θ e ≫ α = α ≫ e'`. The term `refl A` of Hom-Intro is the section `(γ, a) ↦ 𝟙 a`, through which
every morphism `(θ, α)` goes to the proof of `A θ (𝟙 a) ≫ α = α ≫ 𝟙 a'`, by `rfl`.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- **The exchange** `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ ⟶ Γ ▹ Aᵒᵖ ▹ A⦃𝐩 Aᵒᵖ⦄` of the two variables,
`((γ, b), a) ↦ ((γ, a), b)`. -/
def homExch (A : ICatLax.{u}.Ty Γ) : Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ ⟶ Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄ :=
  (show ((Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ : Cat.{u, u}) : Type u) ⥤ ((Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄ : Cat.{u, u}) :
      Type u) from
    { obj X := ⟨⟨X.1.1, X.2⟩, X.1.2⟩
      map F := ⟨⟨F.base.base, F.fiber⟩, F.base.fiber⟩
      map_id _ := rfl
      map_comp _ _ := rfl }).toCatHom

/-- The Hom-type of `A` with its variables exchanged, as a dependent profunctor over `A⦃𝐩 A⦄`: at
`((γ, b), a)`, the discrete category on the morphisms `a ⟶ b` of `A γ`, and at a morphism
`((θ, β), φ)`, `h ↦ φ ≫ A θ h ≫ β`. It is `Hom[A]` along the exchange (`homProf_obj`,
`homProf_map`). -/
def homProf (A : ICatLax.{u}.Ty Γ) :
    (∫ ((A⦃𝐩 A⦄ : ICatLax.{u}.Ty (Γ ▹ A)) : (Γ ▹ A : Cat.{u, u}) ⥤ Cat.{u, u}))ᵒᵖ.Total ⥤
      Cat.{u, u} where
  obj X := discrete' (@Quiver.Hom (A.obj X.1.1) _ X.2 X.1.2)
  map g := discreteMap' (homAct A g.base.base g.fiber g.base.fiber)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- `homProf A` is `Hom[A]` along the exchange, on objects. -/
theorem homProf_obj (A : ICatLax.{u}.Ty Γ) (X : ((Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ : Cat.{u, u}) : Type u)) :
    (homProf A).obj X = (homFunctor A).obj ((homExch A).toFunctor.obj X) :=
  rfl

/-- `homProf A` is `Hom[A]` along the exchange, on morphisms. -/
theorem homProf_map (A : ICatLax.{u}.Ty Γ) {X Y : ((Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ : Cat.{u, u}) : Type u)}
    (g : X ⟶ Y) :
    (homProf A).map ⟨g.base, g.fiber⟩ ≍ (homFunctor A).map ((homExch A).toFunctor.map g) :=
  HEq.rfl

/-- The displayed category of the twisted Hom-type of `A`, over `Γ ▹ A`: the twist of `homProf A`,
reindexed along the diagonal. Its objects over `(γ, a)` are the endomorphisms of `a`. -/
def twistedHomDisp (A : ICatLax.{u}.Ty Γ) :
    Displayed.{u, u, u, u} ((Γ ▹ A : Cat.{u, u}) : Type u) :=
  DisplayedCat.pull (diag A) (twistDisp (homProf A))

/-- **The twisted Hom-type of `A`**, `Γ ▹ a : A ⊢ Homₐ(ā, a)`, a type of the displayed model. -/
def twistedHom (A : ICatLax.{u}.Ty Γ) : Straightening.LaxNormalCat.{u}.Ty (Γ ▹ A) :=
  Straightening.straightenObj (twistedHomDisp A)

/-- **The twisted Hom-type is derivable**: it is the twist of the Hom-type of `A`, with its
variables exchanged, substituted along the diagonal. -/
theorem twistedHom_eq (A : ICatLax.{u}.Ty Γ) : twistedHom A = (twist (homProf A))⦃diag A⦄ :=
  (DisplayedModel.straightenObj_pull (diag A) (twistDisp (homProf A))).symm

/-- **Hom-Intro**: the term `refl` of the twisted Hom-type, the section `(γ, a) ↦ 𝟙 a`. -/
def refl (A : ICatLax.{u}.Ty Γ) : Tm(Γ ▹ A, twistedHom A) :=
  DisplayedModel.tmMk (D := twistedHomDisp A) (fun x => 𝟙 (show A.obj x.1 from x.2))
    (fun _ => ⟨⟨rfl⟩⟩) (fun _ => rfl) fun _ _ => rfl

end ComprehensionCategory.OverCat

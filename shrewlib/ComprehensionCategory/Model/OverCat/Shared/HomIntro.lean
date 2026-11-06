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
    Γ ▹ b : A ▹ a : Aᵒᵖ ⊢ Homₐ(a, b) type
  ----------------------------------- Twist
    Γ ▹ b : A ▹ a : A ⊢ Homₐ(ā, b) type
  ----------------------------------- Subst
    Γ ▹ a : A ⊢ Homₐ(ā, a) type

         Γ ⊢ A type
  ----------------------------------- Hom-Intro
    Γ ▹ a : A ⊢ refl a : Homₐ(ā, a)
```

* Twist: `Hom[A]` lives in context `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ`, with its contravariant variable last, so
  its underlying type `homFunctor A` of the category model has a twist, a type of the displayed
  model in context `Γ ▹ A ▹ A⦃𝐩 A⦄` (`Shared/Twist.lean`).
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

/-- The displayed category of the twisted Hom-type of `A`, over `Γ ▹ A`: the twist of its Hom-type,
reindexed along the diagonal. Its objects over `(γ, a)` are the endomorphisms of `a`. -/
def twistedHomDisp (A : ICatLax.{u, u}.Ty Γ) :
    Displayed.{u, u} ((Γ ▹ A : Cat.{u, u}) : Type u) :=
  DisplayedCat.pull (diag A) (twistDisp (homFunctor A))

/-- **The twisted Hom-type of `A`**, `Γ ▹ a : A ⊢ Homₐ(ā, a)`, a type of the displayed model. -/
def twistedHom (A : ICatLax.{u, u}.Ty Γ) : Straightening.LaxNormalCat.{u, u, u}.Ty (Γ ▹ A) :=
  Straightening.straightenObj (twistedHomDisp A)

/-- **The twisted Hom-type is derivable**: it is the twist of the Hom-type of `A`, substituted along
the diagonal. -/
theorem twistedHom_eq (A : ICatLax.{u, u}.Ty Γ) :
    twistedHom A = (twist (homFunctor A))⦃diag A⦄ :=
  (DisplayedModel.straightenObj_pull (diag A) (twistDisp (homFunctor A))).symm

/-- **Hom-Intro**: the term `refl` of the twisted Hom-type, the section `(γ, a) ↦ 𝟙 a`. -/
def refl (A : ICatLax.{u, u}.Ty Γ) : Tm(Γ ▹ A, twistedHom A) :=
  DisplayedModel.tmMk (D := twistedHomDisp A) (fun x => 𝟙 (show A.obj x.1 from x.2))
    (fun _ => ⟨⟨rfl⟩⟩) (fun _ => rfl) fun _ _ => rfl

end ComprehensionCategory.OverCat

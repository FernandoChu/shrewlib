import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Cat.TermRules
import ComprehensionCategory.Model.OverCat.Displayed.Term

/-!
# Hom-introduction

For a type `A` of the category model in context `Γ`, twisting its Hom-type makes it a type of the
displayed model that depends covariantly on both of its variables, so that it can be substituted
along the diagonal, and along a term `a₀` of `A` in both variables, where the identities are a
term of it:

```
         Γ ⊢ A type
  ----------------------------------- Hom-Form
    Γ ▹ b : A ▹ a : Aᵒᵖ ⊢ Homₐ(a, b) type
  ----------------------------------- Twist
    Γ ▹ b : A ▹ a : A ⊢ Homₐ(ā, b) type
  ----------------------------------- Subst
    Γ ▹ a : A ⊢ Homₐ(ā, a) type

    Γ ⊢ A type      Γ ⊢ a₀ : A
  ----------------------------------- Hom-Intro
    Γ ⊢ refl_a₀ : Homₐ(ā₀, a₀)
```

* Twist: `Hom[A]` lives in context `Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ`, with its contravariant variable last, so
  its underlying type `homFunctor A` of the category model has a twist, a type of the displayed
  model in context `Γ ▹ A ▹ A⦃𝐩 A⦄` (`Shared/Twist.lean`).
* Subst: its substitution along the diagonal `diag A : Γ ▹ A ⟶ Γ ▹ A ▹ A⦃𝐩 A⦄` is the displayed
  type `twistedHom A` in context `Γ ▹ A` (`twistedHom_eq`). Concretely, `twistedHom A` is the
  straightening of the displayed category `twistedHomDisp A` over `Γ ▹ A` whose objects over
  `(γ, a)` are the endomorphisms `e : a ⟶ a` of `A γ`, and whose morphisms over
  `(θ, α) : (γ, a) ⟶ (γ', a')`, with `α : A θ a ⟶ a'`, from `e` to `e'` are the proofs of
  `A θ e ≫ α = α ≫ e'`.
* Hom-Intro: for a term `Γ ⊢ a₀ : A`, the type `Homₐ(ā₀, a₀)` is the twist of the Hom-type
  substituted along `[a₀/a] : Γ ▹ b : A ⟶ Γ ▹ b : A ▹ a : A`, the section `(a₀⦃𝐩 A⦄).sec` of `a₀`
  weakened to `Γ ▹ A`, and then along `[a₀/b]`, the section of `a₀`. The term `reflAt a₀` is the
  section `γ ↦ 𝟙 (a₀ γ)`, through which every morphism `θ` goes to the proof of
  `A θ (𝟙 (a₀ γ)) ≫ a₀ θ = a₀ θ ≫ 𝟙 (a₀ γ')`, by `rfl`. Its type is a substitution along the
  sections of terms, so that it extends the section of `a₀` to the substitution
  `[a₀/b, refl_a₀/f]` of Hom-elimination (`Shared/HomElim`) with no transport.

Hom-Intro is stable under substitution: `refl_a₀⦃σ⦄` is `refl` of `a₀⦃σ⦄` (`reflAt_pull`). Its type
is stable too (`reflAtTy_pull`), by `rfl` in the kernel, though the elaborator does not find it
out. This equality is a rule, oriented towards the type at the substituted term and declared
after the composition of substitutions, with the same head, so that `reflAt_pull` needs no
transport.

The values `a₀ γ : A γ` are those of the section `Tm.toSection a₀`, and the section of the weakened
term computes, by the rules of `OverCat/Cat/TermRules`, which this file imports.
-/

universe u

namespace ComprehensionCategory.OverCat

open CategoryTheory Displayed Displayed.Opfibration.Straightening Displayed.Discrete CatModel

open scoped Displayed

variable {Γ : Cat.{u, u}}

/-- The displayed category of the twisted Hom-type of `A`, over `Γ ▹ A`: the twist of its Hom-type,
reindexed along the diagonal. Its objects over `(γ, a)` are the endomorphisms of `a`. -/
def twistedHomDisp (A : ICatLax.{u, u}.Ty Γ) :
    Displayed.{u, u} (Γ ▹ A : Cat.{u, u}) :=
  DisplayedCat.pull (diag A) (twistDisp (homFunctor A))

/-- **The twisted Hom-type of `A`**, `Γ ▹ a : A ⊢ Homₐ(ā, a)`, a type of the displayed model. -/
def twistedHom (A : ICatLax.{u, u}.Ty Γ) : Straightening.IProf.{u, u, u}.Ty (Γ ▹ A) :=
  Straightening.straightenObj (twistedHomDisp A)

/-- **The twisted Hom-type is derivable**: it is the twist of the Hom-type of `A`, substituted along
the diagonal. -/
theorem twistedHom_eq (A : ICatLax.{u, u}.Ty Γ) :
    twistedHom A = (twist (homFunctor A))⦃diag A⦄ :=
  (DisplayedModel.straightenObj_pull (diag A) (twistDisp (homFunctor A))).symm

/-- **Hom-Intro at a term**: for `Γ ⊢ a₀ : A`, the term `Γ ⊢ refl_a₀ : Homₐ(ā₀, a₀)`, with value
`𝟙 (a₀ γ)` at `γ`. Its type is the twist of the Hom-type substituted along
`[a₀/a] : Γ ▹ b : A ⟶ Γ ▹ b : A ▹ a : A`, the section of `a₀` weakened to `Γ ▹ A`, and then along
`[a₀/b]`, the section of `a₀`, so that it extends the section of `a₀` with no transport. -/
def reflAt {A : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, A)) :
    Tm(Γ, ((twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄)⦃a₀.sec⦄) :=
  DisplayedModel.Tm.ofSectionPull₂ a₀.sec (a₀⦃𝐩 A⦄).sec (twistDisp (homFunctor A))
    { obj := fun γ => 𝟙 ((Tm.toSection a₀).obj γ)
      map := fun _ => ⟨⟨rfl⟩⟩ }

/-- **The type `Homₐ(ā₀, a₀)` is stable under substitution**: along `σ`, it is that of `A⦃σ⦄` at
`a₀⦃σ⦄`. It is a rule, so that the substitution of `reflAt a₀` has the type of `reflAt a₀⦃σ⦄`. -/
@[rewrite_rule]
theorem reflAtTy_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, A)) :
    (((twist (homFunctor A))⦃(a₀⦃𝐩 A⦄).sec⦄)⦃a₀.sec⦄)⦃σ⦄ =
      ((twist (homFunctor (A⦃σ⦄)))⦃(a₀⦃σ⦄⦃𝐩 (A⦃σ⦄)⦄).sec⦄)⦃a₀⦃σ⦄.sec⦄ := by
  kernel_rfl'

/-- **Hom-Intro is stable under substitution**: `refl_a₀⦃σ⦄` is `refl` of `a₀⦃σ⦄`. -/
theorem reflAt_pull {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {A : ICatLax.{u, u}.Ty Γ} (a₀ : Tm(Γ, A)) :
    (reflAt a₀)⦃σ⦄ = reflAt a₀⦃σ⦄ :=
  (Tm.pull_unique σ (reflAt a₀) (reflAt a₀⦃σ⦄)
    (Cat.Hom.ext (Functor.hext (fun _ => by kernel_rfl') fun _ _ _ => by kernel_rfl'))).symm

end ComprehensionCategory.OverCat

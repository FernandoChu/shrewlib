import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Shared.Universe

/-!
# Shared type formers

Type formers relating several of the models over `Cat`: their premises are types of one model, and
their conclusion a type of another, in a context of the first.

* `Hom`: the Hom-types of the category model, types of the discrete model. For a type `A` of the
  category model, `Hom[A]` sends `((γ, a), b)` to the discrete category on the morphisms `a ⟶ b`
  of `A γ`. It is stable under substitution by `rfl`, and its own opposite in the discrete model,
  as a rewrite rule, since these discrete categories are, by `propext`.
* `Universe`: the Coquand-style universe `UDisc Γ` of the discrete types of level `v`, a type of
  the category model at level `v + 1`, the constant functor at the category of small discrete
  categories. Its terms are exactly the functors `Γ ⥤ Cat.{v, v}` into discrete categories, by
  inverse maps `ElDisc` and `codeDisc`, stable under substitution: a universe along the lift of
  the discrete types of level `v`, `HasUniverse liftDiscComprehensionMap`.
-/

universe u

open CategoryTheory Displayed ComprehensionCategory OverCat CatModel DiscreteModel
  Opfibration.Straightening Displayed.Discrete.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **Hom-op**: the Hom-type is its own opposite, as a rewrite rule. -/
recall ComprehensionCategory.OverCat.op_hom {Γ : Cat.{u, u}} (A : ICatLax.{u}.Ty Γ) :
    Hom[A]ᵒᵖ = Hom[A]

/-- The Hom-types are stable under substitution. -/
recall ComprehensionCategory.OverCat.pull_hom {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    (A : ICatLax.{u}.Ty Γ) :
    Hom[A]⦃𝐪(𝐪(σ, Aᵒᵖ), A⦃𝐩 (Aᵒᵖ)⦄)⦄ = Hom[A⦃σ⦄]

section

variable {Γ : Cat.{u, u}} (A : ICatLax.{u}.Ty Γ)

/-- The Hom-type of a type of the category model is a type of the discrete model. -/
example : IDisc.{u}.Ty (Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄) := Hom[A]

/-- Hom-op holds judgmentally, by the rule `op_hom`. -/
example : Hom[A]ᵒᵖ = Hom[A] := rfl

/-- The rule leaves the other opposites of the discrete model unfolding as before. -/
example (B : IDisc.{u}.Ty Γ) : (Bᵒᵖ)ᵒᵖ = B := rfl

example (B : IDisc.{u}.Ty Γ) : (Bᵒᵖ).toFunctor = B.toFunctorᵒᵖ := rfl

end

section Universe

universe v

/-- **The universe of discrete types is Coquand-style**: its terms are the functors into discrete
categories of `Cat.{v, v}`. -/
recall ComprehensionCategory.OverCat.ElDisc_codeDisc {Γ : Cat.{v + 1, v + 1}}
    (A : Discrete.Straightening.IDiscOb.{v} Γ) : ElDisc (codeDisc A) = A

recall ComprehensionCategory.OverCat.codeDisc_ElDisc {Γ : Cat.{v + 1, v + 1}}
    (t : Tm(Γ, UDisc Γ)) : codeDisc (ElDisc t) = t

/-- The universe of discrete types is closed. -/
recall ComprehensionCategory.OverCat.pull_UDisc {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (UDisc Γ)⦃σ⦄ = UDisc Δ

/-- **The category model has a universe of the discrete types of level `v`**, along their lift. -/
recall ComprehensionCategory.OverCat.hasUniverseDisc : HasUniverse liftDiscComprehensionMap.{v}

end Universe

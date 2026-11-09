import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Shared.HomDisc
import ComprehensionCategory.Model.OverCat.Shared.Universe
import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Shared.HomIntro

/-!
# Shared type formers

Type formers relating several of the models over `Cat`: their premises are types of one model, and
their conclusion a type of another, in a context of the first.

* `Hom`: the Hom-types of the category model, types of the discrete model. For a type `A` of the
  category model, `Hom[A]`, in context `Γ ▹ b : A ▹ a : Aᵒᵖ`, sends `((γ, b), a)` to the discrete
  category on the morphisms `a ⟶ b` of `A γ`. It is stable under substitution by `rfl`, and its
  own opposite in the discrete model, as a rewrite rule, since these discrete categories are, by
  `propext`. The Hom-type of two terms `a : Tm(Γ, Aᵒᵖ)` and `b : Tm(Γ, A)`, in context `Γ`, as in
  the paper, is its substitution along their pairing (`homAt`), stable under substitution.
* `HomDisc`: the Hom-types of the types of the discrete model, defined there, with an action on
  morphisms given by discreteness. Forgetting the discreteness preserves them strictly: they are
  those of the category model, since the morphisms of discrete categories are unique. Hom-Disc:
  if empty types are unique, terms `a b` of a discrete type with a term of the Hom-type from `a`
  to `b` are equal.
* `Universe`: the Coquand-style universe `UDisc Γ` of the discrete types of level `v`, a type of
  the category model at level `v + 1`, the constant functor at the category of small discrete
  categories. Its terms are exactly the functors `Γ ⥤ Cat.{v, v}` into discrete categories, by
  inverse maps `ElDisc` and `codeDisc`, stable under substitution: a universe along the lift of
  the discrete types of level `v`, `HasUniverse liftDiscComprehensionMap`.
* `Twist`: the twist of a type of the category model in context `Γ ▹ Bᵒᵖ`, a type of the
  displayed model in context `Γ ▹ B`: seeing the type as a dependent profunctor over `B`, the
  straightening of its unstraightening, a D2SFib over the unstraightening of `B`, displayed over
  `Γ ▹ B`. The twist of a type weakened from `Γ` is that type, seen in the displayed model,
  weakened (Twist-Weak).
* `HomIntro`: the twisted Hom-type `Γ ▹ a : A ⊢ Homₐ(ā, a)` of a type `A` of the category model, a
  type of the displayed model whose objects over `(γ, a)` are the endomorphisms of `a`, derived from
  `Hom[A]` by twist and substitution along the diagonal, and its term `refl A`, the
  identities (Hom-Intro).
-/

universe u

open CategoryTheory Displayed ComprehensionCategory OverCat CatModel DiscreteModel
  Opfibration.Straightening Displayed.Discrete.Straightening

open scoped Displayed

/-! ## Main results -/

/-- **Hom-op**: the Hom-type is its own opposite, as a rewrite rule. -/
recall ComprehensionCategory.OverCat.op_hom {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) :
    Hom[A]ᵒᵖ = Hom[A]

/-- The Hom-types are stable under substitution. -/
recall ComprehensionCategory.OverCat.pull_hom {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    (A : ICatLax.{u, u}.Ty Γ) :
    Hom[A]⦃𝐪(𝐪(σ, A), (A⦃𝐩 A⦄)ᵒᵖ)⦄ = Hom[A⦃σ⦄]

section

variable {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ)

/-- The Hom-type of a type of the category model is a type of the discrete model. -/
example : IDisc.{u, u}.Ty (Γ ▹ A ▹ (A⦃𝐩 A⦄)ᵒᵖ) := Hom[A]

/-- Hom-op holds judgmentally, by the rule `op_hom`. -/
example : Hom[A]ᵒᵖ = Hom[A] := rfl

/-- The rule leaves the other opposites of the discrete model unfolding as before. -/
example (B : IDisc.{u, u}.Ty Γ) : (Bᵒᵖ)ᵒᵖ = B := rfl

example (B : IDisc.{u, u}.Ty Γ) : (Bᵒᵖ).toFunctor = B.toFunctorᵒᵖ := rfl

end

section HomAt

/-- **Hom-Form**, as in the paper: the Hom-type of two terms, a type of the discrete model. -/
example {Γ : Cat.{u, u}} {A : ICatLax.{u, u}.Ty Γ} (a : Tm(Γ, CatModel.op A)) (b : Tm(Γ, A)) :
    IDisc.{u, u}.Ty Γ :=
  homAt a b

/-- The Hom-type of two terms is stable under substitution. -/
recall ComprehensionCategory.OverCat.pull_homAt {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    {A : ICatLax.{u, u}.Ty Γ} (a : Tm(Γ, CatModel.op A)) (b : Tm(Γ, A)) :
    (homAt a b)⦃σ⦄ = homAt (A := A⦃σ⦄) a⦃σ⦄ b⦃σ⦄

/-- Hom-op for the Hom-type of two terms. -/
recall ComprehensionCategory.OverCat.op_homAt {Γ : Cat.{u, u}} {A : ICatLax.{u, u}.Ty Γ}
    (a : Tm(Γ, CatModel.op A)) (b : Tm(Γ, A)) : DiscreteModel.op (homAt a b) = homAt a b

/-- **Forgetting the discreteness preserves the Hom-types strictly**, in context form and for two
terms. -/
recall ComprehensionCategory.OverCat.homDisc_eq {Γ : Cat.{u, u}} (A : IDisc.{u, u}.Ty Γ) :
    homDisc A = Hom[forgetComprehensionMap.toPre.obj A]

recall ComprehensionCategory.OverCat.homDiscAt_eq {Γ : Cat.{u, u}} {A : IDisc.{u, u}.Ty Γ}
    (a : Tm(Γ, DiscreteModel.op A)) (b : Tm(Γ, A)) :
    homDiscAt a b = homAt (A := forgetComprehensionMap.toPre.obj A)
      (forgetComprehensionMap.tmEquiv a) (forgetComprehensionMap.tmEquiv b)

/-- **Hom-Disc**: if empty types are unique, terms of a discrete type with a term of the Hom-type
from one to the other are equal. -/
recall ComprehensionCategory.OverCat.eq_of_homDiscAt {Γ : Cat.{u, u}} (hE : EmptyUnique.{u})
    {A : IDisc.{u, u}.Ty Γ} (a b : Tm(Γ, A)) (f : Tm(Γ, homDiscAt (OverCat.Tm.toOp hE a) b)) :
    a = b

end HomAt

section Universe

universe v

/-- **The universe of discrete types is Coquand-style**: its terms are the functors into discrete
categories of `Cat.{v, v}`. -/
recall ComprehensionCategory.OverCat.ElDisc_codeDisc {Γ : Cat.{v + 1, v + 1}}
    (A : Discrete.Straightening.IDiscOb.{v, v} Γ) : ElDisc (codeDisc A) = A

recall ComprehensionCategory.OverCat.codeDisc_ElDisc {Γ : Cat.{v + 1, v + 1}}
    (t : Tm(Γ, UDisc Γ)) : codeDisc (ElDisc t) = t

/-- The universe of discrete types is closed. -/
recall ComprehensionCategory.OverCat.pull_UDisc {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ) :
    (UDisc Γ)⦃σ⦄ = UDisc Δ

/-- **The category model has a universe of the discrete types of level `v`**, along their lift. -/
recall ComprehensionCategory.OverCat.hasUniverseDisc : HasUniverse liftDiscComprehensionMap.{v}

end Universe

/-- **Twist-Weak**: the twist of a weakened type is the type, in the displayed model, weakened. -/
recall ComprehensionCategory.OverCat.twist_weak {Γ : Cat.{u, u}} (B C : ICatLax.{u, u}.Ty Γ) :
    twist (C⦃𝐩 (Bᵒᵖ)⦄) = (catToDisp C)⦃𝐩 B⦄

/-- **The twisted Hom-type is derivable**: the twist of the Hom-type, substituted along the
diagonal. -/
recall ComprehensionCategory.OverCat.twistedHom_eq {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ)
    :
    twistedHom A = (twist (homFunctor A))⦃diag A⦄

/-- **Hom-Intro**: the identities are a term of the twisted Hom-type. -/
recall ComprehensionCategory.OverCat.refl {Γ : Cat.{u, u}} (A : ICatLax.{u, u}.Ty Γ) :
    Tm(Γ ▹ A, twistedHom A)

import ComprehensionCategory.Model.OverCat.Shared.Hom
import ComprehensionCategory.Model.OverCat.Shared.HomDisc
import ComprehensionCategory.Model.OverCat.Shared.Universe
import ComprehensionCategory.Model.OverCat.Shared.Twist
import ComprehensionCategory.Model.OverCat.Shared.HomIntro
import ComprehensionCategory.Model.OverCat.Shared.Pi
import ComprehensionCategory.Model.OverCat.Shared.OpSigma
import ComprehensionCategory.Model.OverCat.Shared.FunTwist
import ComprehensionCategory.Model.OverCat.Shared.HomElim

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
  inverse maps `ElDisc` and `codeDisc`, stable under substitution: `HasUniverse ICatLax
  SmallIDisc`. And the universe `Uop Γ` of the contravariant types of level `v`, the opposite of
  the universe `U Γ`, whose terms are exactly the functors `Γᵒᵖ ⥤ Cat.{v, v}`, by `ElOp` and
  `codeOp`: `HasUniverse ICatLax SmallICatOp`. Its terms decode to types of the contravariant
  category model.
* `Twist`: the twist of a type of the category model in context `Γ ▹ Bᵒᵖ`, a type of the
  displayed model in context `Γ ▹ B`: seeing the type as a dependent profunctor over `B`, the
  straightening of its unstraightening, a D2SFib over the unstraightening of `B`, displayed over
  `Γ ▹ B`. The twist of a type weakened from `Γ` is that type, seen in the displayed model,
  weakened (Twist-Weak). The twist is stable under substitution, by `rfl`, as a
  rule.
* `HomIntro`: the twisted Hom-type `Γ ▹ a : A ⊢ Homₐ(ā, a)` of a type `A` of the category model, a
  type of the displayed model whose objects over `(γ, a)` are the endomorphisms of `a`, derived from
  `Hom[A]` by twist and substitution along the diagonal, and its term `refl A`, the
  identities (Hom-Intro).
* `Pi`: the Π-types `Π[A] B` of the category model over the contravariant one, for `A` a
  functor `Γᵒᵖ ⥤ Cat` and `B` a functor `Γ ⋉ A ⥤ Cat`: the functor sending `γ` to the category of
  sections of `∫ B` over the fibre `A γ`, stable under substitution by `rfl`. Abstraction and
  application are the bijections between the terms of `B`, the sections of `∫ B`, those of the
  dependent product `piDisp A (∫ B)` and those of the unstraightening of `Π[A] B`, and abstraction
  is stable under substitution: `HasPi ICatOpLax ICatLax`.
* `OpSigma`: the opposite of a Σ-type. For `B` in context `Γ ▹ A`, the context extension by the
  twist of `Bᵒᵖ`, written `Bᵒᵖ[ā/a]` in the paper, is that by `(Σ[A] B)ᵒᵖ`, over `Γ`, so the terms
  of `(Σ[A] B)ᵒᵖ` are the pairs of a term `x` of `Aᵒᵖ` and a term of the twist of `Bᵒᵖ` at `x`,
  naturally in `Γ`.
* `FunTwist`: the twist `Γ ▹ X : U ▹ Y : U ⊢ Ȳ → X` of the function type
  `Γ ▹ X : U ▹ Y : Uᵒᵖ ⊢ Y → X`, a Π-type, at level `v + 1`. Substituted by the codes of two types
  `A` and `B` of level `v`, its terms are those of `B` in context `Γ ▹ a : A`: a section over `γ`
  is a functor `A γ ⥤ B γ`, and over `g` a natural transformation `B g ∘ T γ ⇒ T γ' ∘ A g`, and
  these are the sections of `∫ B` over `Γ ▹ A`. Both `Ā → B` and this bijection are stable under
  substitution.
* `HomElim`: Hom-Elim and Hom-Comp. For `X` in context `Γ ▹ a : A` and a motive `D` of the category
  model in context `Γ ▹ b : A ▹ a : A ▹ f : Homₐ(ā, b) ▹ x : X`, a term `d` of
  `D[ā/a, a/b, refl_a/f]` gives the term `j(f, x, d)` of `D`, with `j(refl_a, x, d) ≡ d`, stable
  under substitution. As in the paper, `j` is the chosen lift of the comma AWFS on `Cat` from the
  left adjoint right inverse `r : (γ, a, x) ↦ (γ, a, a, 𝟙 a, x)`, an `L`-coalgebra, to the split
  opfibration `𝐩 D`, an `R`-algebra; stability comes from the functoriality of the chosen lifts.
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
recall ComprehensionCategory.OverCat.hasUniverseDisc :
    HasUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1} SmallIDisc.{v}

/-- **The universe of contravariant types is Coquand-style**: its terms are the functors
`Γᵒᵖ ⥤ Cat.{v, v}`. It is the opposite of the universe of types. -/
recall ComprehensionCategory.OverCat.ElOp_codeOp {Γ : Cat.{v + 1, v + 1}}
    (A : (↑Γ)ᵒᵖ ⥤ Cat.{v, v}) : ElOp (codeOp A) = A

recall ComprehensionCategory.OverCat.codeOp_ElOp {Γ : Cat.{v + 1, v + 1}}
    (t : Tm(Γ, Uop Γ)) : codeOp (ElOp t) = t

recall ComprehensionCategory.OverCat.Uop_eq_op (Γ : Cat.{v + 1, v + 1}) :
    Uop Γ = CatModel.op (CatModel.U Γ)

/-- **The category model has a universe of the contravariant types of level `v`.** -/
recall ComprehensionCategory.OverCat.hasUniverseOp :
    HasUniverse ICatLax.{v + 1, v + 1, v + 1, v + 1} CatOpModel.SmallICatOp.{v}

/-- A term of the universe of contravariant types decodes to a type of the contravariant category
model. -/
example {Γ : Cat.{v + 1, v + 1}} (t : Tm(Γ, Uop Γ)) :
    Fibration.Straightening.ICatOpLax.{v + 1, v + 1}.Ty Γ :=
  decode liftOpComprehensionMap t

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

/-- **The category model has Π-types over the contravariant model.** -/
recall ComprehensionCategory.OverCat.hasPi :
    HasPi Fibration.Straightening.ICatOpLax.{u, u, u, u} ICatLax.{u, u, u, u}

/-- The Π-type of `A` and `B` sends `γ` to the category of sections of `∫ B` over `A γ`. -/
example {Γ : Cat.{u, u}} (A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ)
    (B : ICatLax.{u, u}.Ty (Γ ▹ A)) (γ : Γ) :
    ((Π[A] B : ICatLax.{u, u}.Ty Γ).obj γ : Type u) = PiFib A B γ :=
  rfl

/-- Π-types are stable under substitution by `rfl`. -/
example {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (A : Fibration.Straightening.ICatOpLax.{u, u}.Ty Γ)
    (B : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    (Π[A] B : ICatLax.{u, u}.Ty Γ)⦃σ⦄ = Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄ :=
  rfl

section OpSigma

variable {Γ : Cat.{u, u}}

/-- **The terms of the opposite of a Σ-type** are pairs of a term of `Aᵒᵖ` and a term of the twist
of `Bᵒᵖ` at it. -/
recall ComprehensionCategory.OverCat.opSigmaEquiv (A : ICatLax.{u, u}.Ty Γ)
    (B : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    Tm(Γ, (Σ[A] B)ᵒᵖ) ≃ Σ x : Tm(Γ, Aᵒᵖ), Tm(Γ, (twist (B := Aᵒᵖ) (Bᵒᵖ))⦃x.sec⦄)

/-- It comes from an isomorphism of contexts over `Γ`. -/
recall ComprehensionCategory.OverCat.opSigmaIso (A : ICatLax.{u, u}.Ty Γ)
    (B : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    (Γ ▹ Aᵒᵖ ▹ twist (B := Aᵒᵖ) (Bᵒᵖ) : Cat.{u, u}) ≅ Γ ▹ (Σ[A] B)ᵒᵖ

/-- The bijection is natural in `Γ`. -/
recall ComprehensionCategory.OverCat.opFst_pull {A : ICatLax.{u, u}.Ty Γ}
    {B : ICatLax.{u, u}.Ty (Γ ▹ A)} {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) :
    opFst (A := A⦃σ⦄) (B := B⦃𝐪(σ, A)⦄) t⦃σ⦄ = (opFst t)⦃σ⦄

recall ComprehensionCategory.OverCat.opSnd_pull {A : ICatLax.{u, u}.Ty Γ}
    {B : ICatLax.{u, u}.Ty (Γ ▹ A)} {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (t : Tm(Γ, (Σ[A] B)ᵒᵖ)) :
    (opSnd (A := A⦃σ⦄) (B := B⦃𝐪(σ, A)⦄) t⦃σ⦄).sec ≍ ((opSnd t)⦃σ⦄).sec

/-- The twist is stable under substitution, by a rule. -/
example {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) {B : ICatLax.{u, u}.Ty Γ} (C : ICatLax.{u, u}.Ty (Γ ▹ Bᵒᵖ)) :
    (twist C)⦃𝐪(σ, B)⦄ = twist (C⦃𝐪(σ, Bᵒᵖ)⦄) :=
  rfl

end OpSigma

section FunTwist

universe v

/-- **The terms of the twisted function type `Ā → B`** are those of `B` in context `Γ ▹ a : A`. -/
recall ComprehensionCategory.OverCat.funTwistEquiv {Γ : Cat.{v + 1, v + 1}}
    (A B : Γ ⥤ Cat.{v, v}) :
    Tm(Γ, funTwist A B) ≃ Tm(Γ ▹ CatModel.lift A, (CatModel.lift B)⦃𝐩 (CatModel.lift A)⦄)

/-- `Ā → B` is the twist of the function type over the universes, substituted by the codes. -/
example {Γ : Cat.{v + 1, v + 1}} (A B : Γ ⥤ Cat.{v, v}) :
    funTwist A B =
      (twist (B := CatModel.U (funCtx₀ Γ)) (Π[funDom Γ] (funCod Γ)⦃𝐩 (funDom Γ)⦄))⦃consSec
        (CatModel.code B).sec (CatModel.code A)⦄ :=
  rfl

/-- `Ā → B` is stable under substitution. -/
recall ComprehensionCategory.OverCat.funTwist_pull {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    (A B : Γ ⥤ Cat.{v, v}) :
    (funTwist A B)⦃σ⦄ = funTwist (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B)

/-- **The bijection is natural in `Γ`**: application is stable under substitution. -/
recall ComprehensionCategory.OverCat.funTwistEquiv_pull {Γ Δ : Cat.{v + 1, v + 1}} (σ : Δ ⟶ Γ)
    {A B : Γ ⥤ Cat.{v, v}} (t : Tm(Γ, funTwist A B)) :
    funTwistEquiv (σ.toFunctor ⋙ A) (σ.toFunctor ⋙ B) (t⦃σ⦄.castTy (funTwist_pull σ A B)) =
      (funTwistEquiv A B t)⦃𝐪(σ, CatModel.lift A)⦄

end FunTwist

section HomElim

variable {Γ : Cat.{u, u}} {A : ICatLax.{u, u}.Ty Γ} {X : ICatLax.{u, u}.Ty (Γ ▹ A)}

/-- **Hom-Elim**: a term of the motive in context `Γ ▹ b : A ▹ a : A ▹ f : Homₐ(ā, b) ▹ x : X`. -/
recall ComprehensionCategory.OverCat.homElim (D : ICatLax.{u, u}.Ty (elimCtx A X))
    (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : Tm(elimCtx A X, D)

/-- The context of the motive extends the twisted Hom-type, in the displayed model. -/
example : homCtx A = (Γ ▹ A ▹ A⦃𝐩 A⦄ ▹ twist (homFunctor A) : Cat.{u, u}) :=
  rfl

/-- The premise is a term of `D[ā/a, a/b, refl_a/f]`: `r` is the substitution `reflSec A`,
`(γ, a) ↦ (γ, a, a, 𝟙 a)`, extended by `x`, and `reflSec A` the extension of the diagonal by
`refl A`. -/
recall ComprehensionCategory.OverCat.homR_eq (A : ICatLax.{u, u}.Ty Γ)
    (X : ICatLax.{u, u}.Ty (Γ ▹ A)) : homR A X = 𝐪(reflSec A, X⦃homDom A⦄)

recall ComprehensionCategory.OverCat.reflSec_eq (A : ICatLax.{u, u}.Ty Γ) :
    reflSec A = consSec (diag A) ((refl A).castTy (twistedHom_eq A))

/-- **Hom-Comp**: `j(refl_a, x, d) ≡ d`. -/
recall ComprehensionCategory.OverCat.homElim_pull_homR (D : ICatLax.{u, u}.Ty (elimCtx A X))
    (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : (homElim D d)⦃homR A X⦄ = d

/-- **Hom-Elim is stable under substitution**, along `σ⁺ = elimCtxMap σ A X`, the morphism of the
comprehension structures. -/
recall ComprehensionCategory.OverCat.homElim_pull {Γ Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    {A : ICatLax.{u, u}.Ty Γ} {X : ICatLax.{u, u}.Ty (Γ ▹ A)}
    (D : ICatLax.{u, u}.Ty (elimCtx A X)) (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) :
    (homElim D d)⦃elimCtxMap σ A X⦄ =
      homElim (D⦃elimCtxMap σ A X⦄) (homElimPremisePull σ D d)

recall ComprehensionCategory.OverCat.elimCtxMap_eq {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    (A : ICatLax.{u, u}.Ty Γ) (X : ICatLax.{u, u}.Ty (Γ ▹ A)) :
    elimCtxMap σ A X = 𝐪(homCtxMap σ A, X⦃homDom A⦄)

recall ComprehensionCategory.OverCat.homCtxMap_eq {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ)
    (A : ICatLax.{u, u}.Ty Γ) :
    homCtxMap σ A = 𝐪(𝐪(𝐪(σ, A), A⦃𝐩 A⦄), twist (homFunctor A))

/-- The substituted premise is `d⦃𝐪(𝐪(σ, A), X)⦄`, with no transport. -/
example {Δ : Cat.{u, u}} (σ : Δ ⟶ Γ) (D : ICatLax.{u, u}.Ty (elimCtx A X))
    (d : Tm(Γ ▹ A ▹ X, D⦃homR A X⦄)) : homElimPremisePull σ D d = d⦃𝐪(𝐪(σ, A), X)⦄ :=
  rfl

end HomElim

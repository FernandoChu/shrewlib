import ComprehensionCategory.Basic
import ComprehensionCategory.Map
import ComprehensionCategory.Term
import ComprehensionCategory.TypeFormers.Sigma
import ComprehensionCategory.TypeFormers.Universe
import ComprehensionCategory.Model.Codomain.Readme
import ComprehensionCategory.Model.OverCat.Readme

/-!
# Comprehension categories

Comprehension categories as displayed categories, their type formers, and models of them.

* `Basic`: comprehension categories (`Comprehension D` on a fibration `[Fib D]`,
  `FullComprehension`, `SplitComprehension`), context extension, and the notation
  `D.Ty Γ`, `Γ ▹ A`, `A⦃σ⦄`, `𝐩 A`, `𝐪(σ, A)`.
* `Term`: the terms `Tm(Γ, A)` of a type, the sections of its projection, and their
  substitution `t⦃σ⦄ : Tm(Δ, A⦃σ⦄)`, the unique section over `t` along `𝐪(σ, A)`, functorial
  over a split comprehension category.
* `Map`: maps of comprehension categories over a functor of the bases, with a comparison
  `F.obj (Γ ▹ A) ⟶ F.obj Γ ▹ M.obj A`, and their pseudo and strict versions.
* `TypeFormers/`: what it means to have a (strict) type former.
  * `Sigma`: Σ-types `Σ[A] B`, with `Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B`, and their strict preservation by
    strict maps (`StrictComprehensionMap.PreservesSigma`).
  * `Universe`: Coquand-style universes `univ M Γ` in `D` of the types of `E`, along a strict map
    `M : E ⟶ D` over the identity: inverse maps `El M : Tm(Γ, univ M Γ) → E.Ty Γ` and `code M`,
    natural in `Γ`.
* `Model/`: comprehension categories, with a `Readme.lean` in each folder.
  * `Codomain/`: `cod C`, for a category with chosen pullbacks.
  * `OverCat/`: the models over `Cat`, one folder each, whose `TypeFormers/` folders mirror the one
    above, with type formers specific to them:
    * `Cat/`: the category model `ICat`, with Σ-types, opposite types and a Coquand-style
      universe of the types of a lower level (`SmallICat`).
    * `Discrete/`: the discrete model `IDisc`, the full sub-comprehension category of the category
      model on the functors into discrete categories, with Σ-types and opposite types, and its
      types of a lower level (`SmallIDisc`).
    * `Displayed/`: the displayed category model `LaxNormalCat`, whose types are the lax normal
      functors into profunctors, with the equivalence `LaxNormalCat ≃ cod Cat` as comprehension
      functor: a split replacement of `cod Cat`, with Σ-types.
    * `Shared/`: type formers relating the models: the Hom-types of the category model, types of
      the discrete model, and the universe of discrete types in the category model.
    * `Maps/`: maps between the models: forgetting the discreteness, a strict map preserving
      Σ-types and opposite types, and the lifts of the types of a lower level.

-/

universe v u v₂ u₂

open CategoryTheory Limits Displayed

open scoped Displayed

/-! ## Examples -/

/-- Substitution squares are pullbacks. -/
recall Displayed.isPullback_q {C : Type u} [Category.{v} C] (D : Displayed.{v, u, v₂, u₂} C)
    [Fib D] [Comprehension D] {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) :
    IsPullback 𝐪(σ, A) 𝐩 A⦃σ⦄ (𝐩 A) σ

/-- Σ-types are stable under substitution. -/
recall Displayed.pull_sigma {C : Type u} [Category.{v} C] (D : Displayed.{v, u, v₂, u₂} C)
    [Fib D] [Comprehension D] [PreSigma D] {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ)
    (B : D.Ty (Γ ▹ A)) : (Σ[A] B)⦃σ⦄ = Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄

/-- Substitution of a term is the unique section over it along `𝐪(σ, A)`. -/
recall Displayed.Tm.pull_unique {C : Type u} [Category.{v} C] {D : Displayed.{v, u, v₂, u₂} C}
    [Fib D] [Comprehension D] {Δ Γ : C} (σ : Δ ⟶ Γ) {A : D.Ty Γ} (t : Tm(Γ, A))
    (s : Tm(Δ, A⦃σ⦄)) (h : s.sec ≫ 𝐪(σ, A) = σ ≫ t.sec) : s = t⦃σ⦄

/-- Over a split fibration, substitution commutes with weakening. -/
recall Displayed.pull_q_pull_proj {C : Type u} [Category.{v} C] (D : Displayed.{v, u, v₂, u₂} C)
    [PreSplitFib D] [Comprehension D] {Δ Γ : C} (σ : Δ ⟶ Γ) (B A : D.Ty Γ) :
    A⦃𝐩 B⦄⦃𝐪(σ, B)⦄ = A⦃σ⦄⦃𝐩 B⦃σ⦄⦄

/-- Substitution of terms is written like that of types, and is functorial over a split
comprehension category. -/
recall Displayed.Tm.pull_comp {C : Type u} [Category.{v} C] {D : Displayed.{v, u, v₂, u₂} C}
    [SplitComprehension D] {Γ : C} {A : D.Ty Γ} {Δ Θ : C} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ)
    (t : Tm(Γ, A)) : t⦃τ ≫ σ⦄ = t⦃σ⦄⦃τ⦄

/-- A universe classifies the types of `E`, naturally. -/
recall Displayed.code_pull {C : Type u} [Category.{v} C] {D : Displayed.{v, u, v₂, u₂} C}
    {E : Displayed.{v, u, v₂, u₂} C} [Fib D] [Comprehension D] [Fib E] [Comprehension E]
    (M : StrictComprehensionMap (𝟭 C) E D) [HasUniverse M] {Δ Γ : C} (σ : Δ ⟶ Γ)
    (A : E.Ty Γ) : (code M A)⦃σ⦄ = code M A⦃σ⦄

import ComprehensionCategory.Basic
import ComprehensionCategory.Map
import ComprehensionCategory.TypeFormers.Sigma
import ComprehensionCategory.Model.Cat.Readme
import ComprehensionCategory.Model.Codomain.Readme

/-!
# Comprehension categories

Comprehension categories as displayed categories, their type formers, and models of them.

* `Basic`: comprehension categories (`Comprehension D` on a fibration `[Fib D]`,
  `FullComprehension`, `SplitComprehension`), context extension, and the notation
  `D.Ty Γ`, `Γ ▹ A`, `A⦃σ⦄`, `𝐩 A`, `𝐪(σ, A)`.
* `Map`: maps of comprehension categories over a functor of the bases, with a comparison
  `F.obj (Γ ▹ A) ⟶ F.obj Γ ▹ M.obj A`, and their pseudo and strict versions.
* `TypeFormers/`: what it means to have a (strict) type former.
  * `Sigma`: Σ-types `Σ[A] B`, with `Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B`.
* `Model/`: comprehension categories, one folder each, with a `Readme.lean`. Their
  `TypeFormers/` folders mirror the one above.
  * `Cat/`: the category model `ICat` over `Cat`, with Σ-types.
  * `Codomain/`: `cod C`, for a category with chosen pullbacks.

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

import ComprehensionCategory.Basic

/-!
# Σ-types in a comprehension category

A comprehension category has (split) *Σ-types* if for every type `A : D.Ty Γ` and type
`B : D.Ty (Γ ▹ A)` there is a type `Σ[A] B : D.Ty Γ`, with an isomorphism of contexts

```
  pair : Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B
```

over `Γ` (`pair ≫ 𝐩 (Σ[A] B) = 𝐩 B ≫ 𝐩 A`), and both are stable under substitution on the nose:
for `σ : Δ ⟶ Γ`, `(Σ[A] B)⦃σ⦄ = Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄`, and `pair` commutes with the morphisms `𝐪`
over `σ`. In a full comprehension category this makes `Σ[A]` a left adjoint to weakening along
`𝐩 A`, whose counit `Γ ▹ A ▹ B ⟶ Γ ▹ Σ[A] B` is invertible: Jacobs' strong coproducts.

The notion is meant for full split comprehension categories, `[SplitComprehension D]
[FullComprehension D]`, but it is stated over any comprehension category, `[Fib D]
[Comprehension D]`.

As for `PreSplitFib` and `SplitFib`, it comes in two classes:

* `PreSigma D`: the type former and its stability, `(Σ[A] B)⦃σ⦄ = Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄`, which is
  a rewrite rule;
* `HasSigma D`: the isomorphisms `pair`, over `Γ` and stable under substitution. The `PreSigma D`
  is an instance field, so that the rule applies to the stability of `pair`, whose two sides lie
  over `(Σ[A] B)⦃σ⦄` and `Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄`.

The notation `Σ[A] B` for `D.sigma A B` is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`.
-/

universe v u v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- Σ-type formers on a comprehension category, stable under substitution on the nose. The
stability is a rewrite rule. It is stated with `Fib.pull`, on which the rules for substitution are
keyed, rather than with `D.pull`, for which `pull_sigma` below is the rule. -/
class PreSigma (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] where
  /-- The Σ-type `Σ[A] B` in context `Γ` of `B` in context `Γ ▹ A`. -/
  sigma : ∀ {Γ : C} (A : D.Ty Γ), D.Ty (Γ ▹ A) → D.Ty Γ
  /-- Stability under substitution: `(Σ[A] B)⦃σ⦄ = Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄`. -/
  pull_sigma : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)),
    Fib.pull σ (sigma A B) = sigma (Fib.pull σ A) (Fib.pull 𝐪(σ, A) B)

attribute [rewrite_rule] PreSigma.pull_sigma

section

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] [PreSigma D]

/-- The Σ-type `Σ[A] B` of `B` in context `Γ ▹ A`. -/
@[reducible] def sigma {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)) : D.Ty Γ :=
  PreSigma.sigma A B

/-- `Σ[A] B` is the Σ-type `D.sigma A B` of `B` in context `Γ ▹ A`. -/
scoped notation:max "Σ[" A "] " B:max => Displayed.sigma _ A B

/-- Displays `D.sigma A B` as `Σ[A] B`. -/
@[scoped app_unexpander Displayed.sigma]
def unexpandSigma : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $A $B) => `(Σ[$A] $B)
  | _ => throw ()

@[rewrite_rule]
theorem pull_sigma {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)) :
    (Σ[A] B)⦃σ⦄ = Σ[A⦃σ⦄] B⦃𝐪(σ, A)⦄ :=
  PreSigma.pull_sigma σ A B

end

/-- Σ-types on a comprehension category: Σ-type formers with isomorphisms of contexts
`Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B` over `Γ`, stable under substitution. -/
class HasSigma (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] where
  /-- The underlying Σ-type formers. -/
  [toPreSigma : PreSigma D]
  /-- The pairing isomorphism `Γ ▹ A ▹ B ⟶ Γ ▹ Σ[A] B`. -/
  pair : ∀ {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)), Γ ▹ A ▹ B ⟶ Γ ▹ Σ[A] B
  /-- Its inverse `Γ ▹ Σ[A] B ⟶ Γ ▹ A ▹ B`. -/
  unpair : ∀ {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)), Γ ▹ Σ[A] B ⟶ Γ ▹ A ▹ B
  pair_unpair : ∀ {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)), pair A B ≫ unpair A B = 𝟙 _
  unpair_pair : ∀ {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)), unpair A B ≫ pair A B = 𝟙 _
  /-- `pair` lies over `Γ`. -/
  pair_proj : ∀ {Γ : C} (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)), pair A B ≫ 𝐩 (Σ[A] B) = 𝐩 B ≫ 𝐩 A
  /-- `pair` is stable under substitution: it commutes with the morphisms `𝐪` over `σ`. -/
  pair_q : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) (B : D.Ty (Γ ▹ A)),
    pair A⦃σ⦄ B⦃𝐪(σ, A)⦄ ≫ 𝐪(σ, Σ[A] B) = 𝐪(𝐪(σ, A), B) ≫ pair A B

attribute [instance_reducible, instance] HasSigma.toPreSigma

section

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [Comprehension D] [HasSigma D] {Γ : C}
  (A : D.Ty Γ) (B : D.Ty (Γ ▹ A))

/-- The isomorphism of contexts `Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B`. -/
def sigmaIso : Γ ▹ A ▹ B ≅ Γ ▹ Σ[A] B where
  hom := HasSigma.pair A B
  inv := HasSigma.unpair A B
  hom_inv_id := HasSigma.pair_unpair A B
  inv_hom_id := HasSigma.unpair_pair A B

theorem sigmaIso_hom_proj : (D.sigmaIso A B).hom ≫ 𝐩 (Σ[A] B) = 𝐩 B ≫ 𝐩 A :=
  HasSigma.pair_proj A B

theorem sigmaIso_inv_proj : (D.sigmaIso A B).inv ≫ 𝐩 B ≫ 𝐩 A = 𝐩 (Σ[A] B) := by
  rw [← sigmaIso_hom_proj, Iso.inv_hom_id_assoc]

theorem sigmaIso_hom_q {Δ : C} (σ : Δ ⟶ Γ) :
    (D.sigmaIso A⦃σ⦄ B⦃𝐪(σ, A)⦄).hom ≫ 𝐪(σ, Σ[A] B) = 𝐪(𝐪(σ, A), B) ≫ (D.sigmaIso A B).hom :=
  HasSigma.pair_q σ A B

end

end Displayed

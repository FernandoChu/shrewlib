import ComprehensionCategory.TypeFormers.Op

/-!
# Hom-types in a comprehension category

A comprehension category with opposite types has (split) *Hom-types* if every type `A : D.Ty Γ` has
a type of morphisms from `a : Aᵒᵖ` to `b : A`, in the context extended by both:

```
                 Γ ⊢ A type
  ------------------------------------------- Hom-Form
    Γ ▹ a : Aᵒᵖ ▹ b : A ⊢ Homₐ(a, b) type

                 Γ ⊢ A type
  ------------------------------------------- Hom-op
    Γ ▹ a : Aᵒᵖ ▹ b : A ⊢ Homₐ(a, b)ᵒᵖ ≡ Homₐ(a, b) type
```

Here `b : A` is in context `Γ ▹ Aᵒᵖ`, so it is the weakening `A⦃𝐩 Aᵒᵖ⦄`, and the Hom-type is
`Hom[A] : D.Ty (Γ ▹ Aᵒᵖ ▹ A⦃𝐩 Aᵒᵖ⦄)`. It is stable under substitution on the nose: for
`σ : Δ ⟶ Γ`, the substitution of `Hom[A]` along the morphism
`𝐪(𝐪(σ, Aᵒᵖ), A⦃𝐩 Aᵒᵖ⦄) : Δ ▹ Aᵒᵖ⦃σ⦄ ▹ A⦃𝐩 Aᵒᵖ⦄⦃𝐪(σ, Aᵒᵖ)⦄ ⟶ Γ ▹ Aᵒᵖ ▹ A⦃𝐩 Aᵒᵖ⦄`
is `Hom[A⦃σ⦄]`. Both Hom-op and the stability are rewrite rules.

The stability is well typed as a plain equation since the two contexts agree: `Aᵒᵖ⦃σ⦄` is
`A⦃σ⦄ᵒᵖ` by `pull_op`, and `A⦃𝐩 Aᵒᵖ⦄⦃𝐪(σ, Aᵒᵖ)⦄` is `A⦃σ⦄⦃𝐩 A⦃σ⦄ᵒᵖ⦄` by the rule that substitution
commutes with weakening (`pull_q_pull_proj`), which holds over a split fibration. So `HasHom D` is
stated over `[PreSplitFib D] [Comprehension D] [HasOp D]`.

The rules are confluent at `(Hom[A]ᵒᵖ)⦃τ⦄` and `(Hom[A]ᵒᵖ)ᵒᵖ`, where Hom-op commutes with `pull_op`
and `op_op`.

The notation `Hom[A]` for `D.hom A` is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`.
-/

universe v u v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- Hom-types on a split comprehension category with opposite types, stable under substitution
on the nose. Hom-op and the stability are rewrite rules. The stability is stated with `Fib.pull`,
on which the rules for substitution are keyed, rather than with `D.pull`, for which `pull_hom`
below is the rule. -/
class HasHom (D : Displayed.{v, u, v₂, u₂} C) [PreSplitFib D] [Comprehension D] [HasOp D] where
  /-- The Hom-type of `A`, from `a : Aᵒᵖ` to `b : A` (Hom-Form). -/
  hom : ∀ {Γ : C} (A : D.Ty Γ), D.Ty (Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄)
  /-- The Hom-type is its own opposite (Hom-op). -/
  op_hom : ∀ {Γ : C} (A : D.Ty Γ), (hom A)ᵒᵖ = hom A
  /-- Stability under substitution: `Hom[A]⦃𝐪(𝐪(σ, Aᵒᵖ), A⦃𝐩 Aᵒᵖ⦄)⦄ = Hom[A⦃σ⦄]`. -/
  pull_hom : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ),
    Fib.pull 𝐪(𝐪(σ, Aᵒᵖ), A⦃𝐩 (Aᵒᵖ)⦄) (hom A) = hom (A⦃σ⦄)

attribute [rewrite_rule] HasHom.op_hom HasHom.pull_hom

section

variable (D : Displayed.{v, u, v₂, u₂} C) [PreSplitFib D] [Comprehension D] [HasOp D] [HasHom D]

/-- The Hom-type `Hom[A]` of `A`, from `a : Aᵒᵖ` to `b : A`. -/
@[reducible] def hom {Γ : C} (A : D.Ty Γ) : D.Ty (Γ ▹ Aᵒᵖ ▹ A⦃𝐩 (Aᵒᵖ)⦄) :=
  HasHom.hom A

/-- `Hom[A]` is the Hom-type `D.hom A` of `A`. -/
scoped notation:max "Hom[" A "]" => Displayed.hom _ A

/-- Displays `D.hom A` as `Hom[A]`. -/
@[scoped app_unexpander Displayed.hom]
def unexpandHom : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $A) => `(Hom[$A])
  | _ => throw ()

/-- **Hom-op**: the Hom-type is its own opposite. -/
@[rewrite_rule]
theorem op_hom {Γ : C} (A : D.Ty Γ) : Hom[A]ᵒᵖ = Hom[A] :=
  HasHom.op_hom A

@[rewrite_rule]
theorem pull_hom {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) :
    Hom[A]⦃𝐪(𝐪(σ, Aᵒᵖ), A⦃𝐩 (Aᵒᵖ)⦄)⦄ = Hom[A⦃σ⦄] :=
  HasHom.pull_hom σ A

end

end Displayed

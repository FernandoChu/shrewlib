import ComprehensionCategory.Basic

/-!
# Opposite types in a comprehension category

A comprehension category has (split) *opposite types* if every type `A : D.Ty Γ` has an opposite
`Aᵒᵖ : D.Ty Γ`, which is involutive and stable under substitution on the nose:

```
      Γ ⊢ A type                    Γ ⊢ A type
  ------------------ op-Form   ---------------------- op-Inv
    Γ ⊢ Aᵒᵖ type                Γ ⊢ (Aᵒᵖ)ᵒᵖ ≡ A type
```

and `(Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ` for `σ : Δ ⟶ Γ`. Both equations are rewrite rules, so that they hold
definitionally, as judgmental equalities. They form a critical pair at `((Aᵒᵖ)ᵒᵖ)⦃σ⦄`, which both
rewrite to `A⦃σ⦄`.

Unlike Σ-types, opposite types do not involve context extension, so `HasOp D` is stated over any
cloven fibration `[Fib D]`; in a comprehension category, it gives the extended contexts `Γ ▹ Aᵒᵖ`.

The notation `Aᵒᵖ` for `D.op A` is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`. It overloads Mathlib's `Cᵒᵖ` for opposite categories, which is
chosen when `A` is a type rather than a type of `D`.
-/

universe v u v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- Opposite types on a cloven fibration, involutive and stable under substitution on the nose.
Both equations are rewrite rules. Stability is stated with `Fib.pull`, on which the rules for
substitution are keyed, rather than with `D.pull`, for which `pull_op` below is the rule. -/
class HasOp (D : Displayed.{v, u, v₂, u₂} C) [Fib D] where
  /-- The opposite `Aᵒᵖ` of a type `A` (op-Form). -/
  op : ∀ {Γ : C}, D.Ty Γ → D.Ty Γ
  /-- The opposite is involutive, `(Aᵒᵖ)ᵒᵖ = A` (op-Inv). -/
  op_op : ∀ {Γ : C} (A : D.Ty Γ), op (op A) = A
  /-- Stability under substitution: `(Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ`. -/
  pull_op : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ), Fib.pull σ (op A) = op (Fib.pull σ A)

attribute [rewrite_rule] HasOp.op_op HasOp.pull_op

section

variable (D : Displayed.{v, u, v₂, u₂} C) [Fib D] [HasOp D]

/-- The opposite `Aᵒᵖ` of the type `A`. -/
@[reducible] def op {Γ : C} (A : D.Ty Γ) : D.Ty Γ :=
  HasOp.op A

/-- `Aᵒᵖ` is the opposite type `D.op A`. -/
scoped notation:max A:max "ᵒᵖ" => Displayed.op _ A

/-- Displays `D.op A` as `Aᵒᵖ`. -/
@[scoped app_unexpander Displayed.op]
def unexpandOp : Lean.PrettyPrinter.Unexpander
  | `($_ $_ $A) => `($Aᵒᵖ)
  | _ => throw ()

/-- **op-Inv**: the opposite is involutive. -/
@[rewrite_rule]
theorem op_op {Γ : C} (A : D.Ty Γ) : (Aᵒᵖ)ᵒᵖ = A :=
  HasOp.op_op A

@[rewrite_rule]
theorem pull_op {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) : (Aᵒᵖ)⦃σ⦄ = A⦃σ⦄ᵒᵖ :=
  HasOp.pull_op σ A

end

end Displayed

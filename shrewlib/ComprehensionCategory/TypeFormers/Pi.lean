import ComprehensionCategory.Map
import ComprehensionCategory.Term

/-!
# Π-types in a comprehension category

Let `D` and `E` be comprehension categories over the same base `C`. `E` has (split) *Π-types over
`D`* if for every type `A : D.Ty Γ` and type `B : E.Ty (Γ ▹ A)` of `E` in the context extended by
`A` in `D`, there is a type `Π[A] B : E.Ty Γ`, whose terms are those of `B`:

```
  lam : Tm(Γ ▹ A, B) ≃ Tm(Γ, Π[A] B) : app
```

and both are stable under substitution on the nose: for `σ : Δ ⟶ Γ`,
`(Π[A] B)⦃σ⦄ = Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄`, and `(lam t)⦃σ⦄ = lam t⦃𝐪(σ, A)⦄` (and so `app`, `app_pull`).
These are mixed Π-types: the domain `A` is a type of `D` and the codomain `B` a type of `E`, so
that the category model has Π-types over the contravariant category model, whose types are its
domains (`OverCat/Shared/Pi`). The usual Π-types are those of `E` over itself.

As for Σ-types, it comes in two classes:

* `PrePi D E`: the type former and its stability, `(Π[A] B)⦃σ⦄ = Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄`, a rewrite
  rule;
* `HasPi D E`: the inverse maps `lam` and `app`, with `lam` stable under substitution. The
  `PrePi D E` is an instance field, so that the rule applies to the stability of `lam`, whose two
  sides are terms of `(Π[A] B)⦃σ⦄` and `Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄`.

The notation `Π[A] B` for `pi A B` is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`.
-/

universe v u v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- Π-type formers of `E` over `D`, stable under substitution on the nose. The stability is a
rewrite rule, stated with `Fib.pull`, on which the rules for substitution are keyed; `pull_pi`
below is the rule for `E.pull`. -/
class PrePi (D : Displayed.{v₂, u₂} C) (E : Displayed.{v₃, u₃} C) [Fib D] [Comprehension D]
    [Fib E] [Comprehension E] where
  /-- The Π-type `Π[A] B` in context `Γ` of `B` in context `Γ ▹ A`. -/
  pi : ∀ {Γ : C} (A : D.Ty Γ), E.Ty (Γ ▹ A) → E.Ty Γ
  /-- Stability under substitution: `(Π[A] B)⦃σ⦄ = Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄`. -/
  pull_pi : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) (B : E.Ty (Γ ▹ A)),
    Fib.pull σ (pi A B) = pi (Fib.pull σ A) (Fib.pull 𝐪(σ, A) B)

attribute [rewrite_rule] PrePi.pull_pi

section

variable {D : Displayed.{v₂, u₂} C} {E : Displayed.{v₃, u₃} C} [Fib D] [Comprehension D]
  [Fib E] [Comprehension E] [PrePi D E]

/-- The Π-type `Π[A] B` of `B` in context `Γ ▹ A`. -/
@[reducible] def pi {Γ : C} (A : D.Ty Γ) (B : E.Ty (Γ ▹ A)) : E.Ty Γ :=
  PrePi.pi A B

/-- `Π[A] B` is the Π-type `pi A B` of `B` in context `Γ ▹ A`. -/
scoped notation:max "Π[" A "] " B:max => Displayed.pi A B

/-- Displays `pi A B` as `Π[A] B`. -/
@[scoped app_unexpander Displayed.pi]
def unexpandPi : Lean.PrettyPrinter.Unexpander
  | `($_ $A $B) => `(Π[$A] $B)
  | _ => throw ()

/-- **The Π-types are stable under substitution.** -/
@[rewrite_rule]
theorem pull_pi {Δ Γ : C} (σ : Δ ⟶ Γ) (A : D.Ty Γ) (B : E.Ty (Γ ▹ A)) :
    (Π[A] B)⦃σ⦄ = Π[A⦃σ⦄] B⦃𝐪(σ, A)⦄ :=
  PrePi.pull_pi σ A B

end

/-- Π-types of `E` over `D`: Π-type formers with inverse maps `lam` and `app` between the terms of
`B` and those of `Π[A] B`, with `lam` stable under substitution. -/
class HasPi (D : Displayed.{v₂, u₂} C) (E : Displayed.{v₃, u₃} C) [Fib D] [Comprehension D]
    [Fib E] [Comprehension E] where
  /-- The underlying Π-type formers. -/
  [toPrePi : PrePi D E]
  /-- Abstraction. -/
  lam : ∀ {Γ : C} {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)}, Tm(Γ ▹ A, B) → Tm(Γ, Π[A] B)
  /-- Application. -/
  app : ∀ {Γ : C} {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)}, Tm(Γ, Π[A] B) → Tm(Γ ▹ A, B)
  app_lam : ∀ {Γ : C} {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)} (t : Tm(Γ ▹ A, B)), app (lam t) = t
  lam_app : ∀ {Γ : C} {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)} (t : Tm(Γ, Π[A] B)), lam (app t) = t
  /-- `lam` is stable under substitution. -/
  lam_pull : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)} (t : Tm(Γ ▹ A, B)),
    (lam t)⦃σ⦄ = lam t⦃𝐪(σ, A)⦄

attribute [instance_reducible, instance] HasPi.toPrePi

section

variable {D : Displayed.{v₂, u₂} C} {E : Displayed.{v₃, u₃} C} [Fib D] [Comprehension D]
  [Fib E] [Comprehension E] [HasPi D E] {Δ Γ : C} {A : D.Ty Γ} {B : E.Ty (Γ ▹ A)}

/-- **Abstraction**: a term of `B` in context `Γ ▹ A` as a term of `Π[A] B`. -/
def lam (t : Tm(Γ ▹ A, B)) : Tm(Γ, Π[A] B) :=
  HasPi.lam t

/-- **Application**: a term of `Π[A] B` as a term of `B` in context `Γ ▹ A`. -/
def app (t : Tm(Γ, Π[A] B)) : Tm(Γ ▹ A, B) :=
  HasPi.app t

/-- β: application undoes abstraction. -/
theorem app_lam (t : Tm(Γ ▹ A, B)) : app (lam t) = t :=
  HasPi.app_lam t

/-- η: abstraction undoes application. -/
theorem lam_app (t : Tm(Γ, Π[A] B)) : lam (app t) = t :=
  HasPi.lam_app t

/-- The terms of `B` in context `Γ ▹ A` are those of `Π[A] B`. -/
def lamEquiv : Tm(Γ ▹ A, B) ≃ Tm(Γ, Π[A] B) where
  toFun := lam
  invFun := app
  left_inv := app_lam
  right_inv := lam_app

/-- **Abstraction is stable under substitution.** -/
theorem lam_pull (σ : Δ ⟶ Γ) (t : Tm(Γ ▹ A, B)) : (lam t)⦃σ⦄ = lam t⦃𝐪(σ, A)⦄ :=
  HasPi.lam_pull σ t

/-- **Application is stable under substitution.** -/
theorem app_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, Π[A] B)) : app t⦃σ⦄ = (app t)⦃𝐪(σ, A)⦄ :=
  (congrArg app ((congrArg (·⦃σ⦄) (lam_app t).symm).trans (lam_pull σ (app t)))).trans
    (app_lam _)

end

end Displayed

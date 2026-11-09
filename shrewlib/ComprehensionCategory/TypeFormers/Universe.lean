import ComprehensionCategory.Map
import ComprehensionCategory.Term

/-!
# Universes in a comprehension category

Let `D` and `E` be comprehension categories over the same base `C`. `D` has a (Coquand-style)
*universe of the types of `E`* if there is a type `univ D E Γ` of `D` in every context `Γ`, stable
under substitution on the nose, whose terms are exactly the types of `E`: there are inverse maps

```
  El D E : Tm(Γ, univ D E Γ) → E.Ty Γ        code D E : E.Ty Γ → Tm(Γ, univ D E Γ)
```

natural in `Γ`, `El D E t⦃σ⦄ = (El D E t)⦃σ⦄` (and so `code D E`, `code_pull`).

The types of `E` are types of another comprehension category `D'` along a strict map
`M : E ⟶ D'` over the identity: a term `t` of the universe decodes to the type
`decode M t = M.obj (El D E t)` of `D'`, which has the same context extension and projection as
`El D E t`, since `M` is strict (`ext_decode`, `proj_decode`). In Coquand's formulation, `E` is the
types of a lower level, and `M` their inclusion into the types of `D`, which makes the hierarchy
cumulative. But `D'` need not be `D`: the category model has a universe of the contravariant types,
which are types of the contravariant category model, not of the category model.

As for Σ-types, it comes in two classes:

* `PreUniverse D E`: the universe and its stability, `(univ D E Γ)⦃σ⦄ = univ D E Δ`, a rewrite
  rule;
* `HasUniverse D E`: the maps `El` and `code`. The `PreUniverse D E` is an instance field, so that
  the rule applies to the naturality of `El`, which applies `El` to
  `t⦃σ⦄ : Tm(Δ, (univ D E Γ)⦃σ⦄)`.

The classes are indexed by `D` and `E`, so that `D` can have universes of the types of several
comprehension categories.
-/

universe v u v₂ u₂ v₃ u₃ v₄ u₄

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- A universe in `D` for the types of `E`: a type `univ Γ` of `D` in every context, stable under
substitution on the nose. The stability is a rewrite rule, stated with `Fib.pull`, on which the
rules for substitution are keyed; `pull_univ` below is the rule for `D.pull`. -/
class PreUniverse (D : Displayed.{v₂, u₂} C) (E : Displayed.{v₃, u₃} C) [Fib D]
    [Comprehension D] where
  /-- The universe in context `Γ`. -/
  univ : ∀ Γ : C, D.Ty Γ
  /-- The universe is closed: `(univ Γ)⦃σ⦄ = univ Δ`. -/
  pull_univ : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ), Fib.pull σ (univ Γ) = univ Δ

attribute [rewrite_rule] PreUniverse.pull_univ

variable (D : Displayed.{v₂, u₂} C) (E : Displayed.{v₃, u₃} C) [Fib D] [Comprehension D]

section

variable [PreUniverse D E]

/-- The universe in `D` of the types of `E`, in context `Γ`. -/
@[reducible] def univ (Γ : C) : D.Ty Γ :=
  PreUniverse.univ E Γ

/-- **The universe is closed**: it is stable under substitution. -/
@[rewrite_rule]
theorem pull_univ {Δ Γ : C} (σ : Δ ⟶ Γ) : (univ D E Γ)⦃σ⦄ = univ D E Δ :=
  PreUniverse.pull_univ σ

end

/-- A Coquand-style universe in `D` of the types of `E`: a closed type `univ D E Γ` of `D` whose
terms are the types of `E`, by inverse maps `El` and `code`, natural in `Γ`. -/
class HasUniverse (D : Displayed.{v₂, u₂} C) (E : Displayed.{v₃, u₃} C) [Fib D]
    [Comprehension D] [Fib E] [Comprehension E] where
  /-- The underlying universe. -/
  [toPreUniverse : PreUniverse D E]
  /-- The type of `E` decoded from a term of the universe. -/
  El : ∀ {Γ : C}, Tm(Γ, univ D E Γ) → E.Ty Γ
  /-- The code of a type of `E`, a term of the universe. -/
  code : ∀ {Γ : C}, E.Ty Γ → Tm(Γ, univ D E Γ)
  El_code : ∀ {Γ : C} (A : E.Ty Γ), El (code A) = A
  code_El : ∀ {Γ : C} (t : Tm(Γ, univ D E Γ)), code (El t) = t
  /-- `El` commutes with substitution. -/
  El_pull : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (t : Tm(Γ, univ D E Γ)), El t⦃σ⦄ = (El t)⦃σ⦄

attribute [instance_reducible, instance] HasUniverse.toPreUniverse

variable [Fib E] [Comprehension E]

section

variable [HasUniverse D E] {Δ Γ : C}

/-- The type of `E` decoded from a term `t` of the universe. -/
def El (t : Tm(Γ, univ D E Γ)) : E.Ty Γ :=
  HasUniverse.El t

/-- The code of a type `A` of `E`, a term of the universe. -/
def code (A : E.Ty Γ) : Tm(Γ, univ D E Γ) :=
  HasUniverse.code A

/-- `El` undoes `code`. -/
theorem El_code (A : E.Ty Γ) : El D E (code D E A) = A :=
  HasUniverse.El_code A

/-- `code` undoes `El`. -/
theorem code_El (t : Tm(Γ, univ D E Γ)) : code D E (El D E t) = t :=
  HasUniverse.code_El t

/-- `El` commutes with substitution. -/
theorem El_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, univ D E Γ)) : El D E t⦃σ⦄ = (El D E t)⦃σ⦄ :=
  HasUniverse.El_pull σ t

/-- `code` commutes with substitution. -/
theorem code_pull (σ : Δ ⟶ Γ) (A : E.Ty Γ) : (code D E A)⦃σ⦄ = code D E A⦃σ⦄ :=
  (code_El D E _).symm.trans
    (congrArg (code D E) ((El_pull D E σ (code D E A)).trans
      (congrArg (E.pull σ) (El_code D E A))))

variable {D E} {D' : Displayed.{v₄, u₄} C} [Fib D'] [Comprehension D']
  (M : StrictComprehensionMap (𝟭 C) E D')

/-- The type of `D'` decoded from a term `t` of the universe: the type `El D E t` of `E`, along a
strict map `M : E ⟶ D'`. -/
def decode (t : Tm(Γ, univ D E Γ)) : D'.Ty Γ :=
  M.toPre.obj (El D E t)

/-- The context extended by the decoded type is that extended by the type of `E`, since `M` is
strict. -/
theorem ext_decode (t : Tm(Γ, univ D E Γ)) : Γ ▹ decode M t = Γ ▹ El D E t :=
  rfl

theorem proj_decode (t : Tm(Γ, univ D E Γ)) : 𝐩 (decode M t) = 𝐩 (El D E t) :=
  rfl

end

end Displayed

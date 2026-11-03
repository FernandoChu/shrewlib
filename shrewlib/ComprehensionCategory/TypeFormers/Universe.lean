import ComprehensionCategory.Map
import ComprehensionCategory.Term

/-!
# Universes in a comprehension category

Let `D` and `E` be comprehension categories over the same base `C`, and `M : E ⟶ D` a strict map
of comprehension categories over the identity. `D` has a (Coquand-style) *universe of the types of
`E` along `M`* if there is a type `univ M Γ` of `D` in every context `Γ`, stable under substitution
on the nose, whose terms are exactly the types of `E`: there are inverse maps

```
  El M : Tm(Γ, univ M Γ) → E.Ty Γ        code M : E.Ty Γ → Tm(Γ, univ M Γ)
```

natural in `Γ`, `El M t⦃σ⦄ = (El M t)⦃σ⦄` (and so `code M`, `code_pull`). The types of `E` are
types of `D` along `M`: a term `t` of the universe decodes to the type `decode M t = M.obj (El M t)`
of `D`, which has the same context extension and projection as `El M t`, since `M` is strict
(`ext_decode`, `proj_decode`). In Coquand's formulation, `E` is the types of a lower level, and `M`
their inclusion into the types of `D`, which makes the hierarchy cumulative.

As for Σ-types, it comes in two classes:

* `PreUniverse M`: the universe and its stability, `(univ M Γ)⦃σ⦄ = univ M Δ`, a rewrite rule;
* `HasUniverse M`: the maps `El` and `code`. The `PreUniverse M` is an instance field, so that the
  rule applies to the naturality of `El`, which applies `El` to `t⦃σ⦄ : Tm(Δ, (univ M Γ)⦃σ⦄)`.

The classes are indexed by `M`, rather than by `D` and `E`, so that `D` can have universes of the
types of several comprehension categories.
-/

universe v u v₂ u₂ v₃ u₃

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C] {D : Displayed.{v, u, v₂, u₂} C}
  {E : Displayed.{v, u, v₃, u₃} C} [Fib D] [Comprehension D] [Fib E] [Comprehension E]

/-- A universe in `D` for the types of `E` along `M`: a type `univ Γ` of `D` in every context,
stable under substitution on the nose. The stability is a rewrite rule, stated with `Fib.pull`, on
which the rules for substitution are keyed; `pull_univ` below is the rule for `D.pull`. -/
class PreUniverse (M : StrictComprehensionMap (𝟭 C) E D) where
  /-- The universe in context `Γ`. -/
  univ : ∀ Γ : C, D.Ty Γ
  /-- The universe is closed: `(univ Γ)⦃σ⦄ = univ Δ`. -/
  pull_univ : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ), Fib.pull σ (univ Γ) = univ Δ

attribute [rewrite_rule] PreUniverse.pull_univ

variable (M : StrictComprehensionMap (𝟭 C) E D)

section

variable [PreUniverse M]

/-- The universe in `D` of the types of `E` along `M`, in context `Γ`. -/
@[reducible] def univ (Γ : C) : D.Ty Γ :=
  PreUniverse.univ M Γ

/-- **The universe is closed**: it is stable under substitution. -/
@[rewrite_rule]
theorem pull_univ {Δ Γ : C} (σ : Δ ⟶ Γ) : (univ M Γ)⦃σ⦄ = univ M Δ :=
  PreUniverse.pull_univ σ

end

/-- A Coquand-style universe in `D` of the types of `E` along `M`: a closed type `univ M Γ` of `D`
whose terms are the types of `E`, by inverse maps `El` and `code`, natural in `Γ`. -/
class HasUniverse (M : StrictComprehensionMap (𝟭 C) E D) where
  /-- The underlying universe. -/
  [toPreUniverse : PreUniverse M]
  /-- The type of `E` decoded from a term of the universe. -/
  El : ∀ {Γ : C}, Tm(Γ, univ M Γ) → E.Ty Γ
  /-- The code of a type of `E`, a term of the universe. -/
  code : ∀ {Γ : C}, E.Ty Γ → Tm(Γ, univ M Γ)
  El_code : ∀ {Γ : C} (A : E.Ty Γ), El (code A) = A
  code_El : ∀ {Γ : C} (t : Tm(Γ, univ M Γ)), code (El t) = t
  /-- `El` commutes with substitution. -/
  El_pull : ∀ {Δ Γ : C} (σ : Δ ⟶ Γ) (t : Tm(Γ, univ M Γ)), El t⦃σ⦄ = (El t)⦃σ⦄

attribute [instance_reducible, instance] HasUniverse.toPreUniverse

section

variable [HasUniverse M] {Δ Γ : C}

/-- The type of `E` decoded from a term `t` of the universe. -/
def El (t : Tm(Γ, univ M Γ)) : E.Ty Γ :=
  HasUniverse.El t

/-- The code of a type `A` of `E`, a term of the universe. -/
def code (A : E.Ty Γ) : Tm(Γ, univ M Γ) :=
  HasUniverse.code A

/-- `El` undoes `code`. -/
theorem El_code (A : E.Ty Γ) : El M (code M A) = A :=
  HasUniverse.El_code A

/-- `code` undoes `El`. -/
theorem code_El (t : Tm(Γ, univ M Γ)) : code M (El M t) = t :=
  HasUniverse.code_El t

/-- `El` commutes with substitution. -/
theorem El_pull (σ : Δ ⟶ Γ) (t : Tm(Γ, univ M Γ)) : El M t⦃σ⦄ = (El M t)⦃σ⦄ :=
  HasUniverse.El_pull σ t

/-- `code` commutes with substitution. -/
theorem code_pull (σ : Δ ⟶ Γ) (A : E.Ty Γ) : (code M A)⦃σ⦄ = code M A⦃σ⦄ :=
  (code_El M _).symm.trans
    (congrArg (code M) ((El_pull M σ (code M A)).trans (congrArg (E.pull σ) (El_code M A))))

/-- The type of `D` decoded from a term `t` of the universe: the type `El M t` of `E`, along `M`. -/
def decode (t : Tm(Γ, univ M Γ)) : D.Ty Γ :=
  M.toPre.obj (El M t)

/-- The context extended by the decoded type is that extended by the type of `E`, since `M` is
strict. -/
theorem ext_decode (t : Tm(Γ, univ M Γ)) : Γ ▹ decode M t = Γ ▹ El M t :=
  rfl

theorem proj_decode (t : Tm(Γ, univ M Γ)) : 𝐩 (decode M t) = 𝐩 (El M t) :=
  rfl

end

end Displayed

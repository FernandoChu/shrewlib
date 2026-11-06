import ComprehensionCategory.Basic

/-!
# Terms in a comprehension category

The terms of a type `A` in context `Γ`, `Tm(Γ, A)`, are the sections of its projection: the
morphisms `t.sec : Γ ⟶ Γ ▹ A` with `t.sec ≫ 𝐩 A = 𝟙 Γ`.

The substitution `t⦃σ⦄ : Tm(Δ, A⦃σ⦄)` of a term along `σ : Δ ⟶ Γ` (`Tm.pull`) is the
factorization of `σ ≫ t.sec` through the pullback square of `𝐪(σ, A)`: it is the unique section
`s` of `𝐩 A⦃σ⦄` with `s.sec ≫ 𝐪(σ, A) = σ ≫ t.sec` (`Tm.pull_sec_q`, `Tm.pull_unique`). The
factorization is given by the cartesian morphism of `cod C` that the comprehension functor sends
the chosen lift of `σ` at `A` to, as data, so that it computes. Over a split comprehension
category, substitution of terms is functorial (`Tm.pull_id`, `Tm.pull_comp`), as `𝐪(𝟙 Γ, A)` and
`𝐪(τ ≫ σ, A)` are `𝟙` and `𝐪(τ, A⦃σ⦄) ≫ 𝐪(σ, A)` by the rules for the chosen lifts.

The notation `Tm(Γ, A)` for `D.Tm A`, for `A` over `Γ`, is scoped in `Displayed`, with that of
`ComprehensionCategory/Basic`. As there, the comprehension category `D` is inferred from the type
of `A`. The notation `t⦃σ⦄` for `t.pull σ` is that of the substitution of types, `A⦃σ⦄`, whose
elaborator tells them apart by the type of `t`.
-/

universe v u v₂ u₂

open CategoryTheory

namespace Displayed

open scoped Displayed

variable {C : Type u} [Category.{v} C]

/-- The terms of the type `A` in context `Γ`: the sections of its projection `𝐩 A`. -/
@[ext]
structure Tm (D : Displayed.{v₂, u₂} C) [Fib D] [Comprehension D] {Γ : C} (A : D.Ty Γ) where
  /-- The section. -/
  sec : Γ ⟶ Γ ▹ A
  /-- It is a section of the projection. -/
  sec_proj : sec ≫ 𝐩 A = 𝟙 Γ

/-- `Tm(Γ, A)` is the type `D.Tm A` of the terms of the type `A` in context `Γ`. -/
scoped notation "Tm(" ctx ", " ty ")" => Displayed.Tm _ (Γ := ctx) ty

open Lean PrettyPrinter Delaborator SubExpr in
/-- Displays `D.Tm A`, for `A` over `Γ`, as `Tm(Γ, A)`. -/
@[scoped delab app.Displayed.Tm]
def delabTm : Delab := whenPPOption getPPNotation <| withOverApp 7 do
  let Γ ← withNaryArg 5 delab
  let A ← withNaryArg 6 delab
  `(Tm($Γ, $A))

namespace Tm

variable {D : Displayed.{v₂, u₂} C} [Fib D] [Comprehension D] {Δ Γ : C} (σ : Δ ⟶ Γ)
  {A : D.Ty Γ}

/-- `σ ≫ t.sec`, as a morphism of `cod C` over `σ` from the identity of `Δ` to the projection of
`A`: what the substitution of `t` along `σ` factors. -/
def pullCone (t : Tm(Γ, A)) :
    (⟨Δ, 𝟙 Δ⟩ : (cod C).Ob Δ) ⟶[𝟙 Δ ≫ σ] (D.compr).obj A :=
  ⟨σ ≫ t.sec, (congrArg (σ ≫ ·) t.sec_proj : _)⟩

/-- **The substitution of a term** along `σ : Δ ⟶ Γ`: the factorization of `σ ≫ t.sec` through
the pullback square of `𝐪(σ, A)`. -/
def pull (t : Tm(Γ, A)) : Tm(Δ, A⦃σ⦄) where
  sec := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (pullCone σ t)).1
  sec_proj := ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift (𝟙 Δ) (pullCone σ t)).2

/-- Displays `t.pull σ` as `t⦃σ⦄`. -/
@[scoped app_unexpander Tm.pull]
def unexpandPull : Lean.PrettyPrinter.Unexpander
  | `($_ $σ $t) => `($t⦃$σ⦄)
  | _ => throw ()

/-- The substituted term is over `t` along `𝐪(σ, A)`. -/
theorem pull_sec_q (t : Tm(Γ, A)) : t⦃σ⦄.sec ≫ 𝐪(σ, A) = σ ≫ t.sec :=
  congrArg Subtype.val ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_fac (𝟙 Δ)
    (pullCone σ t))

/-- **The substituted term is the unique section over `t` along `𝐪(σ, A)`.** -/
theorem pull_unique (t : Tm(Γ, A)) (s : Tm(Δ, A⦃σ⦄)) (h : s.sec ≫ 𝐪(σ, A) = σ ≫ t.sec) :
    s = t⦃σ⦄ :=
  Tm.ext (congrArg Subtype.val ((D.isCartesianComprMap (D.isCartesianClift σ A)).lift_uniq
    (χ := pullCone σ t)
    (⟨s.sec, s.sec_proj⟩ : CodHom (𝟙 Δ) (⟨Δ, 𝟙 Δ⟩ : CodOb C Δ) ((D.compr).obj (D.pull σ A)))
    (CodHom.ext h)))

end Tm

namespace Tm

variable {D : Displayed.{v₂, u₂} C} [SplitComprehension D] {Γ : C} {A : D.Ty Γ}

/-- Substitution of terms along the identity is the identity. -/
theorem pull_id (t : Tm(Γ, A)) : t⦃𝟙 Γ⦄ = t :=
  (pull_unique (𝟙 Γ) t t rfl).symm

/-- Substitution of terms along a composite is the composite of the substitutions. -/
theorem pull_comp {Δ Θ : C} (τ : Θ ⟶ Δ) (σ : Δ ⟶ Γ) (t : Tm(Γ, A)) :
    t⦃τ ≫ σ⦄ = t⦃σ⦄⦃τ⦄ :=
  (pull_unique (τ ≫ σ) t t⦃σ⦄⦃τ⦄
    (((congrArg (· ≫ 𝐪(σ, A)) (pull_sec_q τ t⦃σ⦄)).trans
      (congrArg (τ ≫ ·) (pull_sec_q σ t)) :))).symm

end Tm

end Displayed

import TwoCategory.Factorization.Comma.Basic
import TwoCategory.Factorization.Comma.AWFS
import TwoCategory.Factorization.Comma.Algebras

/-!
# The comma factorization

In a 2-category `B` with comma objects, every 1-cell factors as `f = Lf ≫ Rf` through `f/B`, the
comma object of `f` and `𝟙 B`. This is an AWFS, whose 2-monad `R` is lax idempotent.

* `Basic`: the factorization, as strict 2-functors `L R : Arr B ⥤ Arr B` (Mathlib's
  `StrictPseudofunctor`). Squares and their 2-cells act on `f/B` by the 1- and 2-dimensional
  universal property of comma objects, and the functor laws of these actions are rules, so the
  laws of `L` and `R` hold by `rfl` (checked by `kernel_rfl`).
* `AWFS`: the comma factorization is an AWFS (`commaAWFS`). `R` is a 2-monad (`rMonad`, with unit
  `(Lf, 𝟙)` and multiplication `(π_f, 𝟙)`, composing the universal 2-cells of `f/B` and `Rf/B`),
  `L` a 2-comonad (`lComonad`, with counit `(𝟙, Rf)` and comultiplication `(𝟙, σ_f)`, induced by a
  2-cell from the 2-dimensional universal property of `f/B`), and the square
  `(σ_f, π_f) : L(Rf) ⟶ R(Lf)` is a distributive law of `L` over `R` (`distributiveLaw`). Their
  2-categories of strict (co)algebras are `RAlg B` and `LCoalg B`. The laws are proved by
  extensionality into comma objects and `kernel_rfl`; a few equations about these 1- and 2-cells
  are proved first and made rules.
* `Algebras`: `R` is lax idempotent (`rLaxIdempotent`), and `R`-algebras are split reflections:
  of the units `(Lf, 𝟙)` in `Arr B` (`rAlgEquiv`), and of `Lf` in the slice over the codomain
  (`ralgEquiv`).
-/

universe w v u

open CategoryTheory TwoCategory

/-! ## Main results -/

/-- The comma factorization is an AWFS. -/
example {B : Type u} [TwoCategory.{w, v} B] [HasCommas B] : AWFS B :=
  commaAWFS B

/-- `R` is a lax idempotent 2-monad on the arrow 2-category. -/
example {B : Type u} [TwoCategory.{w, v} B] [HasCommas B] : (rMonad (B := B)).LaxIdempotent :=
  rLaxIdempotent

/-- `R`-algebras are split reflections of `Lf` over the codomain. -/
example {B : Type u} [TwoCategory.{w, v} B] [HasCommas B] :
    RAlg B ≃ Σ f : Arr B, f.SplitReflection :=
  ralgEquiv

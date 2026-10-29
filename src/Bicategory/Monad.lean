import Mathlib.CategoryTheory.Bicategory.End
import Mathlib.CategoryTheory.Monoidal.Mon

/-!
# Monads in a bicategory

A monad in a bicategory `B` is a 1-morphism `t : a ⟶ a` with a unit `𝟙 a ⟶ t` and a multiplication
`t ≫ t ⟶ t` satisfying the monad laws: a monoid object in the monoidal category `a ⟶ a`
(`Bicategory.Monad`), dually to Mathlib's `Bicategory.Comonad`. For the strict 2-monads on a
2-category, see `TwoMonad`.
-/

universe w v u

namespace CategoryTheory.Bicategory

/-- A monad in a bicategory `B` is a 1-morphism `t : a ⟶ a` together with 2-morphisms
`η : 𝟙 a ⟶ t` and `μ : t ≫ t ⟶ t` satisfying the monad laws: a monoid object in the monoidal
category `a ⟶ a`, dually to Mathlib's `Bicategory.Comonad`. -/
abbrev Monad {B : Type u} [Bicategory.{w, v} B] {a : B} (t : a ⟶ a) :=
  MonObj t

end CategoryTheory.Bicategory

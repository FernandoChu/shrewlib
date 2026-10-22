import Displayed.Fibration.Basic

/-!
# Fibrations

The exact dual of `Opfibration/`, whose `Readme.lean` explains the design.

* `Basic`: cartesian morphisms (`IsCartesian`), and cloven fibrations (`Fib`), with chosen
  `pull f y` and `clift f y : pull f y ⟶[f] y`, the cartesian factorization, the transport
  `pullMap` and its functors, and split versions (`PreSplitFib`, `SplitFib`). Cleavages transfer
  along equivalences over the base.
-/

universe v₁ u₁

open CategoryTheory Displayed

open scoped Displayed

/-! ## Main results -/

/-- A vertical equivalence preserves cartesian morphisms. -/
recall Displayed.VertEquivalence.isCartesianMap {A : Type u₁} [Category.{v₁} A]
    {D E : Displayed A} (e : VertEquivalence D E) {a a' : A} {f : a ⟶ a'} {x : D.Ob a}
    {y : D.Ob a'} {φ : x ⟶[f] y} (H : IsCartesian φ) : IsCartesian (e.functor.map φ)

/-- A cleavage transfers along a vertical equivalence. -/
recall Displayed.VertEquivalence.fib {A : Type u₁} [Category.{v₁} A] {D E : Displayed A}
    (e : VertEquivalence D E) [Fib D] : Fib E

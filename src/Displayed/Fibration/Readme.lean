import Displayed.Fibration.Basic
import Displayed.Fibration.DualFib
import Displayed.Fibration.Sigma
import Displayed.Fibration.SplitFibCat
import Displayed.Fibration.Straightening.Readme

/-!
# Fibrations

The exact dual of `Opfibration/`, whose `Readme.lean` explains the design.

* `Basic`: cartesian morphisms (`IsCartesian`), and cloven fibrations (`Fib`), with chosen
  `pull f y` and `clift f y : pull f y ⟶[f] y`, the cartesian factorization, the transport
  `pullMap` and its functors, and split versions (`PreSplitFib`, `SplitFib`). Cleavages transfer
  along equivalences over the base.
* `DualFib`: the dual fibration of a split fibration.
* `Sigma`: fibrations compose, and so do split fibrations.
* `SplitFibCat`: the split fibrations and displayed functors between them, a category displayed
  over `Cat`.
* `Straightening/`: functors `Aᵒᵖ ⥤ Cat` and their unstraightenings, an equivalence with the split
  fibrations over `Cat` (see its `Readme.lean`).
-/

universe v₁ u₁ v₂ u₂ v₃ u₃

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

/-- Split fibrations compose: for `D` over `A` and `E` over `D.Total`, the composite is a split
fibration over `A`. -/
recall Displayed.sigmaSplitFib {A : Type u₁} [Category.{v₁} A] {D : Displayed.{v₁, u₁, v₂, u₂} A}
    {E : Displayed.{max v₁ v₂, max u₁ u₂, v₃, u₃} D.Total} [SplitFib D] [SplitFib E] :
    SplitFib (D.sigmaDisp E)
